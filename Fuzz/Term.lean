/-!
# Terms in the serializer's syntax

`tools/serialize.py` writes syntax trees as Lean terms: `(.name 3 5)`, `[a, b]`, `(a, b)`,
`(some x)`, `none`, `{ names := [..], defaults := [..], vararg := none }`. The fuzz runner reads
the same syntax at run time, so it reuses the serializer's encoding without a Lean compile per
program.
-/

namespace SpecLean.Fuzz

/-- A parsed term. An identifier, with or without a leading dot, is an `app` with no
arguments. -/
inductive Term where
  | int (n : Int)
  | str (s : String)
  | app (f : String) (args : List Term)
  | list (xs : List Term)
  | tuple (xs : List Term)
  | record (fs : List (String × Term))
  deriving Inhabited, Repr

abbrev PM := ReaderT (Array Char) (StateT Nat (Except String))

def peek : PM (Option Char) := do return (← read)[← get]?

def bump : PM Unit := modify (· + 1)

partial def skipWs : PM Unit := do
  match ← peek with
  | some c => if c.isWhitespace then bump; skipWs else pure ()
  | none => pure ()

def fail {α : Type} (msg : String) : PM α := do
  throw s!"term parse error at {← get}: {msg}"

def expect (c : Char) : PM Unit := do
  skipWs
  if (← peek) == some c then bump else fail s!"expected '{c}'"

partial def digits (acc : Nat) : PM Nat := do
  match ← peek with
  | some c => if c.isDigit then bump; digits (acc * 10 + (c.toNat - '0'.toNat)) else pure acc
  | none => pure acc

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

partial def ident (acc : String) : PM String := do
  match ← peek with
  | some c => if isIdChar c then bump; ident (acc.push c) else pure acc
  | none => pure acc

partial def strBody (acc : String) : PM String := do
  match ← peek with
  | some '"' => bump; pure acc
  | some '\\' =>
    bump
    match ← peek with
    | some 'n' => bump; strBody (acc.push '\n')
    | some c => bump; strBody (acc.push c)
    | none => fail "unterminated string"
  | some c => bump; strBody (acc.push c)
  | none => fail "unterminated string"

mutual

/-- One atom: a number, a string, an identifier, a list, a record or a parenthesized form. -/
partial def atom : PM Term := do
  skipWs
  match ← peek with
  | some '(' =>
    bump
    let first ← appExpr
    skipWs
    if (← peek) == some ',' then
      let rest ← sepBy ')'
      pure (.tuple (first :: rest))
    else
      expect ')'
      pure first
  | some '[' =>
    bump
    skipWs
    if (← peek) == some ']' then bump; pure (.list []) else
    let first ← appExpr
    skipWs
    if (← peek) == some ',' then pure (.list (first :: (← sepBy ']')))
    else expect ']'; pure (.list [first])
  | some '{' =>
    bump
    let fs ← fields []
    pure (.record fs)
  | some '"' => bump; pure (.str (← strBody ""))
  | some '-' =>
    bump
    pure (.int (-((← digits 0 : Nat) : Int)))
  | some '.' =>
    bump
    pure (.app (← ident "") [])
  | some c =>
    if c.isDigit then pure (.int (← digits 0))
    else if isIdChar c then pure (.app (← ident "") [])
    else fail s!"unexpected '{c}'"
  | none => fail "unexpected end"

/-- The rest of a comma-separated sequence, after the first item, up to `close`. -/
partial def sepBy (close : Char) : PM (List Term) := do
  skipWs
  match ← peek with
  | some ',' =>
    bump
    let t ← appExpr
    pure (t :: (← sepBy close))
  | some c => if c == close then bump; pure [] else fail s!"expected ',' or '{close}'"
  | none => fail "unexpected end"

partial def fields (acc : List (String × Term)) : PM (List (String × Term)) := do
  skipWs
  match ← peek with
  | some '}' => bump; pure acc.reverse
  | some ',' => bump; fields acc
  | _ =>
    let k ← ident ""
    expect ':'
    expect '='
    let v ← appExpr
    fields ((k, v) :: acc)

/-- An atom applied to more atoms: `.name 3 5` or `some x`. -/
partial def appExpr : PM Term := do
  let head ← atom
  let args ← argList []
  match head, args with
  | t, [] => pure t
  | .app f [], as => pure (.app f as)
  | _, _ => fail "application of a non-identifier"

partial def argList (acc : List Term) : PM (List Term) := do
  skipWs
  match ← peek with
  | some c =>
    if c == ',' || c == ')' || c == ']' || c == '}' then pure acc.reverse
    else argList ((← atom) :: acc)
  | none => pure acc.reverse

end

def parseTerm (s : String) : Except String Term :=
  match ((appExpr <* skipWs).run s.toList.toArray).run 0 with
  | .ok (t, i) => if i == s.length then .ok t else .error s!"trailing input at {i}"
  | .error e => .error e

end SpecLean.Fuzz
