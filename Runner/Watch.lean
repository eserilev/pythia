import Runner.Build
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# The dynamic write condition check (SPEC 9.4)

The runner sets the watches of `Heap.set`, `Locals.set` and `frame`. They keep a stack of
frames. Each frame holds the objects of its arguments and of every value that a local of the
frame got.

- At each in-place write, the check counts the heap paths from the live roots to the written
  object. The live roots are the objects of all frames. A root that another root reaches is
  an alias, as `validator = state.validators[i]`, and is not a start of paths. More than one
  path is a hit. A written object under a container root that no FP pattern names is an FP
  miss. A write to a Python list, dict or set is not checked.
- At the entry of each call of a spec function `g`, each object at a `Footprint g` path from
  the arguments, that is each object that `g` writes, has one path from the arguments.
  Paths count through every root.
- At the exit of the call: Reach. Every object that the arguments or the result reach was
  reachable from the arguments at the entry, or is new. An old object that the call wrote and
  that no `Footprint g` path from the arguments names is a footprint miss.
- At the entry and the exit of the top-level call: `WTree` over FP from its arguments, and
  over FP from its result.
-/

namespace SpecLean.Runner.Watch

open Std

structure Frame where
  fn : Name
  roots : HashSet Nat
  /-- The objects that the arguments reached at the entry, when `g` writes. -/
  before : Option (HashSet Nat) := none
  /-- `Heap.next` at the entry. An object at or above it is new. -/
  next : Nat := 0
  /-- The write counts at the entry. -/
  writesAt : Nat × Nat := (0, 0)
  /-- The objects at `Footprint g` paths from the arguments at the entry. -/
  fpObjs : HashSet Nat := {}
  /-- The old objects that the call wrote. -/
  written : HashSet Nat := {}
  deriving Inhabited

structure State where
  frames : Array Frame := #[]
  /-- Hits by description, with a count. -/
  hits : HashMap String Nat := {}
  /-- Writes to SSZ objects and to Python objects so far. A call check is skipped when
  nothing that it reads changed since the same check. -/
  writes : Nat := 0
  pyWrites : Nat := 0
  checked : HashSet (Nat × Nat × List Nat) := {}
  /-- When each root object first became a root: the arguments of one call share a time, and
  each binding of a local gets a new time. -/
  rootTime : HashMap Nat Nat := {}
  clock : Nat := 0
  deriving Inhabited

initialize state : IO.Ref State ← IO.mkRef {}

/-- The tables of the build that the check reads. -/
structure Ctx where
  names : Array String
  /-- The step to an element: the interned `*`. -/
  star : Name
  fieldNames : HashMap Name (Array Name)
  fnFootprint : HashMap Name (List (Nat × List Name))
  /-- The FP patterns: root type and steps. -/
  patterns : Array (Name × Array Name)
  /-- The pattern states that a container of each type starts: `(i, 0)` for pattern `i`. -/
  starters : HashMap Name (List (Nat × Nat))
  deriving Inhabited

def Ctx.ofBuild (B : Build) : Ctx := Id.run do
  let patterns := (B.footprint.map fun (t, ss) => (t, ss.toArray)).toArray
  let mut starters : HashMap Name (List (Nat × Nat)) := {}
  for i in [0:patterns.size] do
    let t := patterns[i]!.1
    starters := starters.insert t ((i, 0) :: starters.getD t [])
  return { names := B.names, star := B.ids.getD "*" 1000000000,
           fnFootprint := B.fnFootprint.foldl (init := {}) fun m (f, ps) => m.insert f ps,
           fieldNames := B.containers.foldl (init := {}) fun m (ty, fs) =>
             m.insert ty (fs.map (·.1)).toArray,
           patterns, starters }

initialize ctxRef : IO.Ref Ctx ← IO.mkRef default

def Ctx.nameOf (C : Ctx) (n : Name) : String := C.names[n]?.getD s!"#{n}"

partial def refsOf : Value → List Nat
  | .ref a => [a]
  | .tuple xs => xs.flatMap refsOf
  | .enumView v => refsOf v
  | .zipView vs _ => vs.flatMap refsOf
  | .member b _ => refsOf b
  | .frozenDict kvs => kvs.flatMap fun (k, v) => refsOf k ++ refsOf v
  | _ => []

/-- The children of an object, with the step to each: a field name, or `star`. -/
def children (C : Ctx) (h : Heap) (a : Nat) : Array (Name × Nat) := Id.run do
  let mut out := #[]
  match h.objs a with
  | some (.container ty fs) =>
    let names := C.fieldNames.getD ty #[]
    let mut i := 0
    for v in fs do
      for c in refsOf v do out := out.push (names[i]?.getD C.star, c)
      i := i + 1
  | some (.list _ _ _ xs) | some (.set xs) =>
    for v in xs do
      match v with
      | .ref c => out := out.push (C.star, c)
      | .boolean _ | .uint _ _ | .bytes _ _ => pure ()
      | v => for c in refsOf v do out := out.push (C.star, c)
  | some (.dict es) =>
    for (k, v) in es do
      for c in refsOf k ++ refsOf v do out := out.push (C.star, c)
  | _ => pure ()
  return out

def typeOf (h : Heap) (a : Nat) : Option Name :=
  match h.objs a with
  | some (.container ty _) => some ty
  | _ => none

/-- The objects that the roots reach, parents first, with the children of each. -/
partial def topo (C : Ctx) (h : Heap) (roots : List Nat) :
    Array Nat × HashMap Nat (Array (Name × Nat)) := Id.run do
  let mut adj : HashMap Nat (Array (Name × Nat)) := {}
  let mut post : Array Nat := #[]
  let mut stack : List (Nat × Bool) := roots.map (·, false)
  while true do
    match stack with
    | [] => break
    | (a, done) :: rest =>
      stack := rest
      if done then post := post.push a
      else if !adj.contains a then
        let cs := children C h a
        adj := adj.insert a cs
        stack := (a, true) :: stack
        for (_, c) in cs do
          if !adj.contains c then stack := (c, false) :: stack
  return (post.reverse, adj)

structure Analysis where
  cnt : HashMap Nat Nat
  fp : HashSet Nat
  /-- One parent of each object, with the step from it. -/
  parent : HashMap Nat (Nat × Name)

/-- For each object of `order`: the number of heap paths from `starts` (a start may count
more than once), whether an FP pattern names it, and one parent. A pattern state `(i, k)`
means that pattern `i` has matched `k` steps. -/
def analyze (C : Ctx) (h : Heap) (order : Array Nat) (adj : HashMap Nat (Array (Name × Nat)))
    (starts : List Nat) : Analysis := Id.run do
  let mut cnt : HashMap Nat Nat := {}
  for r in starts do cnt := cnt.insert r (cnt.getD r 0 + 1)
  let mut st : HashMap Nat (List (Nat × Nat)) := {}
  let mut parent : HashMap Nat (Nat × Name) := {}
  let mut fp : HashSet Nat := {}
  for a in order do
    let s := match typeOf h a with
      | some ty => C.starters.getD ty [] ++ st.getD a []
      | none => st.getD a []
    if s.any fun (i, k) => k = C.patterns[i]!.2.size then fp := fp.insert a
    let c := cnt.getD a 0
    for (step, b) in adj.getD a #[] do
      cnt := cnt.insert b (cnt.getD b 0 + c)
      if !parent.contains b then parent := parent.insert b (a, step)
      let next := s.filterMap fun (i, k) =>
        if C.patterns[i]!.2[k]? = some step then some (i, k + 1) else none
      if !next.isEmpty then st := st.insert b (next ++ st.getD b [])
  return { cnt, fp, parent }

/-- One path to `a`, as the root type and the steps. -/
partial def pathOf (C : Ctx) (h : Heap) (an : Analysis) (a : Nat) : String :=
  match an.parent[a]? with
  | some (p, step) => pathOf C h an p ++ "." ++ C.nameOf step
  | none => (typeOf h a).map C.nameOf |>.getD "list"

def hit (s : State) (msg : String) : State :=
  { s with hits := s.hits.insert msg (s.hits.getD msg 0 + 1) }

/-- The function of the innermost frame that is not a closure. -/
def currentFn (C : Ctx) (s : State) : String :=
  match s.frames.reverse.find? (·.fn ≠ 0) with
  | some f => C.nameOf f.fn
  | none => "<top>"

/-- A Python list, dict or set. FP names none of them. -/
def isPy (h : Heap) (a : Nat) : Bool :=
  match h.objs a with
  | some (.list .pyList _ _ _) | some (.dict _) | some (.set _) => true
  | _ => false

/-- Give the objects `rs` the next root time, unless they have one. -/
def stamp (s : State) (rs : List Nat) : State :=
  { s with clock := s.clock + 1,
           rootTime := rs.foldl (init := s.rootTime) fun m r =>
             if m.contains r then m else m.insert r s.clock }

/-- The objects that `roots` reach, with the children of each, without a walk into `stop`. -/
partial def reachStop (C : Ctx) (h : Heap) (stop : HashSet Nat) (roots : List Nat) :
    HashSet Nat × HashSet Nat := Id.run do
  let mut seen : HashSet Nat := {}
  let mut inner : HashSet Nat := {}
  let mut stack := roots
  while true do
    match stack with
    | [] => break
    | a :: rest =>
      stack := rest
      if seen.contains a || stop.contains a then continue
      seen := seen.insert a
      for (_, c) in children C h a do
        inner := inner.insert c
        if !seen.contains c && !stop.contains c then stack := c :: stack
  return (seen, inner)

/-- The starts of the path count. A root is an alias, and not a start, when a root of an
earlier or the same time reaches it, as `validator = state.validators[i]` or a callee argument
that a caller root reaches. A root that only a later root reaches stays a start: in
`v = Box(p=a); a.x = 1` the argument `a` and the local `v` both reach the written object. -/
def startsOf (C : Ctx) (h : Heap) (s : State) (roots : List Nat) : List Nat := Id.run do
  let times := (roots.map fun r => s.rootTime.getD r 0).eraseDups.mergeSort (· ≤ ·)
  let mut before : HashSet Nat := {}
  let mut starts := []
  for t in times do
    let g := roots.filter fun r => s.rootTime.getD r 0 = t
    -- A walk from `g` that stops at objects of earlier roots: an object behind one of them is
    -- reachable from an earlier root.
    let (seen, inner) := reachStop C h before g
    for r in g do
      if !before.contains r && !inner.contains r then starts := r :: starts
    before := before.insertMany seen.toList
  return starts

def onWrite (h : Heap) (a : Nat) (_ : HeapObj) : BaseIO Nat := do
  let C ← ctxRef.get
  let s ← state.get
  -- A write to a Python object is not a write to an FP object. A later write to an object
  -- that it holds counts its paths.
  if isPy h a then
    state.set { s with pyWrites := s.pyWrites + 1 }
    return 0
  let s := { s with writes := s.writes + 1,
                    frames := s.frames.map fun fr =>
                      if a < fr.next then { fr with written := fr.written.insert a } else fr }
  let roots : HashSet Nat := s.frames.foldl (init := {}) fun acc f => acc.insertMany f.roots
  let roots := roots.toList
  -- The starts reach the same objects as all roots.
  let (order, adj) := topo C h roots
  let starts := startsOf C h s roots
  let an := analyze C h order adj starts
  let n := an.cnt.getD a 0
  let mut s := s
  if n > 1 then
    s := hit s s!"write {currentFn C s}: {pathOf C h an a} has {n} paths"
  -- FP names SSZ objects only. A path from a local Python list is not an FP path.
  if n ≥ 1 && !an.fp.contains a then
    let p := pathOf C h an a
    if !p.startsWith "list" then s := hit s s!"FP miss {currentFn C s}: {p}"
  state.set s
  pure 0

/-- `WTree` over FP from `vs`: each object at an FP path has one path from `vs`. -/
def wtree (kind : String) (f : Name) (vs : List Value) (h : Heap) : BaseIO Unit := do
  let C ← ctxRef.get
  let starts := vs.flatMap refsOf
  if starts.isEmpty then return
  let (order, adj) := topo C h starts
  let an := analyze C h order adj starts
  let mut s ← state.get
  for a in an.fp.toList do
    let n := an.cnt.getD a 0
    if n > 1 then
      s := hit s s!"WTree {kind} {C.nameOf f}: {pathOf C h an a} has {n} paths"
  state.set s

/-- The objects at the end of `steps` from `a`. -/
def follow (C : Ctx) (h : Heap) (a : Nat) : List Name → List Nat
  | [] => [a]
  | x :: rest => (children C h a).toList.flatMap fun (step, b) =>
    if step = x then follow C h b rest else []

/-- The entry check of `g`: each object that `g` writes has one path from the arguments. -/
def footprintCheck (C : Ctx) (f : Name) (fp : List (Nat × List Name)) (vs : List Value)
    (h : Heap) : BaseIO (List Nat) := do
  let starts := vs.flatMap refsOf
  let written := fp.flatMap fun (j, steps) =>
    ((vs[j]?.map refsOf).getD []).flatMap fun a => follow C h a steps
  if written.isEmpty then return written
  let s ← state.get
  let key := (s.writes, s.pyWrites, f :: starts)
  if s.checked.contains key then return written
  let (order, adj) := topo C h starts
  let an := analyze C h order adj starts
  let mut s := { s with checked := s.checked.insert key }
  for a in written.eraseDups do
    let n := an.cnt.getD a 0
    if n > 1 then
      s := hit s s!"WTree entry {C.nameOf f}: {pathOf C h an a} has {n} paths"
  state.set s
  return written

def onEnter (f : Name) (vs : List Value) (h : Heap) : BaseIO Nat := do
  let C ← ctxRef.get
  let top := (← state.get).frames.isEmpty
  let starts := vs.flatMap refsOf
  let fp := C.fnFootprint.getD f []
  let mut before := none
  let mut fpObjs : HashSet Nat := {}
  if f ≠ 0 then
    if top then wtree "top entry" f vs h
    fpObjs := fpObjs.insertMany (← footprintCheck C f fp vs h)
    if !fp.isEmpty then
      before := some (({} : HashSet Nat).insertMany (topo C h starts).1)
  let roots : HashSet Nat := ({} : HashSet Nat).insertMany starts
  state.modify fun s =>
    let fr : Frame :=
      { fn := f, roots, before, fpObjs, next := h.next, writesAt := (s.writes, s.pyWrites) }
    { stamp s starts with frames := s.frames.push fr }
  pure 0

def onExit (f : Name) (vs : List Value) (r : Res (Value × Heap)) : BaseIO Nat := do
  let C ← ctxRef.get
  let s ← state.get
  let fr := s.frames.back?.getD default
  state.set { s with frames := s.frames.pop }
  if f = 0 then return 0
  let .ok (v, h) := r | return 0
  if s.frames.size = 1 then
    wtree "top exit" f vs h
    wtree "top exit result" f [v] h
  -- An old object that the call wrote is at a `Footprint g` path from the arguments.
  let starts := (vs ++ [v]).flatMap refsOf
  let miss := fr.written.toList.filter (!fr.fpObjs.contains ·)
  if let some a := miss.head? then
    let (order, adj) := topo C h starts
    let an := analyze C h order adj starts
    let p := if an.cnt.contains a then pathOf C h an a else "an object outside the arguments"
    state.modify fun st => hit st s!"footprint miss {C.nameOf f}: writes {p}"
  -- Reach. A call that wrote nothing only allocated, so it holds.
  if (s.writes, s.pyWrites) = fr.writesAt then return 0
  if let some before := fr.before then
    let (order, adj) := topo C h starts
    let bad := order.toList.filter fun a => a < fr.next && !before.contains a
    if let some a := bad.head? then
      let an := analyze C h order adj starts
      state.modify fun st =>
        hit st s!"Reach exit {C.nameOf f}: {pathOf C h an a} was not reachable"
  pure 0

def onBind (v : Value) : BaseIO Nat := do
  let rs := refsOf v
  if rs.isEmpty then return 0
  state.modify fun s =>
    match s.frames.back? with
    | some fr =>
      { stamp s rs with frames := s.frames.pop.push { fr with roots := fr.roots.insertMany rs } }
    | none => s
  pure 0

/-- Turn the check on, with an empty state. -/
def install (B : Build) : IO Unit := do
  if (← ctxRef.get).names.isEmpty then ctxRef.set (Ctx.ofBuild B)
  state.set {}
  writeWatch.set onWrite
  bindWatch.set onBind
  enterWatch.set onEnter
  exitWatch.set onExit

/-- The hits of the last run, sorted. -/
def hits : IO (List (String × Nat)) := do
  let s ← state.get
  pure (s.hits.toList.mergeSort fun a b => a.1 ≤ b.1)

end SpecLean.Runner.Watch
