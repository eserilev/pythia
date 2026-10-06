import SpecLean.Layer4.Denote

/-!
# Layer 4 spike: evaluation steps of the denotation

Symbolic evaluation lemmas: one denotation step under hypotheses on its parts. A proof that the
denotation of a real function equals its readable Lean rewrites with these, so `simp` never
reduces a `match` on a value rule. Such a reduction unfolds the rule down to a range check on
the literal `2 ^ 64`, which the kernel then evaluates in unary.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

@[simp] theorem lift_ok (a : α) : lift (.ok a : Res α) = some (.ok a) := rfl

@[simp] theorem lift_err (e : SpecError) (h : e ≠ .outOfFuel) :
    lift (.error e : Res α) = some (.error e) := by
  cases e <;> first | rfl | exact absurd rfl h

/-- `obj[i] op= e` that writes. -/
theorem dAugIndex_eval {env : Env} {fp : Footprint} {s : DSt} {o ie e : Expr} {op : BinOp}
    {k : Nat} {p : List Nat} {kd : ListKind} {el : SszTy} {ll : Option Nat} {ds : List DV}
    {iv cur rv v v' : Value} {j : Int} {m : Nat}
    (h1 : dExpr env s o = some (.ok (.place k p))) (h2 : dExpr env s ie = some (.ok (.val iv)))
    (h3 : s.deref k p = some (.list kd el ll ds)) (hb : isByteList kd el = false)
    (h4 : toIndex iv = .ok j) (h5 : normIndex ds.length j = some m) (h6 : ds[m]? = some (.leaf cur))
    (h7 : dExpr env s e = some (.ok (.val rv))) (h8 : binopVal op cur rv = .ok v)
    (h9 : Flat v = true) (h10 : dCoerce env false el v = some (.ok v')) :
    dAugIndex env fp s o ie op e = dWrite fp s k p m v' := by
  simp [dAugIndex, h1, h2, h3, hb, h4, h5, h6, h7, h8, h9, h10, DM.bind, lift]

/-- `obj[i] op= e` whose operator raises. -/
theorem dAugIndex_err {env : Env} {fp : Footprint} {s : DSt} {o ie e : Expr} {op : BinOp}
    {k : Nat} {p : List Nat} {kd : ListKind} {el : SszTy} {ll : Option Nat} {ds : List DV}
    {iv cur rv : Value} {j : Int} {m : Nat} {err : SpecError}
    (h1 : dExpr env s o = some (.ok (.place k p))) (h2 : dExpr env s ie = some (.ok (.val iv)))
    (h3 : s.deref k p = some (.list kd el ll ds)) (hb : isByteList kd el = false)
    (h4 : toIndex iv = .ok j) (h5 : normIndex ds.length j = some m) (h6 : ds[m]? = some (.leaf cur))
    (h7 : dExpr env s e = some (.ok (.val rv))) (h8 : binopVal op cur rv = .error err)
    (h9 : err ≠ .outOfFuel) :
    dAugIndex env fp s o ie op e = some (.error err) := by
  simp [dAugIndex, h1, h2, h3, hb, h4, h5, h6, h7, h8, DM.bind, lift_err err h9]

/-- `obj[i] op= e` with an index out of range. -/
theorem dAugIndex_oob {env : Env} {fp : Footprint} {s : DSt} {o ie e : Expr} {op : BinOp}
    {k : Nat} {p : List Nat} {kd : ListKind} {el : SszTy} {ll : Option Nat} {ds : List DV}
    {iv : Value} {j : Int}
    (h1 : dExpr env s o = some (.ok (.place k p))) (h2 : dExpr env s ie = some (.ok (.val iv)))
    (h3 : s.deref k p = some (.list kd el ll ds)) (hb : isByteList kd el = false)
    (h4 : toIndex iv = .ok j) (h5 : normIndex ds.length j = none) :
    dAugIndex env fp s o ie op e = some (.error .indexError) := by
  simp [dAugIndex, h1, h2, h3, hb, h4, h5, DM.bind, lift]

end SpecLean.Layer4
