import SpecLean.Ssz
import SpecLean.Lemmas
import SpecLean.Paths
import SpecLean.Rd.Prelude
import SpecLean.Validation.Attr

/-!
# Step lemmas of the library, by value shape

The generated proofs do not unfold a library function. A lemma here fires only when the
arguments have a known shape, so terms stay small.
-/

namespace SpecLean.Validation.Steps

open SpecLean

variable {env : Env} {h : Heap}

@[rd_simp] theorem construct_uint_int (u : UintTy) (n : Int) :
    LibModel.construct env h (.uint u) [.int n] [] = (do pure (← wrapUint u n, h)) := rfl

@[rd_simp] theorem construct_uint_uint (u t : UintTy) (n : Nat) :
    LibModel.construct env h (.uint u) [.uint t n] [] = (do pure (← wrapUint u n, h)) := rfl

@[rd_simp] theorem construct_uint_boolean (u : UintTy) (b : Bool) :
    LibModel.construct env h (.uint u) [.boolean b] [] =
      .ok (.uint u (if b then 1 else 0), h) := rfl

attribute [rd_simp] wrapUint UintTy.bits Locals.empty_apply Locals.set_apply seqBinop_uu
  seqBinop_ui seqBinop_iu seqBinop_ii Ssz.binopVal_uint Ssz.binopVal_uint_int Ssz.cmpVal_uint
  resolveUint SpecError.fail Rd.decUintC Rd.uv Rd.erase Rd.UintC.ofNat Rd.UintC.val Rd.UintC.bits
  Rd.BytesC.len Rd.BytesC.data Rd.BytesC.ofBytes

/-! The core interpreter steps on a known syntax tree. -/
attribute [rd_simp] callFn execBlock execStmt evalExpr evalList evalArgs evalOpt evalCmp evalBoolOp
  lookupName bindArgs bindArgs.go callValue anyAll frame_eq callName interp

/-! The readable helpers. -/
attribute [rd_simp] Rd.uCast Rd.uOp Rd.uOf Rd.iOp Rd.bd Rd.assert Rd.assertBug

end SpecLean.Validation.Steps

namespace SpecLean.Validation.Steps

open SpecLean SpecLean.Encode

@[rd_simp] theorem frame_self (h : Heap) (vs : List Value) (fp : Footprint) : Frame h h vs fp :=
  Frame_refl h vs fp
@[rd_simp] theorem fresh_self (h : Heap) : Fresh h h := Fresh_refl h
@[rd_simp] theorem reach_self (h : Heap) (vs : List Value) : Reach h h vs := Reach_refl h vs

theorem intArith_ne_oof {op : BinOp} {a b : Int} {e : SpecError}
    (h : intArith op a b = .error e) : e ≠ .outOfFuel := by
  cases op <;> simp only [intArith] at h <;> (repeat' split at h) <;> cases h <;> decide

end SpecLean.Validation.Steps

/-- The error of a step is not out of fuel. -/
macro "rd_oof" : tactic => `(tactic| first
  | exact SpecLean.Validation.Steps.intArith_ne_oof ‹_›
  | decide)

/-- Close a leaf goal of the split tree. -/
macro "rd_finish" : tactic => `(tactic| first
  | done
  | omega
  | (exfalso; omega)
  | assumption
  | contradiction
  | rd_oof
  | (simp [rd_simp] at * <;> first
      | done | omega | rd_oof | (exfalso; omega)))

namespace SpecLean.Validation.Steps

open SpecLean

attribute [rd_simp] cmpInt assignTarget assignTargets assignAll sliceBound coerceH_plain depthBound

/-- A range check on a cast compares in `Nat`. `whnf` of the `Int` form runs in unary. -/
@[rd_simp] theorem natCast_lt_lit (a n : Nat) :
    ((a : Int) < (no_index (OfNat.ofNat n) : Int)) = (a < (OfNat.ofNat n : Nat)) := by
  simp only [eq_iff_iff]; exact Int.ofNat_lt

@[rd_simp] theorem fromLE_eq (b : List UInt8) :
    Rd.fromLE b = ((b.foldr (fun x acc => x.toNat + 256 * acc) 0 : Nat) : Int) := by
  simp only [Rd.fromLE]; congr 1
  induction b with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, ih]; omega

@[rd_simp] theorem pyIndex_eq : Rd.pyIndex = normIndex := rfl

attribute [rd_simp] Rd.lget Rd.lset Rd.lappend

@[rd_simp] theorem sliceBound'_eq : Rd.sliceBound' = sliceBound := rfl

@[rd_simp] theorem lslice_eq {α : Type} (xs : List α) (lo hi : Option Int) :
    Rd.lslice xs lo hi = xs.extract ((lo.map (sliceBound xs.length)).getD 0)
      ((hi.map (sliceBound xs.length)).getD xs.length) := by
  rw [← sliceBound'_eq]; simp [Rd.lslice, List.extract]

/-- A value that `==` compares without the heap. -/
def scalarV : Value → Bool
  | .ref _ | .tuple _ => false
  | _ => true

attribute [rd_simp] scalarV

@[rd_simp] theorem deepEq_scalar (d : Nat) (h : Heap) (a b : Value) (ha : scalarV a = true)
    (hb : scalarV b = true) : deepEq (d + 1) h a b = cmpVal .eq a b := by
  cases a <;> cases b <;> simp_all [scalarV, deepEq]

end SpecLean.Validation.Steps
