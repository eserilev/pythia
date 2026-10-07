import SpecLean.Ssz
import SpecLean.Lemmas
import SpecLean.Paths
import SpecLean.Compose
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
attribute [rd_simp] Rd.uCast Rd.uOp Rd.uOf Rd.iOp Rd.bd Rd.assert Rd.assertBug Rd.pyMin Rd.pyMax
  Rd.PyOrd.lt

-- `min` and `max` of the interpreter.
attribute [rd_simp] pickBest isVal

end SpecLean.Validation.Steps

namespace SpecLean.Validation.Steps

open SpecLean SpecLean.Encode

@[rd_simp] theorem frame_self (h : Heap) (vs : List Value) (fp : Footprint) : Frame h h vs fp :=
  Frame_refl h vs fp
@[rd_simp] theorem fresh_self (h : Heap) : Fresh h h := Fresh_refl h
@[rd_simp] theorem nnp_self (h : Heap) (vs : List Value) (fp : Footprint) :
    NoNewPaths h h vs fp :=
  NoNewPaths_refl h vs fp

/-! `Int.toNat` of a value that is never negative: `max x 0 = x`. Each `max` left in a fact is a
case split for `omega`, and many of them make `omega` run out of memory. -/
@[rd_simp] theorem max_natCast (a : Nat) : max (a : Int) 0 = a := Int.max_eq_left (Int.natCast_nonneg a)
@[rd_simp] theorem max_natCast_add_lit (a n : Nat) :
    max ((a : Int) + (no_index (OfNat.ofNat n) : Int)) 0 = (a : Int) + (OfNat.ofNat n : Int) :=
  Int.max_eq_left (by have : (0 : Int) ≤ (OfNat.ofNat n : Int) := Int.natCast_nonneg n; omega)
@[rd_simp] theorem max_natCast_add (a b : Nat) : max ((a : Int) + (b : Int)) 0 = (a : Int) + b :=
  Int.max_eq_left (by omega)
@[rd_simp] theorem max_natCast_emod_lit (a n : Nat) :
    max ((a : Int) % (no_index (OfNat.ofNat n) : Int)) 0 = (a : Int) % (OfNat.ofNat n : Int) :=
  Int.max_eq_left (by
    show (0 : Int) ≤ (a : Int) % (n : Int)
    rw [← Int.natCast_emod]; exact Int.natCast_nonneg _)
@[rd_simp] theorem max_natCast_sub_emod_lit (a n : Nat) :
    max ((a : Int) - (a : Int) % (no_index (OfNat.ofNat n) : Int)) 0 =
      (a : Int) - (a : Int) % (OfNat.ofNat n : Int) :=
  Int.max_eq_left (by
    show (0 : Int) ≤ (a : Int) - (a : Int) % (n : Int)
    rw [← Int.natCast_emod]; have := Nat.mod_le a n; omega)

theorem toNat_natCast_emod_lit (a n : Nat) :
    ((a : Int) % (no_index (OfNat.ofNat n) : Int)).toNat = a % (OfNat.ofNat n : Nat) := by
  show ((a : Int) % (n : Int)).toNat = a % n
  rw [← Int.natCast_emod]; exact Int.toNat_natCast _
theorem toNat_natCast_sub_emod_lit (a n : Nat) :
    ((a : Int) - (a : Int) % (no_index (OfNat.ofNat n) : Int)).toNat =
      a - a % (OfNat.ofNat n : Nat) := by
  show ((a : Int) - (a : Int) % (n : Int)).toNat = a - a % n
  rw [← Int.natCast_emod]; have := Nat.mod_le a n; omega

/-! Integer arithmetic that cannot fail: the proofs compute it, they do not split on it. -/
@[rd_simp] theorem intArith_add (a b : Int) : intArith .add a b = .ok (a + b) := rfl
@[rd_simp] theorem intArith_sub (a b : Int) : intArith .sub a b = .ok (a - b) := rfl
@[rd_simp] theorem intArith_mul (a b : Int) : intArith .mul a b = .ok (a * b) := rfl
@[rd_simp] theorem intArith_mod (a b : Int) (hb : b ≠ 0) : intArith .mod a b = .ok (a.fmod b) := by
  simp [intArith, hb]
@[rd_simp] theorem intArith_floorDiv (a b : Int) (hb : b ≠ 0) :
    intArith .floorDiv a b = .ok (a.fdiv b) := by
  simp [intArith, hb]

theorem intArith_ne_oof {op : BinOp} {a b : Int} {e : SpecError}
    (h : intArith op a b = .error e) : e ≠ .outOfFuel := by
  cases op <;> simp only [intArith] at h <;> (repeat' split at h) <;> cases h <;> decide

end SpecLean.Validation.Steps

/-- The error of a step is not out of fuel. -/
macro "rd_oof" : tactic => `(tactic| first
  | with_reducible exact SpecLean.Validation.Steps.intArith_ne_oof ‹_›
  | decide)

/-- Close a leaf goal of the split tree. -/
macro "rd_finish" : tactic => `(tactic| first
  | done
  | omega
  | (exfalso; omega)
  | assumption
  -- Reducible only: at default transparency `contradiction` can unfold a large heap term
  -- past the recursion limit, and that error escapes `first`.
  | with_reducible contradiction
  | rd_oof
  | (simp [rd_simp] at * <;> first
      | done | omega | rd_oof | (exfalso; omega)))

namespace SpecLean.Validation.Steps

open SpecLean

attribute [rd_simp] cmpInt assignTarget assignTargets assignAll sliceBound coerceH_plain depthBound
  Ssz.coerceH ctorFields Ssz.construct.build kwArg Ssz.checkLength

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

attribute [rd_simp] Rd.lget Rd.lset Rd.lappend Ssz.defaultOf Ssz.defaultList Rd.bytesOf

/-- An item that a fact gives as an option, read by its bound index. -/
@[rd_simp] theorem getElem_of_getElem?_some {α : Type} {xs : List α} {i : Nat} {y : α}
    (h : xs[i]? = some y) (p : i < xs.length) : xs[i] = y := by
  rw [List.getElem?_eq_getElem p] at h; exact Option.some.inj h

/-- A list index from a `Nat` below the length. -/
@[rd_simp] theorem normIndex_of_lt {n i : Nat} (h : i < n) : normIndex n (i : Int) = some i := by
  rw [normIndex_nat, if_pos h]

-- Python's `%` and `//` by a positive number: `omega` reads `%` and `/`.
attribute [rd_simp] Int.fmod_eq_emod_of_nonneg Int.fdiv_eq_ediv_of_nonneg

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

namespace SpecLean.Validation.Steps

open SpecLean

/-- The result of a function that returns a new Python list: a reference to a fresh object that
holds `xs`. -/
def ListRes (h h' : Heap) (v : Value) (xs : List Value) : Prop :=
  ∃ a, v = .ref a ∧ h.next ≤ a ∧ h'.objs a = some (.list .pyList .any none xs)

@[rd_simp] theorem listRes_ref (h h' : Heap) (a : Nat) (xs : List Value) :
    ListRes h h' (.ref a) xs ↔ h.next ≤ a ∧ h'.objs a = some (.list .pyList .any none xs) := by
  simp [ListRes]

end SpecLean.Validation.Steps
