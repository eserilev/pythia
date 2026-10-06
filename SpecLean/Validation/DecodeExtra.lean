import SpecLean.Rd.Prelude

/-!
# Decoder facts for the tactic

A typed list decoder and a typed container decoder that succeed show the heap object they read.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Rd

theorem decListT_some {α : Type} {k : ListKind} {e : SszTy} {l : Option Nat} {f : Dec α}
    {h : Heap} {v : Value} {ys : List α} (hd : decListT k e l f h v = some ys) :
    ∃ a xs, v = .ref a ∧ h.objs a = some (.list k e l xs) ∧ xs.mapM (f h) = some ys := by
  unfold decListT at hd
  split at hd
  · rename_i a
    split at hd
    · rename_i k' e' l' xs ho
      split at hd
      · rename_i hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact ⟨a, xs, rfl, ho, hd⟩
      · simp at hd
    · simp at hd
  · simp at hd

theorem containerFieldsT_some {ty : Name} {h : Heap} {v : Value} {fs : List Value}
    (hd : containerFieldsT ty h v = some fs) :
    ∃ a, v = .ref a ∧ h.objs a = some (.container ty fs) := by
  unfold containerFieldsT at hd
  split at hd
  · rename_i a
    split at hd
    · rename_i ty' fs' ho
      split at hd
      · rename_i hc; subst hc; cases hd; exact ⟨a, rfl, ho⟩
      · simp at hd
    · simp at hd
  · simp at hd

end SpecLean.Validation
