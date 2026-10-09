import EpochProofs.Spec.Block.Block

/-!
# The total active balance of a changed state

A loop step that keeps the slot, the number of validators, and for each validator its effective
balance and whether it is active at the current epoch, keeps the total active balance. For
example, a step that moves an exit epoch from `FAR_FUTURE_EPOCH` to an epoch after the current
epoch keeps the validator active at the current epoch. The hand spec computes the total active
balance once before such a loop (`process_registry_updates`), and the readable spec computes it
again in each step. This lemma relates the two.
-/

namespace Pythia.Bridge

open EpochProofs.Spec

theorem active_indices_congr (s t : List Validator) (e : Nat) (n : Nat)
    (hlen : t.length = s.length)
    (h : ∀ i (hs : i < s.length) (ht : i < t.length),
      is_active_validator t[i] e = is_active_validator s[i] e) :
    ((t.zipIdx n).filter fun p => is_active_validator p.1 e).map (·.2) =
      ((s.zipIdx n).filter fun p => is_active_validator p.1 e).map (·.2) := by
  induction s generalizing t n with
  | nil => cases t with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a s ih =>
    cases t with
    | nil => simp at hlen
    | cons b t =>
      have h0 := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      have ih' := ih t (n + 1) (by simpa using hlen) (fun i hs ht => by
        have := h (i + 1) (by simpa using hs) (by simpa using ht)
        simpa only [List.getElem_cons_succ] using this)
      simp only [List.zipIdx_cons, List.filter_cons, h0]
      split <;> simp [ih']

theorem mapM_congr_mem {α β ε : Type} (l : List α) (f g : α → Except ε β)
    (h : ∀ x ∈ l, f x = g x) : l.mapM f = l.mapM g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.mapM_cons, List.mapM_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem lt_of_mem_active (s : List Validator) (e i : Nat)
    (h : i ∈ ((s.zipIdx.filter fun p => is_active_validator p.1 e).map (·.2))) : i < s.length := by
  obtain ⟨⟨v, j⟩, hm, rfl⟩ := List.mem_map.mp h
  have := (List.mem_zipIdx (List.mem_filter.mp hm).1).2.1
  simpa using this

/-- The total active balance of `t` and `s` is the same when the slot, the number of validators
and, for each validator, the effective balance and the activity at the current epoch are the
same. -/
theorem total_active_balance_congr (p : Preset) (s t : BeaconState) (hslot : t.slot = s.slot)
    (hlen : t.validators.length = s.validators.length)
    (hv : ∀ e, get_current_epoch p s = .ok e → ∀ i (hs : i < s.validators.length)
      (ht : i < t.validators.length),
      t.validators[i].effective_balance = s.validators[i].effective_balance ∧
        is_active_validator t.validators[i] e = is_active_validator s.validators[i] e) :
    get_total_active_balance p t = get_total_active_balance p s := by
  unfold get_total_active_balance
  have he : get_current_epoch p t = get_current_epoch p s := by
    unfold get_current_epoch; rw [hslot]
  rw [he]
  cases hc : get_current_epoch p s with
  | error err => rfl
  | ok e =>
    show get_total_balance p t (get_active_validator_indices t e) =
      get_total_balance p s (get_active_validator_indices s e)
    have hidx : get_active_validator_indices t e = get_active_validator_indices s e := by
      unfold get_active_validator_indices
      exact active_indices_congr s.validators t.validators e 0 hlen
        (fun i hs ht => (hv e hc i hs ht).2)
    rw [hidx]
    unfold get_total_balance
    have hmap : ((get_active_validator_indices s e).mapM fun index => do
        pure (← listGet t.validators index).effective_balance) =
        ((get_active_validator_indices s e).mapM fun index => do
        pure (← listGet s.validators index).effective_balance) := by
      apply mapM_congr_mem
      intro i hi
      have his : i < s.validators.length := lt_of_mem_active s.validators e i hi
      have hit : i < t.validators.length := by rw [hlen]; exact his
      unfold listGet
      rw [List.getElem?_eq_getElem his, List.getElem?_eq_getElem hit]
      have heb := (hv e hc i his hit).1
      simp [heb]
    rw [hmap]

end Pythia.Bridge
