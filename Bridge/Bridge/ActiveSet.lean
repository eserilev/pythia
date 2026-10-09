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

/-! ## The hand steps of `process_registry_updates` keep the active set -/

theorem bind_eq_ok {ε α β : Type} {A : Except ε α} {f : α → Except ε β} {b : β}
    (h : (A >>= f) = .ok b) : ∃ a, A = .ok a ∧ f a = .ok b := by
  cases A with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem uint64Add_ok {a b c : Nat} (h : uint64Add a b = .ok c) : c = a + b := by
  unfold uint64Add at h
  split at h
  · cases h; rfl
  · cases h

theorem compute_activation_exit_epoch_gt (p : Preset) (e c : Nat)
    (h : compute_activation_exit_epoch p e = .ok c) : e < c := by
  unfold compute_activation_exit_epoch at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  have := uint64Add_ok ha
  have := uint64Add_ok h
  omega

/-- `compute_exit_epoch_and_update_churn` gives an exit epoch after the current epoch, and keeps
the slot and the validators. -/
theorem compute_exit_epoch_gt (p : Preset) (tab : Nat) (s s₁ : BeaconState) (bal e cur : Nat)
    (hcur : get_current_epoch p s = .ok cur)
    (h : compute_exit_epoch_and_update_churn p tab s bal = .ok (e, s₁)) :
    cur < e ∧ s₁.slot = s.slot ∧ s₁.validators = s.validators := by
  unfold compute_exit_epoch_and_update_churn at h
  rw [hcur] at h
  obtain ⟨cur', hc', h⟩ := bind_eq_ok h
  cases hc'
  obtain ⟨cae, hcae, h⟩ := bind_eq_ok h
  have hgt := compute_activation_exit_epoch_gt p cur cae hcae
  obtain ⟨churn, _, h⟩ := bind_eq_ok h
  dsimp only at h
  split at h <;> split at h
  all_goals
    repeat (obtain ⟨_, hb, h⟩ := bind_eq_ok h; try have := uint64Add_ok hb)
    cases h
    refine ⟨?_, rfl, rfl⟩
    try dsimp only
    omega

/-- The facts of a validator list change for `total_active_balance_congr`. -/
def KeepsActive (s t : List Validator) (e : Nat) : Prop :=
  t.length = s.length ∧ ∀ i (hs : i < s.length) (ht : i < t.length),
    t[i].effective_balance = s[i].effective_balance ∧
      is_active_validator t[i] e = is_active_validator s[i] e

theorem keepsActive_refl (s : List Validator) (e : Nat) : KeepsActive s s e :=
  ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem keepsActive_trans {s t u : List Validator} {e : Nat} (h1 : KeepsActive s t e)
    (h2 : KeepsActive t u e) : KeepsActive s u e := by
  refine ⟨h2.1.trans h1.1, fun i hs hu => ?_⟩
  have ht : i < t.length := by rw [h1.1]; exact hs
  obtain ⟨a1, b1⟩ := h1.2 i hs ht
  obtain ⟨a2, b2⟩ := h2.2 i ht hu
  exact ⟨a2.trans a1, b2.trans b1⟩

/-- Setting one validator to a value with the same effective balance and activity. -/
theorem keepsActive_set (s : List Validator) (k : Nat) (v : Validator) (e : Nat) (hk : k < s.length)
    (heb : v.effective_balance = s[k].effective_balance)
    (hact : is_active_validator v e = is_active_validator s[k] e) :
    KeepsActive s (s.set k v) e := by
  refine ⟨by simp, fun i hs ht => ?_⟩
  by_cases hik : i = k
  · subst hik; simp [heb, hact]
  · simp [List.getElem_set, Ne.symm hik]

/-- The hand `initiate_validator_exit` keeps the slot, and the effective balance and the activity
at the current epoch of each validator. -/
theorem initiate_validator_exit_keeps (p : Preset) (tab : Nat) (s s' : BeaconState) (k cur : Nat)
    (hcur : get_current_epoch p s = .ok cur) (hcf : cur < FAR_FUTURE_EPOCH)
    (h : initiate_validator_exit p tab s k = .ok s') :
    s'.slot = s.slot ∧ KeepsActive s.validators s'.validators cur := by
  unfold initiate_validator_exit at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok h
  have hk : k < s.validators.length := by
    unfold listGet at hv
    split at hv
    · rename_i a ha; exact (List.getElem?_eq_some_iff.mp ha).1
    · cases hv
  have hvk : v = s.validators[k] := by
    unfold listGet at hv
    rw [List.getElem?_eq_getElem hk] at hv
    cases hv; rfl
  subst hvk
  split at h
  · cases h; exact ⟨rfl, keepsActive_refl _ _⟩
  · rename_i hfar
    obtain ⟨_, _, h⟩ := bind_eq_ok h
    obtain ⟨w, hce, h⟩ := bind_eq_ok h
    obtain ⟨hgt, hslot, hvals⟩ := compute_exit_epoch_gt p tab s w.2 _ w.1 cur hcur hce
    obtain ⟨wd, _, h⟩ := bind_eq_ok h
    obtain ⟨vs, hvs, h⟩ := bind_eq_ok h
    cases h
    unfold listSet at hvs
    rw [hvals] at hvs
    split at hvs
    · cases hvs
      refine ⟨hslot, ?_⟩
      refine keepsActive_set _ _ _ _ hk rfl ?_
      have hex : s.validators[k].exit_epoch = FAR_FUTURE_EPOCH := by simpa using hfar
      unfold is_active_validator
      simp only [hex]
      have h1 : decide (cur < w.1) = true := by simp; omega
      have h2 : decide (cur < FAR_FUTURE_EPOCH) = true := by simp; omega
      rw [h1, h2]
    · rename_i hlt; exact absurd hk hlt

end Pythia.Bridge
