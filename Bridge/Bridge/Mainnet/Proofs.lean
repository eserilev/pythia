import Bridge.GenMainnet.Specs

/-!
# Hand-written bridge proofs (mainnet)

Proofs of `spec_f` that `bridge_main` cannot find: the functions with a loop, and a few steps
without a generic lemma. Each theorem is `hand_f : spec_f`. `tools/gen_bridge.py` reads the names
and uses them in `Eqs.lean`.
-/

namespace Pythia.Bridge.Mainnet

open Pythia.Bridge SpecLean SpecLean.Rd

attribute [local instance] GenMainnet.Cfg.default
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable [Spec]

/-- `y + n / y ≤ n + 1` for `1 ≤ y ≤ n`: the sum in the square-root loop does not overflow. -/
theorem add_div_le (n y : Nat) (h1 : 1 ≤ y) (h2 : y ≤ n) : y + n / y ≤ n + 1 := by
  have hq := Nat.div_mul_le_self n y
  generalize n / y = q at hq ⊢
  cases q with
  | zero => omega
  | succ q =>
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    simp only [Nat.succ_mul, Nat.mul_succ] at hq
    omega

theorem isqrt_loop_ok (n : GenMainnet.Uint64) (hn : n.val + 1 < 2 ^ 64) (x y : GenMainnet.Uint64)
    (hx : x.val ≤ n.val) (hy : y.val < 2 ^ 64) (hy1 : 1 ≤ n.val → 1 ≤ y.val) :
    ∃ b, GenMainnet.integer_squareroot.loop1 n x y =
      .ok (⟨EpochProofs.Spec.integer_squareroot.loop n.val x.val y.val⟩, b) := by
  rw [GenMainnet.integer_squareroot.loop1, EpochProofs.Spec.integer_squareroot.loop]
  by_cases hyx : y.val < x.val
  · have h1 : 1 ≤ y.val := hy1 (by omega)
    have hd : (uOp .floorDiv (uv n) (uv y) : SpecM GenMainnet.Uint64) = .ok ⟨n.val / y.val⟩ :=
      uOp_div_ok (α := GenMainnet.Uint64) rfl n.val y.val (by omega) (by omega)
    have hs : y.val + n.val / y.val ≤ n.val + 1 := add_div_le n.val y.val h1 (by omega)
    have ha : (uOp .add (uv y) (uv (⟨n.val / y.val⟩ : GenMainnet.Uint64)) : SpecM GenMainnet.Uint64) =
        .ok ⟨y.val + n.val / y.val⟩ := by
      rw [show uv y = ((y.val : Nat) : Int) from rfl, show uv (⟨n.val / y.val⟩ : GenMainnet.Uint64) = ((n.val / y.val : Nat) : Int) from rfl,
        uOp_add_nat (α := GenMainnet.Uint64) rfl, if_pos (by omega)]; rfl
    have h2 : (uOp .floorDiv (uv (⟨y.val + n.val / y.val⟩ : GenMainnet.Uint64)) 2 : SpecM GenMainnet.Uint64) =
        .ok ⟨(y.val + n.val / y.val) / 2⟩ :=
      uOp_div_ok (α := GenMainnet.Uint64) rfl _ 2 (by omega) (by show y.val + n.val / y.val < 2 ^ 64; omega)
    obtain ⟨b, hb⟩ := isqrt_loop_ok n hn y ⟨(y.val + n.val / y.val) / 2⟩ (by omega) (by simp; omega)
      (fun hn1 => by
        show 1 ≤ (y.val + n.val / y.val) / 2
        rcases Nat.lt_or_ge 1 y.val with h | h
        · generalize n.val / y.val = q; omega
        · have : y.val = 1 := by omega
          rw [this, Nat.div_one]; omega)
    refine ⟨b, ?_⟩
    rw [if_neg (by simp [uv]; omega), if_pos hyx]
    simp only [pure_bind]
    rw [hd, ok_bind, ha, ok_bind, h2, ok_bind, dif_pos (by show y.val < x.val; exact hyx)]
    exact hb
  · refine ⟨y, ?_⟩
    rw [if_pos (by simp [uv]; omega), if_neg hyx]
    rfl
termination_by x.val
decreasing_by all_goals (simp_wf; omega)

theorem isqrt_loop_le (n x y : Nat) : EpochProofs.Spec.integer_squareroot.loop n x y ≤ x := by
  rw [EpochProofs.Spec.integer_squareroot.loop]
  split
  · have := isqrt_loop_le n y ((y + n / y) / 2); omega
  · exact Nat.le_refl _
termination_by x

theorem hand_integer_squareroot : spec_integer_squareroot := by
  intro n hn
  unfold GenMainnet.integer_squareroot EpochProofs.Spec.integer_squareroot
  by_cases hm : n.val = 18446744073709551615
  · have e : (uv n == uv GenMainnet.UINT64_MAX) = true := by simp [uv, hm, GenMainnet.UINT64_MAX]
    rw [if_pos e]
    have e2 : (n.val == EpochProofs.Spec.UINT64_MAX) = true := by
      simp [hm, EpochProofs.Spec.UINT64_MAX]
    rw [if_pos e2]
    exact ⟨rfl, fun x hx => by cases hx; decide⟩
  · have e : ¬ (uv n == uv GenMainnet.UINT64_MAX) = true := by simp [uv, GenMainnet.UINT64_MAX]; omega
    rw [if_neg e]
    have e2 : ¬ (n.val == EpochProofs.Spec.UINT64_MAX) = true := by
      simp [hm, EpochProofs.Spec.UINT64_MAX]
    rw [if_neg e2]
    have hn' : n.val + 1 < 2 ^ 64 := by omega
    have ha : (uOp .add (uv n) 1 : SpecM GenMainnet.Uint64) = .ok ⟨n.val + 1⟩ := by
      rw [show uv n = ((n.val : Nat) : Int) from rfl, show (1 : Int) = ((1 : Nat) : Int) from rfl,
        uOp_add_nat (α := GenMainnet.Uint64) rfl, if_pos hn']; rfl
    have hd : (uOp .floorDiv (uv (⟨n.val + 1⟩ : GenMainnet.Uint64)) 2 : SpecM GenMainnet.Uint64) =
        .ok ⟨(n.val + 1) / 2⟩ :=
      uOp_div_ok (α := GenMainnet.Uint64) rfl _ 2 (by omega) hn'
    obtain ⟨b, hb⟩ := isqrt_loop_ok n hn' n ⟨(n.val + 1) / 2⟩ (Nat.le_refl _) (by show (n.val + 1) / 2 < 2 ^ 64; omega)
      (fun h1 => by show 1 ≤ (n.val + 1) / 2; omega)
    simp only [pure_bind]
    rw [ha, ok_bind, hd, ok_bind, hb, ok_bind]
    refine ⟨rfl, fun x hx => ?_⟩
    cases hx
    have := isqrt_loop_le n.val n.val ((n.val + 1) / 2)
    show EpochProofs.Spec.integer_squareroot.loop n.val n.val ((n.val + 1) / 2) < 2 ^ 64
    omega

/-- The readable count of set bits: a sum of ones over the set bits. -/
theorem foldl_count (bits : List Boolean) (a : Int) :
    (bits.filterMap fun bit => if bit.val = true then some (1 : Int) else none).foldl (· + ·) a =
      a + (((bits.map Boolean.val).filter id).length : Int) := by
  induction bits generalizing a with
  | nil => simp
  | cons b bits ih =>
    cases hb : b.val <;> simp [hb, ih] <;> omega

theorem hand_get_set_bit_count : spec_get_set_bit_count := by
  intro bits hr
  unfold GenMainnet.get_set_bit_count EpochProofs.Spec.get_set_bit_count
  have hl : ((bits.map Boolean.val).filter id).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (List.length_filter_le _ _) (by simpa using hr.1)
  have e := foldl_count bits 0
  simp only [Int.zero_add] at e
  simp only [bind_pure]
  rw [e, uOf_ok _ rfl hl]
  exact ⟨rfl, fun x hx => by cases hx; exact hl⟩
/-- The readable withdrawn amounts: a `filterMap` against the hand `filter` then `map`. -/
theorem withdrawn_eq (ws : List GenMainnet.Withdrawal) (v : Nat) :
    (ws.filterMap fun w => if (uv w.validator_index == (v : Int)) = true then some w.amount else none).map
        UintC.val =
      ((ws.map abs_Withdrawal).filter fun w => w.validator_index == v).map (·.amount) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.filterMap_cons, List.map_cons, List.filter_cons]
    by_cases hc : w.validator_index.val = v
    · have e : (uv w.validator_index == (v : Int)) = true := by simp [uv, hc]
      rw [if_pos e, if_pos (by simp [abs_Withdrawal, hc])]
      simp only [List.map_cons]
      rw [ih]; rfl
    · rw [if_neg (by simp [uv]; omega), if_neg (by simp [abs_Withdrawal, hc])]
      exact ih

theorem hand_get_balance_after_withdrawals : spec_get_balance_after_withdrawals := by
  intro state vi ws hr0 hr1 hr2
  bridge_split
  unfold GenMainnet.get_balance_after_withdrawals EpochProofs.Spec.get_balance_after_withdrawals
  simp only [bind_pure]
  refine simI_intro ?_ ?_
  · apply sim_bind
    · refine sim_hand_eq (sim_sumU rfl _ rfl _) ?_
      congr 1
      exact withdrawn_eq ws vi.val
    · intro x hx
      try dsimp only
      bridge_run []
  · bridge_post
/-- `range(n)` and a list of zero flags, one per validator. -/
theorem pyRange_zero (n : Nat) : pyRange 0 (n : Int) 1 = .ok ((List.range n).map fun (i : Nat) => (i : Int)) := by
  unfold pyRange
  rw [if_neg (by decide)]
  simp; rfl

theorem mapM_const_ok {α β : Type} (xs : List α) (b : β) :
    xs.mapM (fun _ => (Except.ok b : SpecM β)) = .ok (List.replicate xs.length b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.mapM_cons, ih]; rfl

theorem hand_process_participation_flag_updates : spec_process_participation_flag_updates := by
  intro state hr0
  unfold GenMainnet.process_participation_flag_updates EpochProofs.Spec.process_participation_flag_updates
  have e1 : (uOf GenMainnet.ParticipationFlags (0 : Int) : SpecM GenMainnet.ParticipationFlags) = .ok ⟨0⟩ := rfl
  simp only [Int.ofNat_eq_natCast, pyRange_zero, e1, mapM_const_ok, ok_bind, bind_pure, lfrom_none,
    List.length_map, List.length_range]
  refine ⟨?_, post_true _⟩
  show Except.ok _ = Except.ok _
  simp [abs_BeaconState]
/-- The byte-wise xor: a `mapM` of integer xor over the zipped bytes. -/
theorem xor_mapM (F : Int × Int → SpecM Int) (hF : ∀ x y : Int, F (x, y) = iOp .bitXor x y)
    (a b : List UInt8) :
    ((a.map fun x => (x.toNat : Int)).zip (b.map fun x => (x.toNat : Int))).mapM F =
      .ok ((a.zip b).map fun p => ((p.1.toNat ^^^ p.2.toNat : Nat) : Int)) := by
  induction a generalizing b with
  | nil => rfl
  | cons x a ih =>
    cases b with
    | nil => rfl
    | cons y b =>
      simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons]
      rw [ih b, hF]
      rfl

theorem uint8_xor_ofNat (x y : UInt8) : UInt8.ofNat (x.toNat ^^^ y.toNat) = x ^^^ y := by
  apply UInt8.toNat.inj
  rw [UInt8.toNat_ofNat', UInt8.toNat_xor]
  apply Nat.mod_eq_of_lt
  exact Nat.xor_lt_two_pow (n := 8) x.toNat_lt y.toNat_lt

theorem toVec_zip_xor (a b : List UInt8) (ha : a.length = 32) (hb : b.length = 32) :
    toVec 32 ((a.zip b).map fun p => UInt8.ofNat ((((p.1.toNat ^^^ p.2.toNat : Nat) : Int)).toNat)) =
      Vector.zipWith (fun x1 x2 => x1 ^^^ x2) (toVec 32 a) (toVec 32 b) := by
  apply Vector.toList_inj.mp
  rw [toVec_toList _ _ (by simp [ha, hb]), Vector.toList_zipWith, toVec_toList _ _ ha,
    toVec_toList _ _ hb, List.map_zip_eq_zipWith]
  congr 1
  funext x y
  simp only [Function.curry, Int.toNat_natCast, uint8_xor_ofNat]

theorem hand_xor : spec_xor := by
  intro a b ha hb
  unfold GenMainnet.xor EpochProofs.Spec.xor
  rw [xor_mapM _ (fun _ _ => by simp only [bind_pure]) _ _, ok_bind]
  have hl : ((a.data.zip b.data).map fun p =>
      UInt8.ofNat ((((p.1.toNat ^^^ p.2.toNat : Nat) : Int)).toNat)).length = BytesC.len GenMainnet.Bytes32 := by
    simp [ha, hb]
  simp only [List.map_map, Function.comp_def, bd, data_Bytes32]
  rw [bytesOf_ok _ hl]
  refine ⟨?_, fun x hx => by cases hx; rw [ofBytes_Bytes32]; simpa using hl⟩
  show Except.ok _ = Except.ok _
  dsimp only
  rw [ofBytes_Bytes32, toVec_zip_xor _ _ ha hb]
theorem zipIdx_map' {α β : Type} (f : α → β) (l : List α) (n : Nat) :
    (l.map f).zipIdx n = (l.zipIdx n).map (fun p => (f p.1, p.2)) := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- A hand `for` loop that appends to a list: the same as `filterMapM` of its step. -/
theorem forIn_append {α : Type} (l : List α) (acc : List Nat)
    (B : α → List Nat → EpochProofs.Spec.SpecM (ForInStep (List Nat)))
    (step : α → EpochProofs.Spec.SpecM (Option Nat))
    (hB : ∀ x a, B x a = step x >>= fun o => pure (ForInStep.yield (a ++ o.toList))) :
    forIn l acc B = (l.filterMapM step) >>= fun r => pure (acc ++ r) := by
  induction l generalizing acc with
  | nil => simp [List.filterMapM_nil]
  | cons x l ih =>
    rw [List.forIn_cons, hB, List.filterMapM_cons]
    cases h : step x with
    | error e => rfl
    | ok o =>
      rw [ok_bind, ok_bind]
      show forIn l (acc ++ o.toList) B = _
      rw [ih]
      cases o with
      | none => simp
      | some b =>
        cases hr : List.filterMapM step l with
        | error e => rfl
        | ok r => show Except.ok _ = Except.ok _; simp

theorem sim_filterMapM_gen {γ γ' δ δ' : Type} (k : δ → δ') (e : γ → γ') (F : γ → SpecM (Option δ))
    (G : γ' → HM (Option δ')) (L : List γ) (hF : ∀ x ∈ L, Sim (Option.map k) (F x) (G (e x))) :
    Sim (List.map k) (L.filterMapM F) ((L.map e).filterMapM G) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.map_cons, List.filterMapM_cons, List.filterMapM_cons]
    apply sim_bind (hF x (List.mem_cons_self ..))
    intro o _
    have ih' := ih (fun y hy => hF y (List.mem_cons_of_mem _ hy))
    cases o with
    | none => exact ih'
    | some d =>
      apply sim_bind ih'
      intro r _
      exact sim_pure _ _ _ rfl

/-- The hand `for` loop that collects eligible indices, against the readable comprehension. -/
theorem hand_get_eligible_validator_indices (h_get_previous_epoch : spec_get_previous_epoch)
    (h_is_active_validator : spec_is_active_validator) : spec_get_eligible_validator_indices := by
  intro state hr0
  bridge_split
  unfold GenMainnet.get_eligible_validator_indices EpochProofs.Spec.get_eligible_validator_indices
  simp only [bind_pure]
  refine simI_intro ?_ ?_
  · apply sim_bind
    · apply simI_sim; apply h_get_previous_epoch; assumption
    intro e he
    try dsimp only
    rw [forIn_append _ _ _ (fun (p : EpochProofs.Spec.Validator × Nat) =>
      if EpochProofs.Spec.is_active_validator p.1 e.val = true then pure (some p.2)
      else if p.1.slashed = true then do
        let ep ← EpochProofs.Spec.uint64Add e.val 1
        pure (if ep < p.1.withdrawable_epoch then some p.2 else none)
      else pure none)]
    · simp only [List.nil_append, bind_pure]
      have hz : (abs_BeaconState state).validators.zipIdx =
          (state.validators.zipIdx.map fun (x : GenMainnet.Validator × Nat) => ((x.2 : Int), x.1)).map
            (fun p => (abs_Validator p.2, p.1.toNat)) := by
        show (state.validators.map abs_Validator).zipIdx = _
        rw [zipIdx_map', List.map_map]
        rfl
      rw [hz]
      apply sim_filterMapM_gen
      intro x hx
      obtain ⟨⟨v, i⟩, hm, rfl⟩ := List.mem_map.mp hx
      have hgi := List.mk_mem_zipIdx_iff_getElem?.mp hm
      have hvi : v ∈ state.validators := List.mem_of_getElem? hgi
      have hil : i < state.validators.length := (List.getElem?_eq_some_iff.mp hgi).1
      have hirv : IR_Validator v := by bridge_mem
      have hre : e.val < 2 ^ 64 := (h_get_previous_epoch state hr0).2 e he
      have hia := simI_sim (h_is_active_validator v e hirv hre)
      dsimp only
      cases hb : EpochProofs.Spec.is_active_validator (abs_Validator v) e.val with
      | true =>
        have hok : GenMainnet.is_active_validator v e = .ok true := by
          unfold Sim at hia; rw [hb] at hia
          cases h : GenMainnet.is_active_validator v e <;> rw [h] at hia <;> cases hia; rfl
        rw [hok, ok_bind, if_pos rfl, if_pos rfl, uOf_ok _ rfl (by omega), ok_bind, Int.toNat_natCast]
        rfl
      | false =>
        have hok : GenMainnet.is_active_validator v e = .ok false := by
          unfold Sim at hia; rw [hb] at hia
          cases h : GenMainnet.is_active_validator v e <;> rw [h] at hia <;> cases hia; rfl
        rw [hok, ok_bind]
        have hs' : (abs_Validator v).slashed = v.slashed.val := rfl
        rw [hs']
        by_cases hs : v.slashed.val = true
        · simp only [Bool.false_eq_true, ↓reduceIte, hs]
          have hwe : (abs_Validator v).withdrawable_epoch = v.withdrawable_epoch.val := rfl
          rw [hwe]
          by_cases hov : e.val + 1 < 2 ^ 64
          · have hadd : (uOp .add (uv e) 1 : SpecM GenMainnet.Epoch) = .ok ⟨e.val + 1⟩ := by
              rw [show uv e = ((e.val : Nat) : Int) from rfl, show (1 : Int) = ((1 : Nat) : Int) from rfl,
                uOp_add_nat (α := GenMainnet.Epoch) rfl, if_pos hov]; rfl
            have hadd' : EpochProofs.Spec.uint64Add e.val 1 = .ok (e.val + 1) := by
              unfold EpochProofs.Spec.uint64Add; rw [if_pos (by simpa [EpochProofs.Spec.UINT64_SIZE] using hov)]; rfl
            rw [hadd, ok_bind, hadd', ok_bind]
            by_cases hlt : e.val + 1 < v.withdrawable_epoch.val
            · have hd : decide (uv (⟨e.val + 1⟩ : GenMainnet.Epoch) < uv v.withdrawable_epoch) = true := by
                simp [uv]; omega
              rw [hd]
              simp only [pure_bind, ↓reduceIte, hlt]
              rw [uOf_ok _ rfl (by omega), ok_bind, Int.toNat_natCast]
              rfl
            · have hd : decide (uv (⟨e.val + 1⟩ : GenMainnet.Epoch) < uv v.withdrawable_epoch) = false := by
                simp [uv]; omega
              rw [hd]
              simp only [pure_bind, Bool.false_eq_true, ↓reduceIte, hlt]
              rfl
          · have hadd : (uOp .add (uv e) 1 : SpecM GenMainnet.Epoch) = .error .bug := by
              rw [show uv e = ((e.val : Nat) : Int) from rfl, show (1 : Int) = ((1 : Nat) : Int) from rfl,
                uOp_add_nat (α := GenMainnet.Epoch) rfl, if_neg hov]
            have hadd' : EpochProofs.Spec.uint64Add e.val 1 = .error .overflow := by
              unfold EpochProofs.Spec.uint64Add; rw [if_neg (by simpa [EpochProofs.Spec.UINT64_SIZE] using hov)]; rfl
            rw [hadd, err_bind, hadd', err_bind]
            rfl
        · simp only [Bool.false_eq_true, ↓reduceIte, hs]
          rfl
    · intro ⟨v, i⟩ a
      dsimp only
      split
      · rfl
      · split
        · cases EpochProofs.Spec.uint64Add e.val 1 with
          | error _ => rfl
          | ok ep =>
            show (if _ then _ else _) = _
            by_cases hl : ep < v.withdrawable_epoch
            · rw [if_pos hl]; show _ = (pure (if ep < v.withdrawable_epoch then some i else none) >>= _)
              rw [if_pos hl]; rfl
            · rw [if_neg hl]; show _ = (pure (if ep < v.withdrawable_epoch then some i else none) >>= _)
              rw [if_neg hl]; simp
        · simp
  · bridge_post
/-- A readable index loop that adds the amounts of the items that pass a test, against the hand
`for` loop over the same items. -/
theorem sum_loop {α β : Type} (xs : List α) (ab : α → β) (cond : α → Bool) (cond' : β → Bool)
    (amt : α → GenMainnet.Gwei) (amt' : β → Nat)
    (hc : ∀ x, cond' (ab x) = cond x) (ha : ∀ x, amt' (ab x) = (amt x).val)
    (L : Nat → GenMainnet.Gwei → SpecM GenMainnet.Gwei)
    (hL : ∀ i b, L i b = if i < xs.length then
        (lget xs (i : Int) >>= fun x => if cond x = true then
          (lget xs (i : Int) >>= fun y => uOp .add (uv b) (uv (amt y)) >>= fun b' => L (i + 1) b')
        else L (i + 1) b)
      else pure b)
    (B : β → Nat → EpochProofs.Spec.SpecM (ForInStep Nat))
    (hB : ∀ w r, B w r = if cond' w = true then
        (EpochProofs.Spec.uint64Add r (amt' w) >>= fun r' => pure (ForInStep.yield r'))
      else pure (ForInStep.yield r))
    (i : Nat) (b : GenMainnet.Gwei) (hb : b.val < 2 ^ 64) :
    SimI (fun x : GenMainnet.Gwei => x.val < 2 ^ 64) (fun x => x.val) (L i b)
      (forIn ((xs.map ab).drop i) b.val B) := by
  rw [hL]
  by_cases hi : i < xs.length
  · rw [if_pos hi]
    have hg : lget xs (i : Int) = .ok xs[i] := by
      unfold lget Rd.pyIndex
      rw [if_neg (by omega), if_pos (by omega)]
      simp [hi]; rfl
    have hd : (xs.map ab).drop i = ab xs[i] :: (xs.map ab).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
    rw [hd, List.forIn_cons, hB, hg, ok_bind, hc, ha]
    have ih := fun b' (hb' : GenMainnet.Gwei.val b' < 2 ^ 64) =>
      sum_loop xs ab cond cond' amt amt' hc ha L hL B hB (i + 1) b' hb'
    generalize xs[i] = w at *
    by_cases hcw : cond w = true
    · rw [if_pos hcw, if_pos hcw, ok_bind]
      by_cases ho : b.val + (amt w).val < 2 ^ 64
      · have e1 : (uOp .add (uv b) (uv (amt w)) : SpecM GenMainnet.Gwei) = .ok ⟨b.val + (amt w).val⟩ := by
          rw [show uv b = ((b.val : Nat) : Int) from rfl, show uv (amt w) = (((amt w).val : Nat) : Int) from rfl,
            uOp_add_nat (α := GenMainnet.Gwei) rfl, if_pos ho]; rfl
        have e2 : EpochProofs.Spec.uint64Add b.val (amt w).val = .ok (b.val + (amt w).val) := by
          unfold EpochProofs.Spec.uint64Add
          rw [if_pos (by simpa [EpochProofs.Spec.UINT64_SIZE] using ho)]; rfl
        rw [e1, ok_bind, e2, ok_bind]
        exact ih ⟨b.val + (amt w).val⟩ ho
      · have e1 : (uOp .add (uv b) (uv (amt w)) : SpecM GenMainnet.Gwei) = .error .bug := by
          rw [show uv b = ((b.val : Nat) : Int) from rfl, show uv (amt w) = (((amt w).val : Nat) : Int) from rfl,
            uOp_add_nat (α := GenMainnet.Gwei) rfl, if_neg ho]
        have e2 : EpochProofs.Spec.uint64Add b.val (amt w).val = .error .overflow := by
          unfold EpochProofs.Spec.uint64Add
          rw [if_neg (by simpa [EpochProofs.Spec.UINT64_SIZE] using ho)]; rfl
        rw [e1, err_bind, e2, err_bind]
        exact ⟨rfl, fun x hx => by cases hx⟩
    · rw [if_neg hcw, if_neg hcw]
      exact ih b hb
  · rw [if_neg hi]
    have hd : (xs.map ab).drop i = [] := by simp; omega
    rw [hd]
    exact ⟨rfl, fun x hx => by cases hx; exact hb⟩
termination_by xs.length - i

theorem hand_get_pending_balance_to_withdraw_for_builder : spec_get_pending_balance_to_withdraw_for_builder := by
  intro st bi hr0 hr1
  unfold GenMainnet.get_pending_balance_to_withdraw_for_builder EpochProofs.Spec.get_pending_balance_to_withdraw_for_builder
  simp only [bind_pure]
  have e0 : (uOf GenMainnet.Gwei (0 : Int) : SpecM GenMainnet.Gwei) = .ok ⟨0⟩ := rfl
  rw [e0, ok_bind]
  have h1 := sum_loop st.builder_pending_withdrawals abs_BuilderPendingWithdrawal
    (fun x => uv x.builder_index == uv bi) (fun w => w.builder_index == bi.val) (·.amount) (·.amount)
    (fun x => (int_beq_nat _ _).symm) (fun x => rfl)
    (GenMainnet.get_pending_balance_to_withdraw_for_builder.loop1 bi st st.builder_pending_withdrawals.length)
    (fun i b => by rw [GenMainnet.get_pending_balance_to_withdraw_for_builder.loop1]; rfl) _
    (fun w r => rfl) 0 ⟨0⟩ (by decide)
  have h2 := fun (x : GenMainnet.Gwei) (hx : x.val < 2 ^ 64) =>
    sum_loop st.builder_pending_payments abs_BuilderPendingPayment
    (fun x => uv x.withdrawal.builder_index == uv bi) (fun w => w.withdrawal.builder_index == bi.val)
    (·.withdrawal.amount) (·.withdrawal.amount)
    (fun x => (int_beq_nat _ _).symm) (fun x => rfl)
    (GenMainnet.get_pending_balance_to_withdraw_for_builder.loop2 bi st st.builder_pending_payments.length)
    (fun i b => by rw [GenMainnet.get_pending_balance_to_withdraw_for_builder.loop2]; rfl) _
    (fun w r => rfl) 0 x hx
  refine simI_intro ?_ ?_
  · apply sim_bind (simI_sim h1)
    intro x hx
    exact simI_sim (h2 x (h1.2 x hx))
  · apply post_bind
    intro x hx
    exact (h2 x (h1.2 x hx)).2
theorem hand_get_pending_balance_to_withdraw : spec_get_pending_balance_to_withdraw := by
  intro st vi hr0 hr1
  unfold GenMainnet.get_pending_balance_to_withdraw EpochProofs.Spec.get_pending_balance_to_withdraw
  simp only [bind_pure]
  have e0 : (uOf GenMainnet.Gwei (0 : Int) : SpecM GenMainnet.Gwei) = .ok ⟨0⟩ := rfl
  rw [e0, ok_bind]
  exact sum_loop st.pending_partial_withdrawals abs_PendingPartialWithdrawal
    (fun x => uv x.validator_index == uv vi) (fun w => w.validator_index == vi.val) (·.amount) (·.amount)
    (fun x => (int_beq_nat _ _).symm) (fun x => rfl)
    (GenMainnet.get_pending_balance_to_withdraw.loop1 st vi st.pending_partial_withdrawals.length)
    (fun i b => by rw [GenMainnet.get_pending_balance_to_withdraw.loop1]; rfl) _
    (fun w r => rfl) 0 ⟨0⟩ (by decide)

/-- The search loop for a free builder index: the readable loop returns the same first index as
the hand `for` loop with an early `return`. -/
theorem nb_loop (st : GenMainnet.BeaconState) (e : GenMainnet.Epoch)
    (he : GenMainnet.get_current_epoch st = .ok e)
    (he' : EpochProofs.Spec.get_current_epoch Hand (abs_BeaconState st) = .ok e.val)
    (hlen : st.builders.length < 2 ^ 64)
    (B : Nat → MProd (Option Nat) PUnit → EpochProofs.Spec.SpecM (ForInStep (MProd (Option Nat) PUnit)))
    (hB : ∀ index r, B index r = (have _r := r.snd; do
      let builder ← EpochProofs.Spec.listGet (abs_BeaconState st).builders index
      let __do_lift ← EpochProofs.Spec.get_current_epoch Hand (abs_BeaconState st)
      if (decide (builder.withdrawable_epoch ≤ __do_lift) && builder.balance == 0) = true then
        pure (ForInStep.done ⟨some index, PUnit.unit⟩)
      else do
        pure PUnit.unit
        pure (ForInStep.yield ⟨none, PUnit.unit⟩)))
    (i : Nat) (hi : i ≤ st.builders.length) :
    ∃ o : Option Nat, (∀ j ∈ o, j < st.builders.length) ∧
      GenMainnet.get_index_for_new_builder.loop1 st st.builders.length i =
        .ok (o.map (fun j => (⟨j⟩ : GenMainnet.BuilderIndex)), ()) ∧
      forIn ((List.range st.builders.length).drop i) ⟨none, PUnit.unit⟩ B = .ok ⟨o, PUnit.unit⟩ := by
  rw [GenMainnet.get_index_for_new_builder.loop1]
  by_cases hlt : i < st.builders.length
  · rw [dif_pos hlt]
    have hg : lget st.builders (i : Int) = .ok st.builders[i] := by
      unfold lget Rd.pyIndex
      rw [if_neg (by omega), if_pos (by omega)]
      simp [hlt]; rfl
    have hg' : EpochProofs.Spec.listGet (abs_BeaconState st).builders i =
        .ok (abs_Builder st.builders[i]) := by
      show EpochProofs.Spec.listGet (st.builders.map abs_Builder) i = _
      unfold EpochProofs.Spec.listGet
      simp [hlt]; rfl
    have hd : (List.range st.builders.length).drop i = i :: (List.range st.builders.length).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
    obtain ⟨o, ho, h1, h2⟩ := nb_loop st e he he' hlen B hB (i + 1) hlt
    rw [hd, List.forIn_cons, hB, hg', ok_bind, he', ok_bind]
    dsimp only
    rw [hg, ok_bind, he, ok_bind]
    generalize st.builders[i] = b at *
    by_cases hc : (decide (b.withdrawable_epoch.val ≤ e.val) && b.balance.val == 0) = true
    · refine ⟨some i, (fun j hj => by cases hj; exact hlt), ?_, ?_⟩
      · have hw : b.withdrawable_epoch.val ≤ e.val := by simp at hc; exact hc.1
        have hb0 : b.balance.val = 0 := by simp at hc; exact hc.2
        have d1 : decide (uv b.withdrawable_epoch ≤ uv e) = true := by simp [uv]; exact hw
        rw [d1, if_pos rfl, ok_bind]
        have d2 : (uv b.balance == 0) = true := by simp [uv, hb0]
        rw [d2, pure_bind, if_pos rfl, uOf_ok _ rfl (by omega), ok_bind]
        rfl
      · rw [if_pos (by simpa [abs_Builder] using hc)]
        rfl
    · refine ⟨o, ho, ?_, ?_⟩
      · by_cases hw : b.withdrawable_epoch.val ≤ e.val
        · have d1 : decide (uv b.withdrawable_epoch ≤ uv e) = true := by simp [uv]; exact hw
          have hb0 : ¬ b.balance.val = 0 := by simp [hw] at hc; exact hc
          have d2 : (uv b.balance == 0) = false := by simp [uv]; omega
          rw [d1, if_pos rfl, ok_bind, d2, pure_bind, if_neg (by decide)]
          exact h1
        · have d1 : decide (uv b.withdrawable_epoch ≤ uv e) = false := by simp [uv]; omega
          rw [d1, if_neg (by decide), pure_bind, if_neg (by decide)]
          exact h1
      · rw [if_neg (by simpa [abs_Builder] using hc)]
        exact h2
  · rw [dif_neg hlt]
    have hd : (List.range st.builders.length).drop i = [] := by simp; omega
    refine ⟨none, (fun j hj => by cases hj), rfl, ?_⟩
    rw [hd]; rfl
termination_by st.builders.length - i
theorem gce_ok (st : GenMainnet.BeaconState) (hs : st.slot.val < 2 ^ 64) :
    ∃ e : GenMainnet.Epoch, GenMainnet.get_current_epoch st = .ok e := by
  unfold GenMainnet.get_current_epoch GenMainnet.compute_epoch_at_slot
  simp only [bind_pure, uv, bridge_cast]
  rw [uOp_div_ok rfl st.slot.val _ (by decide) hs, ok_bind]
  exact ⟨_, uCast_ok _ rfl (by simp only [bridge_cast]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hs)⟩

theorem hand_get_index_for_new_builder (h_get_current_epoch : spec_get_current_epoch) :
    spec_get_index_for_new_builder := by
  intro st hr0
  bridge_split
  obtain ⟨e, he⟩ := gce_ok st (by assumption)
  have hs := simI_sim (h_get_current_epoch st hr0)
  have he' : EpochProofs.Spec.get_current_epoch Hand (abs_BeaconState st) = .ok e.val := by
    unfold Sim at hs; rw [he] at hs
    cases h : EpochProofs.Spec.get_current_epoch Hand (abs_BeaconState st) <;> rw [h] at hs <;> cases hs; rfl
  have hlen : st.builders.length < 2 ^ 64 := by assumption
  unfold GenMainnet.get_index_for_new_builder EpochProofs.Spec.get_index_for_new_builder
  obtain ⟨o, ho, h1, h2⟩ := nb_loop st e he he' hlen _ (fun index r => rfl) 0 (Nat.zero_le _)
  rw [List.drop_zero] at h2
  show SimI _ _ (GenMainnet.get_index_for_new_builder.loop1 st st.builders.length 0 >>= _)
    (forIn (List.range (abs_BeaconState st).builders.length) _ _ >>= _)
  have hl' : (abs_BeaconState st).builders.length = st.builders.length := by simp [abs_BeaconState]
  rw [h1, ok_bind, hl', h2, ok_bind]
  cases o with
  | none =>
    simp only [Option.map_none]
    show SimI _ _ (pure PUnit.unit >>= fun _ => uOf GenMainnet.BuilderIndex ((st.builders.length : Nat) : Int) >>= pure) _
    rw [uOf_ok _ rfl hlen]
    exact ⟨rfl, fun x hx => by cases hx; exact hlen⟩
  | some j =>
    have hj := ho j rfl
    exact ⟨rfl, fun x hx => by cases hx; show j < 2 ^ 64; omega⟩
/-- `assert slot < state.slot <= slot + SLOTS_PER_HISTORICAL_ROOT`: one readable `assert` of a
chained comparison against two hand checks. -/
theorem hand_get_block_root_at_slot : spec_get_block_root_at_slot := by
  intro st slot hr0 hr1
  bridge_split
  unfold GenMainnet.get_block_root_at_slot EpochProofs.Spec.get_block_root_at_slot
  simp only [bind_pure]
  have hsl : (abs_BeaconState st).slot = st.slot.val := rfl
  rw [hsl]
  have hsp : Hand.SLOTS_PER_HISTORICAL_ROOT = GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val := by decide
  rw [hsp]
  by_cases h1 : slot.val < st.slot.val
  · have d1 : decide (uv slot < uv st.slot) = true := by simp [uv]; exact h1
    rw [if_pos d1, if_neg (by simpa using h1)]
    have hS : GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val = 8192 := rfl
    by_cases ho : slot.val + GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val < 2 ^ 64
    · have e1 : (uOp .add (uv slot) (uv GenMainnet.SLOTS_PER_HISTORICAL_ROOT) : SpecM GenMainnet.Slot) =
          .ok ⟨slot.val + GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val⟩ := by
        rw [show uv slot = ((slot.val : Nat) : Int) from rfl,
          show uv GenMainnet.SLOTS_PER_HISTORICAL_ROOT = ((GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val : Nat) : Int) from rfl,
          uOp_add_nat (α := GenMainnet.Slot) rfl, if_pos ho]; rfl
      have e2 : EpochProofs.Spec.uint64Add slot.val GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val =
          .ok (slot.val + GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val) := by
        unfold EpochProofs.Spec.uint64Add
        rw [if_pos (by simpa [EpochProofs.Spec.UINT64_SIZE] using ho)]; rfl
      rw [e1, ok_bind, e2, ok_bind, pure_bind]
      by_cases h2 : st.slot.val ≤ slot.val + GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val
      · have d2 : decide (uv st.slot ≤ uv (⟨slot.val + GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val⟩ : GenMainnet.Slot)) = true := by
          simp [uv]; omega
        rw [d2, if_neg (by simpa using h2)]
        show SimI _ _ (pure () >>= fun _ => _) (pure PUnit.unit >>= fun _ => _)
        rw [pure_bind, pure_bind]
        rw [show uv slot = ((slot.val : Nat) : Int) from rfl,
          show uv GenMainnet.SLOTS_PER_HISTORICAL_ROOT = ((GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val : Nat) : Int) from rfl,
          uOp_mod_ok (α := GenMainnet.Slot) rfl slot.val _ (by rw [hS]; decide) hr1, ok_bind]
        refine ⟨sim_lget (fun x : GenMainnet.Root => toVec 32 x.data) st.block_roots _, ?_⟩
        intro x hx
        have hall : ∀ y ∈ st.block_roots, List.length y.data = 32 := by assumption
        exact hall x (lget_mem hx)
      · have d2 : decide (uv st.slot ≤ uv (⟨slot.val + GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val⟩ : GenMainnet.Slot)) = false := by
          simp [uv]; omega
        rw [d2, if_pos (by simpa using h2)]
        exact ⟨rfl, fun x hx => by cases hx⟩
    · have e1 : (uOp .add (uv slot) (uv GenMainnet.SLOTS_PER_HISTORICAL_ROOT) : SpecM GenMainnet.Slot) = .error .bug := by
        rw [show uv slot = ((slot.val : Nat) : Int) from rfl,
          show uv GenMainnet.SLOTS_PER_HISTORICAL_ROOT = ((GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val : Nat) : Int) from rfl,
          uOp_add_nat (α := GenMainnet.Slot) rfl, if_neg ho]
      have e2 : EpochProofs.Spec.uint64Add slot.val GenMainnet.SLOTS_PER_HISTORICAL_ROOT.val = .error .overflow := by
        unfold EpochProofs.Spec.uint64Add
        rw [if_neg (by simpa [EpochProofs.Spec.UINT64_SIZE] using ho)]; rfl
      rw [e1, err_bind, err_bind, e2, err_bind]
      exact ⟨rfl, fun x hx => by cases hx⟩
  · have d1 : ¬ decide (uv slot < uv st.slot) = true := by simp [uv]; omega
    rw [if_neg d1, if_pos (by simpa using h1)]
    exact ⟨rfl, fun x hx => by cases hx⟩
/-! ## Epoch processing: slashings -/

theorem u64add_eq (a b : Nat) : EpochProofs.Spec.uint64Add a b =
    if a + b < 2 ^ 64 then .ok (a + b) else .error .overflow := by
  unfold EpochProofs.Spec.uint64Add EpochProofs.Spec.UINT64_SIZE; split <;> rfl

theorem u64mul_eq (a b : Nat) : EpochProofs.Spec.uint64Mul a b =
    if a * b < 2 ^ 64 then .ok (a * b) else .error .overflow := by
  unfold EpochProofs.Spec.uint64Mul EpochProofs.Spec.UINT64_SIZE; split <;> rfl

theorem uop_add_eq {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) :
    (uOp .add (a : Int) (b : Int) : SpecM α) =
      if a + b < 2 ^ 64 then .ok (UintC.ofNat (a + b)) else .error .bug := uOp_add_nat hb a b

theorem uop_mul_eq {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) :
    (uOp .mul (a : Int) (b : Int) : SpecM α) =
      if a * b < 2 ^ 64 then .ok (UintC.ofNat (a * b)) else .error .bug := by
  unfold uOp
  simp only [erase, intArith, mapError_ok, ok_bind]
  rw [show (a : Int) * (b : Int) = ((a * b : Nat) : Int) by push_cast; rfl]
  by_cases h : a * b < 2 ^ 64
  · rw [uOf_ok _ hb h, if_pos h]
  · rw [uOf_neg _ hb (by omega), if_neg h]
theorem m_saturating_sub (a d : Nat) (ha : a < 2 ^ 64) :
    GenMainnet.saturating_sub ⟨a⟩ (d : Int) = .ok ⟨EpochProofs.Spec.saturating_sub a d⟩ := by
  unfold GenMainnet.saturating_sub EpochProofs.Spec.saturating_sub
  simp only [bind_pure, uOp, erase, intArith, uv, UintC.val]
  by_cases hgt : a > d
  · rw [if_pos (by simp; omega), if_pos hgt, mapError_ok, ok_bind,
      show (a : Int) - (d : Int) = ((a - d : Nat) : Int) by omega,
      uOf_ok (α := GenMainnet.Uint64) (a - d) rfl (by omega)]
    rfl
  · rw [if_neg (by simp; omega), if_neg hgt, mapError_ok, ok_bind,
      show (a : Int) - (a : Int) = ((a - a : Nat) : Int) by omega,
      uOf_ok (α := GenMainnet.Uint64) (a - a) rfl (by omega)]
    rfl

/-- `decrease_balance`: the readable Lean equals the hand spec on the balances, and keeps the
other fields. -/
theorem m_decrease_balance (r : GenMainnet.BeaconState) (i : GenMainnet.ValidatorIndex)
    (d : GenMainnet.Gwei) (hb : ∀ b ∈ r.balances, b.val < 2 ^ 64) :
    GenMainnet.decrease_balance r i d =
      ((EpochProofs.Spec.decrease_balance (r.balances.map (·.val)) i.val d.val).mapError errClass).map
        fun bs => { r with balances := bs.map GenMainnet.Gwei.mk } := by
  unfold GenMainnet.decrease_balance EpochProofs.Spec.decrease_balance
  dsimp only
  by_cases hi : i.val < r.balances.length
  · have hbi : r.balances[i.val].val < 2 ^ 64 := hb _ (List.getElem_mem hi)
    have hi' : i.val < (r.balances.map (·.val)).length := by simpa using hi
    have hg : EpochProofs.Spec.listGet (r.balances.map (·.val)) i.val = .ok r.balances[i.val].val := by
      unfold EpochProofs.Spec.listGet
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    have hs : ∀ v, EpochProofs.Spec.listSet (r.balances.map (·.val)) i.val v =
        .ok ((r.balances.map (·.val)).set i.val v) := fun v => by
      unfold EpochProofs.Spec.listSet
      rw [if_pos hi']
      rfl
    rw [show uv i = ((i.val : Nat) : Int) from rfl, lget_ok _ _ hi, ok_bind,
      show uv d = ((d.val : Nat) : Int) from rfl, m_saturating_sub _ _ hbi, ok_bind,
      lset_ok _ _ _ hi, ok_bind, hg, ok_bind, hs]
    show Except.ok _ = Except.ok _
    congr
    rw [List.map_set, List.map_map]
    have hid : (GenMainnet.Gwei.mk ∘ fun x : GenMainnet.Gwei => x.val) = id := rfl
    rw [hid, List.map_id]
  · have hg : EpochProofs.Spec.listGet (r.balances.map (·.val)) i.val = .error .indexOutOfRange := by
      unfold EpochProofs.Spec.listGet
      rw [List.getElem?_eq_none (by simpa using hi)]
      rfl
    rw [show uv i = ((i.val : Nat) : Int) from rfl, lget_err _ _ hi, err_bind, hg, err_bind]
    rfl

theorem hand_satsub_le (a d : Nat) : EpochProofs.Spec.saturating_sub a d ≤ a := by
  unfold EpochProofs.Spec.saturating_sub
  show (if a > d then a - d else a - a) ≤ a
  split <;> omega

theorem hand_db_range (l : List Nat) (i d : Nat) (bs : List Nat)
    (h : EpochProofs.Spec.decrease_balance l i d = .ok bs) (hl : ∀ x ∈ l, x < 2 ^ 64) :
    ∀ x ∈ bs, x < 2 ^ 64 := by
  unfold EpochProofs.Spec.decrease_balance at h
  unfold EpochProofs.Spec.listGet at h
  split at h
  · rename_i a ha
    rw [pure_bind] at h
    unfold EpochProofs.Spec.listSet at h
    split at h
    · cases h
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with h1 | h1
      · exact hl x h1
      · have hal : a < 2 ^ 64 := hl a (List.mem_of_getElem? ha)
        rw [h1]
        have := hand_satsub_le a d
        bridge_nat
        omega
    · cases h
  · cases h

/-- The readable slashing loop against the hand `for` loop over the validators: the state keeps
its other fields, and the balances follow the hand `decrease_balance`. -/
theorem slash_loop (st0 : GenMainnet.BeaconState) (e : GenMainnet.Epoch) (inc pp : GenMainnet.Gwei)
    (hinc : inc.val ≠ 0) (hlen : st0.validators.length < 2 ^ 64)
    (heb : ∀ v ∈ st0.validators, v.effective_balance.val < 2 ^ 64)
    (B : EpochProofs.Spec.Validator × Nat → List Nat → EpochProofs.Spec.SpecM (ForInStep (List Nat)))
    (hB : ∀ v i r, B (v, i) r = if v.slashed = true then
        (EpochProofs.Spec.uint64Div Hand.EPOCHS_PER_SLASHINGS_VECTOR 2 >>= fun h =>
          EpochProofs.Spec.uint64Add e.val h >>= fun target =>
            if (target == v.withdrawable_epoch) = true then
              (EpochProofs.Spec.uint64Div v.effective_balance inc.val >>= fun ebi =>
                EpochProofs.Spec.uint64Mul pp.val ebi >>= fun pen =>
                  EpochProofs.Spec.decrease_balance r i pen >>= fun r' => pure (ForInStep.yield r'))
            else pure (ForInStep.yield r))
      else pure (ForInStep.yield r))
    (i : Nat) (a b : GenMainnet.Gwei) (st : GenMainnet.BeaconState)
    (hst : st = { st0 with balances := st.balances }) (hbal : ∀ x ∈ st.balances, x.val < 2 ^ 64) :
    Sim (fun l => abs_BeaconState l.2.2)
      (GenMainnet.process_slashings.loop1 e inc pp st0.validators.length i a b st)
      (forIn (((st0.validators.map abs_Validator).zipIdx).drop i) (st.balances.map (·.val)) B >>=
        fun r => pure { abs_BeaconState st0 with balances := r }) := by
  rw [GenMainnet.process_slashings.loop1]
  by_cases hi : i < st0.validators.length
  · rw [dif_pos hi]
    have hv : st.validators = st0.validators := by rw [hst]
    have hg : lget st.validators (i : Int) = .ok st0.validators[i] := by rw [hv]; exact lget_ok _ _ hi
    have hd : ((st0.validators.map abs_Validator).zipIdx).drop i =
        (abs_Validator st0.validators[i], i) :: ((st0.validators.map abs_Validator).zipIdx).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
    have hebi := heb _ (List.getElem_mem hi)
    rw [hd, List.forIn_cons, hB]
    dsimp only
    rw [hg, ok_bind]
    generalize st0.validators[i] = v at *
    have hsl : (abs_Validator v).slashed = v.slashed.val := rfl
    rw [hsl]
    have ih := fun a' b' st' hst' hbal' => slash_loop st0 e inc pp hinc hlen heb B hB (i + 1) a' b' st' hst' hbal'
    by_cases hs : v.slashed.val = true
    · rw [if_pos hs, if_pos hs]
      have e1 : (uOp .floorDiv (uv GenMainnet.EPOCHS_PER_SLASHINGS_VECTOR) 2 : SpecM GenMainnet.Epoch) = .ok ⟨4096⟩ :=
        uOp_div_ok (α := GenMainnet.Epoch) rfl 8192 2 (by decide) (by decide)
      have e1' : EpochProofs.Spec.uint64Div Hand.EPOCHS_PER_SLASHINGS_VECTOR 2 = .ok 4096 := rfl
      rw [e1, e1']
      (repeat rw [ok_bind])
      rw [show uv e = ((e.val : Nat) : Int) from rfl, show uv (⟨4096⟩ : GenMainnet.Epoch) = ((4096 : Nat) : Int) from rfl,
        uop_add_eq (α := GenMainnet.Epoch) rfl, u64add_eq]
      by_cases ho : e.val + 4096 < 2 ^ 64
      · rw [if_pos ho, if_pos ho]
        (repeat rw [ok_bind])
        have hwe : (abs_Validator v).withdrawable_epoch = v.withdrawable_epoch.val := rfl
        rw [hwe]
        by_cases hw : e.val + 4096 = v.withdrawable_epoch.val
        · have d1 : (uv (UintC.ofNat (e.val + 4096) : GenMainnet.Epoch) == uv v.withdrawable_epoch) = true := by
            simp [uv, hw]
          have d2 : (e.val + 4096 == v.withdrawable_epoch.val) = true := by simp [hw]
          rw [pure_bind, d1, if_pos rfl, if_pos d2]
          (repeat rw [ok_bind])
          have heb' : (abs_Validator v).effective_balance = v.effective_balance.val := rfl
          rw [heb', show uv v.effective_balance = ((v.effective_balance.val : Nat) : Int) from rfl,
            show uv inc = ((inc.val : Nat) : Int) from rfl, uOp_div_ok (α := GenMainnet.Gwei) rfl _ _ hinc hebi,
            uint64Div_ok _ _ hinc]
          (repeat rw [ok_bind])
          rw [show uv pp = ((pp.val : Nat) : Int) from rfl,
            show uv (UintC.ofNat (v.effective_balance.val / inc.val) : GenMainnet.Gwei) =
              (((v.effective_balance.val / inc.val : Nat)) : Int) from rfl,
            uop_mul_eq (α := GenMainnet.Gwei) rfl, u64mul_eq]
          by_cases hm : pp.val * (v.effective_balance.val / inc.val) < 2 ^ 64
          · rw [if_pos hm, if_pos hm]
            (repeat rw [ok_bind])
            rw [uOf_ok (α := GenMainnet.ValidatorIndex) i rfl (by omega), ok_bind,
              m_decrease_balance st _ _ hbal]
            have hq : (UintC.ofNat i : GenMainnet.ValidatorIndex).val = i := rfl
            have hp : (UintC.ofNat (pp.val * (v.effective_balance.val / inc.val)) : GenMainnet.Gwei).val =
              pp.val * (v.effective_balance.val / inc.val) := rfl
            rw [hq, hp]
            cases hdb : EpochProofs.Spec.decrease_balance (List.map (fun x => x.val) st.balances) i
                (pp.val * (v.effective_balance.val / inc.val)) with
            | error err => rfl
            | ok bs =>
              rw [mapError_ok, show ∀ f : List Nat → GenMainnet.BeaconState, Except.map f (Except.ok bs : Except Fail (List Nat)) = Except.ok (f bs) from fun _ => rfl,
                ok_bind, ok_bind]
              have hbs := hand_db_range _ _ _ bs hdb (fun x hx => by
                obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hbal y hy)
              have hst' : ({ st with balances := bs.map GenMainnet.Gwei.mk } : GenMainnet.BeaconState) =
                  { st0 with balances := ({ st with balances := bs.map GenMainnet.Gwei.mk } : GenMainnet.BeaconState).balances } := by
                rw [hst]
              have hbal' : ∀ x ∈ ({ st with balances := bs.map GenMainnet.Gwei.mk } : GenMainnet.BeaconState).balances,
                  x.val < 2 ^ 64 := by
                intro x hx
                obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
                exact hbs y hy
              have := ih (UintC.ofNat (v.effective_balance.val / inc.val)) (UintC.ofNat (pp.val * (v.effective_balance.val / inc.val)))
                _ hst' hbal'
              have hmm : (({ st with balances := bs.map GenMainnet.Gwei.mk } : GenMainnet.BeaconState).balances.map (·.val)) = bs := by
                show (bs.map GenMainnet.Gwei.mk).map (·.val) = bs
                rw [List.map_map]; exact List.map_id bs
              rw [hmm] at this
              exact this
          · rw [if_neg hm, if_neg hm]
            rfl
        · have d1 : (uv (UintC.ofNat (e.val + 4096) : GenMainnet.Epoch) == uv v.withdrawable_epoch) = false := by
            simp [uv]; omega
          have d2 : ¬ (e.val + 4096 == v.withdrawable_epoch.val) = true := by simp [hw]
          rw [pure_bind, d1, if_neg (by decide), if_neg d2, pure_bind, pure_bind]
          exact ih a b st hst hbal
      · rw [if_neg ho, if_neg ho]
        rfl
    · rw [if_neg hs, if_neg hs, pure_bind, if_neg (by decide), pure_bind, pure_bind]
      exact ih a b st hst hbal
  · rw [dif_neg hi]
    have hd : ((st0.validators.map abs_Validator).zipIdx).drop i = [] := by simp; omega
    rw [hd]
    show Except.ok _ = Except.ok _
    rw [hst]
    rfl
termination_by st0.validators.length - i

theorem sim_bind_proj {α β γ : Type} {g : β → γ} {A : SpecM α} {k : α → β} {H : HM γ}
    (h : Sim (fun x => g (k x)) A H) : Sim g (A >>= fun x => pure (k x)) H := by
  unfold Sim at *
  cases A with
  | error e => exact h
  | ok a => exact h

theorem hand_process_slashings (h_get_current_epoch : spec_get_current_epoch)
    (h_get_total_active_balance : spec_get_total_active_balance) : spec_process_slashings := by
  intro st t hr0 hr1
  bridge_split
  unfold GenMainnet.process_slashings EpochProofs.Spec.process_slashings
  refine simI_intro ?_ (post_true _)
  apply sim_bind (simI_sim (h_get_current_epoch st hr0))
  intro e he
  apply sim_bind_val (sim_of_ok (simI_sim (h_get_total_active_balance st hr0)) hr1)
  intro tb htb hftb
  subst hftb
  dsimp only
  apply sim_bind (sim_sumU (α := GenMainnet.Gwei) rfl ⟨0⟩ rfl st.slashings)
  intro s1 hs1
  have hs1r := sumU_range hs1
  rw [uCast_ok s1 rfl (by simp only [bridge_cast, bridge_ir] at hs1r ⊢; omega), ok_bind]
  apply sim_bind (sim_uOp_mul (α := GenMainnet.Gwei) rfl _ _)
  intro m hm
  apply sim_bind_val (sim_pyMin2 (fun _ _ => rfl) _ _)
  intro adj hadj hfadj
  have htbr : tb.val < 2 ^ 64 := (h_get_total_active_balance st hr0).2 tb htb
  apply sim_bind (sim_uOp_div (α := GenMainnet.Gwei) rfl _ _ htbr)
  intro q hq
  have hmr := uOp_range hm
  have hadjr : UintC.val adj < 2 ^ 64 := by
    have := pyMin2_val hadj
    simp only [bridge_cast, bridge_ir] at hmr this ⊢
    omega
  have e2 : min (UintC.val m) tb.val = UintC.val adj := hfadj.symm
  rw [e2]
  apply sim_bind (sim_uOp_div (α := GenMainnet.Gwei) rfl _ _ hadjr)
  intro pp hpp
  apply sim_bind_proj
  have hlen : st.validators.length < 2 ^ 64 := by assumption
  have heb : ∀ v ∈ st.validators, v.effective_balance.val < 2 ^ 64 := by
    intro v hv
    have : IR_Validator v := by bridge_mem
    exact this.2.2.1
  have hbal : ∀ x ∈ st.balances, x.val < 2 ^ 64 := by assumption
  exact slash_loop st e GenMainnet.EFFECTIVE_BALANCE_INCREMENT pp (by decide) hlen heb _
    (fun v i r => rfl) 0 default default st rfl hbal
end Pythia.Bridge.Mainnet
