import SpecLean.Paths

/-!
# Decode lemmas

Facts about `decode` that the validation proofs use: how to unpack a decoded state, and how a
decoded value changes after one write.
-/

namespace SpecLean.Encode

open SpecLean SpecLean.Gen SpecLean.Readable

theorem mapM_some_iff {f : α → Option β} :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys ↔
      ys.length = xs.length ∧ ∀ (i : Nat) x, xs[i]? = some x → f x = ys[i]?
  | [], ys => by
    cases ys <;> simp
  | x :: xs, ys => by
    rw [List.mapM_cons]
    cases hx : f x with
    | none =>
      simp only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq, false_iff, not_and]
      intro _ h; have := h 0 x rfl; rw [hx] at this
      cases ys <;> simp_all
    | some y =>
      cases hm : xs.mapM f with
      | none =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq,
          false_iff, not_and]
        intro hl h
        cases ys with
        | nil => simp at hl
        | cons y' ys' =>
          have := (mapM_some_iff xs ys').mpr ⟨by simpa using hl,
            fun i z hz => by simpa using h (i + 1) z (by simpa using hz)⟩
          rw [hm] at this; cases this
      | some zs =>
        obtain ⟨hl, hz⟩ := (mapM_some_iff xs zs).mp hm
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
        constructor
        · intro e; subst e
          refine ⟨by simp [hl], fun i z h => ?_⟩
          cases i with
          | zero => simp at h; subst h; simp [hx]
          | succ i => simpa using hz i z (by simpa using h)
        · rintro ⟨hl', h⟩
          cases ys with
          | nil => simp at hl'
          | cons y' ys' =>
            have h0 := h 0 x rfl; rw [hx] at h0; simp at h0; subst h0
            congr 1
            have := (mapM_some_iff xs ys').mpr ⟨by simpa using hl',
              fun i z hz => by simpa using h (i + 1) z (by simpa using hz)⟩
            rw [hm] at this; exact (Option.some.inj this)

/-- A list decodes again after one element changes. -/
theorem mapM_set {f : α → Option β} {xs : List α} {ys : List β} (h : xs.mapM f = some ys)
    (i : Nat) (x : α) (y : β) (hy : f x = some y) :
    (xs.set i x).mapM f = some (ys.set i y) := by
  obtain ⟨hl, hf⟩ := (mapM_some_iff xs ys).mp h
  refine (mapM_some_iff _ _).mpr ⟨by simp [hl], fun j z hz => ?_⟩
  rw [List.getElem?_set] at hz ⊢
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < xs.length
    · simp only [↓reduceIte, if_pos hi, Option.some.injEq] at hz
      subst hz
      simp only [↓reduceIte, if_pos (hl ▸ hi)]
      exact hy
    · simp [hi] at hz
  · simp only [hij, ↓reduceIte] at hz ⊢; exact hf j z hz

/-- A list of references decodes the same when each element decodes the same. -/
theorem mapM_congr {f g : α → Option β} {xs : List α}
    (h : ∀ (i : Nat) x, xs[i]? = some x → f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, h 0 x rfl,
      ih (fun i z hz => h (i + 1) z (by simpa using hz))]

theorem decGwei_uint (n : Nat) (hn : n < 2 ^ 64) : decGwei (.uint gweiTy n) = some ⟨n⟩ := by
  simp [decGwei, decUint, gweiTy, UintTy.bits, hn]

theorem decGwei_some {v : Value} {g : Gwei} (h : decGwei v = some g) :
    v = .uint gweiTy g.val ∧ g.val < 2 ^ 64 := by
  unfold decGwei decUint at h
  cases v <;> (try rename_i l; cases l) <;> simp at h
  rename_i t n
  obtain ⟨⟨rfl, hn⟩, rfl⟩ := h
  exact ⟨rfl, by simpa [gweiTy, UintTy.bits] using hn⟩

/-- The parts of a decoded state. -/
theorem decState_some {h : Heap} {root : Nat} {s : BeaconState}
    (hd : decState h (.ref root) = some s) :
    ∃ fs va ba vrefs bs, h.objs root = some (.container Id.BeaconState fs) ∧
      fs[fValidators]? = some (.ref va) ∧ fs[fBalances]? = some (.ref ba) ∧
      h.objs va = some (.list .progressiveList (.container Id.Validator) none vrefs) ∧
      vrefs.mapM (decValidator h) = some s.validators ∧
      h.objs ba = some (.list .progressiveList (.uint gweiTy) none bs) ∧
      bs.mapM decGwei = some s.balances := by
  simp only [decState] at hd
  cases ho : h.objs root with
  | none => simp [ho] at hd
  | some o =>
    cases o with
    | list => simp [ho] at hd
    | dict | set | closure => simp [ho] at hd
    | container ty fs =>
      simp only [ho] at hd
      by_cases hty : ty = Id.BeaconState
      · subst hty
        cases hv : fs[fValidators]? with
        | none => simp [hv] at hd
        | some wv =>
          cases hb : fs[fBalances]? with
          | none => simp [hv, hb] at hd
          | some wb =>
            simp only [hv, hb, Option.bind_eq_bind, Option.bind_some] at hd
            cases wv
            all_goals try (simp [decList] at hd; done)
            rename_i va
            cases wb
            all_goals try (simp [decList] at hd; done)
            rename_i ba
            simp only [decList] at hd
            cases hova : h.objs va with
            | none => simp [hova] at hd
            | some ov =>
              cases ov with
              | container => simp [hova] at hd
              | dict | set | closure => simp [hova] at hd
              | list kv ev lv xv =>
                cases kv <;> cases lv <;> simp [hova] at hd
                by_cases hev : ev = .container Id.Validator
                · subst hev
                  cases hmv : xv.mapM (decValidator h) with
                  | none => simp [hmv] at hd
                  | some vals =>
                    cases hoba : h.objs ba with
                    | none => simp [hmv, hoba] at hd
                    | some ob =>
                      cases ob with
                      | container => simp [hmv, hoba] at hd
                      | dict | set | closure => simp [hmv, hoba] at hd
                      | list kb eb lb xb =>
                        cases kb <;> cases lb <;> simp [hmv, hoba] at hd
                        by_cases heb : eb = .uint gweiTy
                        · subst heb
                          cases hmb : xb.mapM decGwei with
                          | none => simp [hmb] at hd
                          | some bals =>
                            simp [hmb] at hd
                            subst hd
                            exact ⟨fs, va, ba, xv, xb, rfl, hv, hb, hova, hmv, hoba, hmb⟩
                        · simp [heb] at hd
                · simp [hev] at hd
      · simp [hty] at hd

/-- A state decodes from its parts. -/
theorem decState_of {h : Heap} {root : Nat} {fs va ba vrefs bs}
    {vals : List Validator} {bals : List Gwei}
    (ho : h.objs root = some (.container Id.BeaconState fs))
    (hv : fs[fValidators]? = some (.ref va)) (hb : fs[fBalances]? = some (.ref ba))
    (hova : h.objs va = some (.list .progressiveList (.container Id.Validator) none vrefs))
    (hmv : vrefs.mapM (decValidator h) = some vals)
    (hoba : h.objs ba = some (.list .progressiveList (.uint gweiTy) none bs))
    (hmb : bs.mapM decGwei = some bals) :
    decState h (.ref root) = some { validators := vals, balances := bals } := by
  simp [decState, ho, hv, hb, decList, hova, hoba, hmv, hmb]

theorem decBytes_some {cls len : Nat} {v : Value} {b : List UInt8}
    (h : decBytes cls len v = some b) : v = .bytes cls b := by
  unfold decBytes at h
  cases v <;> simp at h
  obtain ⟨⟨rfl, -⟩, rfl⟩ := h; rfl

/-- The parts of a decoded validator. -/
theorem decValidator_some {h : Heap} {r : Nat} {v : Validator}
    (hd : decValidator h (.ref r) = some v) :
    ∃ fs, h.objs r = some (.container Id.Validator fs) ∧ decValidatorFields fs = some v := by
  simp only [decValidator] at hd
  cases ho : h.objs r with
  | none => simp [ho] at hd
  | some o =>
    cases o with
    | list => simp [ho] at hd
    | dict | set | closure => simp [ho] at hd
    | container ty fs =>
      simp only [ho] at hd
      by_cases hty : ty = Id.Validator
      · subst hty; simp only [↓reduceIte] at hd; exact ⟨fs, rfl, hd⟩
      · simp [hty] at hd

theorem decValidatorFields_eb {fs : List Value} {v : Validator}
    (h : decValidatorFields fs = some v) :
    fs[fEffectiveBalance]? = some (.uint gweiTy v.effective_balance.val) ∧
      v.effective_balance.val < 2 ^ 64 ∧
      fs[fWithdrawalCredentials]? = some (.bytes Id.Bytes32 v.withdrawal_credentials.data) ∧
      fs.length = 8 := by
  simp only [decValidatorFields, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨pk, ⟨x0, h0, d0⟩, wc, ⟨x1, h1, d1⟩, eb, ⟨x2, h2, d2⟩, sl, ⟨x3, h3, d3⟩,
    e4, ⟨x4, h4, d4⟩, e5, ⟨x5, h5, d5⟩, e6, ⟨x6, h6, d6⟩, e7, ⟨x7, h7, d7⟩, hif⟩ := h
  split at hif
  · rename_i hlen
    cases hif
    obtain ⟨rfl, hb⟩ := decGwei_some d2
    exact ⟨h2, hb, by rw [h1, decBytes_some d1], hlen⟩
  · cases hif

/-- A validator decodes again after a write of its effective balance. -/
theorem decValidatorFields_set_eb {fs : List Value} {v : Validator}
    (h : decValidatorFields fs = some v) (m : Nat) (hm : m < 2 ^ 64) :
    decValidatorFields (fs.set fEffectiveBalance (.uint gweiTy m)) =
      some { v with effective_balance := ⟨m⟩ } := by
  simp only [decValidatorFields, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨pk, ⟨x0, h0, d0⟩, wc, ⟨x1, h1, d1⟩, eb, ⟨x2, h2, d2⟩, sl, ⟨x3, h3, d3⟩,
    e4, ⟨x4, h4, d4⟩, e5, ⟨x5, h5, d5⟩, e6, ⟨x6, h6, d6⟩, e7, ⟨x7, h7, d7⟩, hif⟩ := h
  split at hif
  · rename_i hlen
    cases hif
    have e : ∀ k, k ≠ fEffectiveBalance →
        (fs.set fEffectiveBalance (.uint gweiTy m))[k]? = fs[k]? :=
      fun k hk => List.getElem?_set_ne (Ne.symm hk)
    have e2 : (fs.set fEffectiveBalance (.uint gweiTy m))[fEffectiveBalance]? =
        some (.uint gweiTy m) := by
      rw [List.getElem?_set_self (by rw [hlen]; decide)]
    simp only [decValidatorFields, bind, pure, e 0 (by decide), e 1 (by decide), e2,
      e 3 (by decide), e 4 (by decide), e 5 (by decide), e 6 (by decide), e 7 (by decide),
      h0, h1, h3, h4, h5, h6, h7, Option.bind_some, d0, d1, d3, d4, d5, d6, d7,
      decGwei_uint m hm, List.length_set, hlen, ↓reduceIte]
  · cases hif

end SpecLean.Encode
