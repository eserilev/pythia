import SpecLean.Validation.EffectiveBalance
import SpecLean.Validation.Loop

/-!
# `process_effective_balance_updates` through the generic loop lemma

The same theorem as `process_effective_balance_updates_run`, with the loop part done by
`for_enum_sim`. The invariant speaks only of the current heap. Each step proves the contract
from the heap at its start, and the lemma chains the steps. The step itself is `peb_step`, run
with the current heap as its start heap.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Gen SpecLean.Encode

variable (sha : Oracle) {gfp : Footprint}

/-- The readable loop over the length at loop entry, as the translator emits it. -/
def pebLoopN (N i : Nat) (s : Readable.BeaconState) : Except Fail Readable.BeaconState :=
  if i < N then Readable.process_effective_balance_updates.body s i >>= fun s' => pebLoopN N (i + 1) s'
  else pure s
termination_by N - i

theorem pebLoopN_eq (N : Nat) : ∀ i s, s.validators.length = N →
    pebLoopN N i s = Readable.process_effective_balance_updates.loop s i := by
  intro i
  induction h : N - i generalizing i with
  | zero =>
    intro s hs
    rw [pebLoopN, peb_loop_eq, if_neg (by omega), if_neg (by omega)]
  | succ m ih =>
    intro s hs
    rw [pebLoopN, peb_loop_eq, if_pos (by omega), if_pos (by omega)]
    cases hb : Readable.process_effective_balance_updates.body s i with
    | error => rfl
    | ok s' =>
      simp only [Except.bind_ok']
      exact ih (i + 1) (by omega) s'
        ((Readable.process_effective_balance_updates.body_length hb).trans hs)

/-- The loop invariant, on the current heap only. -/
def PebI (h0 : Heap) (Ly : PebLayout) (_i : Nat) (s : Readable.BeaconState) (L : Locals)
    (h : Heap) : Prop :=
  Ly.Ok h ∧ decState h (.ref Ly.root) = some s ∧ ReadsOk L Ly.root ∧
  WTree h [.ref Ly.root] peb_fp ∧ StateRest h0 h (.ref Ly.root)

theorem pebI_len {h0 Ly i s L h} (hp : PebI h0 Ly i s L h) :
    s.validators.length = Ly.vrefs.length := by
  obtain ⟨hl, hd, -⟩ := hp
  rw [decState_layout hl] at hd
  cases hm : Ly.vrefs.mapM (decValidator h) with
  | none => simp [hm] at hd
  | some vals =>
    cases hm2 : Ly.bs.mapM decGwei with
    | none => simp [hm, hm2] at hd
    | some bals =>
      simp only [hm, hm2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at hd
      subst hd
      exact ((mapM_some_iff _ _).mp hm).1

/-- The new invariant is the old one with the current heap as its start heap. -/
theorem pebI_inv {h0 Ly i s L h} (hp : PebI h0 Ly i s L h) : PebInv h Ly i s L h := by
  obtain ⟨hl, hd, hL, hw, -⟩ := hp
  exact ⟨hl, hd, hL, hw, Frame_refl _ _ _, Fresh_refl h, hl, fun _ _ _ _ => rfl, fun _ _ _ e => e⟩

/-- The old invariant after one step gives the new one and the contract of the step. -/
theorem pebI_step {h0 Ly i s L h i' s' L' h'} (hp : PebI h0 Ly i s L h)
    (hq : PebInv h Ly i' s' L' h') :
    Contract gfp peb_fp [.ref Ly.root] h h' ∧ PebI h0 Ly i' s' L' h' := by
  obtain ⟨hl', hd', hL', hw', hf, hfr, hl, hrest, ha⟩ := hq
  refine ⟨⟨hf, hfr, noNewPaths_of_reach fun k q b e => .inl (ha k q b e), ?_⟩,
    hl', hd', hL', hw', StateRest_trans hp.2.2.2.2 hrest⟩
  rintro k ty ⟨a, hk, ho⟩
  match k, hk with
  | 0, hk =>
    simp at hk; subst hk
    rcases ho with ⟨fs, ho⟩ | ⟨kd, e, l, xs, -, ho⟩ <;> rw [hl'.1] at ho <;> cases ho
    exact rootTy_container rfl hl.1

/-- `process_effective_balance_updates_run`, with the loop through `for_enum_sim`. -/
theorem process_effective_balance_updates_run' (k : Nat) (h : Heap) (root : Nat)
    (state : Readable.BeaconState) (hd : decState h (.ref root) = some state)
    (hw : WTree h [.ref root] peb_fp) (hwf : HeapWF h) (hsub : ∀ p ∈ peb_fp, p ∈ gfp) :
    ResultMatches gfp peb_fp h [.ref root] (PebExpect h root)
      (callName (env sha) (k + state.validators.length + 26)
        Id.process_effective_balance_updates [.ref root] h)
      (Readable.process_effective_balance_updates state) := by
  obtain ⟨fs, va, ba, vrefs, bs, hroot, hfv, hfb, hova, hmv, hoba, hmb⟩ := decState_some hd
  let Ly : PebLayout := ⟨root, va, ba, fs, vrefs, bs⟩
  have hl : Ly.Ok h := ⟨hroot, hfv, hfb, hova, hoba⟩
  have hvlen : state.validators.length = vrefs.length := ((mapM_some_iff _ _).mp hmv).1
  obtain ⟨l, t, it, body, hfn⟩ : ∃ l t it body,
      fn_process_effective_balance_updates.body = [.forStmt l t it body] := ⟨_, _, _, _, rfl⟩
  have hfor := for_enum_sim (env sha) t body va 20 vrefs.length
    (fun K s i => Readable.process_effective_balance_updates.body s i >>= K) id
    (pebLoopN vrefs.length) (fun i s => by rw [pebLoopN]; rfl) (vs := [.ref root]) hsub hwf (PebI h Ly)
    (fun _ _ _ => False) (fun _ _ _ _ => False)
    (fun i s L h' hp => ⟨_, _, _, _, hp.1.2.2.2.1, rfl⟩) ?hstep
    (k + state.validators.length + 3) 0 state (Locals.empty.set Id.state (.ref root)) h ?hinit
    (Contract.refl _ _ _ h) (by omega)
  case hstep =>
    intro n i s L h' x hp hi hx K
    obtain ⟨x', hx', hs⟩ := peb_step sha h' Ly l t it body hfn n i s L h' (pebI_inv hp)
      (by rw [pebI_len hp]; exact hi)
    have : x' = enumItem i x := by simp [Ly, iterItem, hx] at hx'; exact hx'.symm
    subst this
    exact iterK_of_stepRel hs fun s' L' h'' hq => pebI_step hp hq
  case hinit =>
    refine ⟨hl, hd, ?_, hw, fun _ _ _ _ => rfl⟩
    simp (config := { decide := true }) [ReadsOk, Ly]
  simp only [fn_process_effective_balance_updates, List.cons.injEq, Stmt.forStmt.injEq,
    and_true] at hfn
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hfn
  rw [callName, callValue_fn _ _ _ (g_peb sha)]
  simp [callFn, fn_process_effective_balance_updates, execBlock, execStmt, evalExpr, evalList,
    evalArgs, lookupName, bindArgs, bindArgs.go, g_enumerate sha,
    getAttr_container _ hroot (fi_validators sha), hfv, call_enumerate, applyBuiltin,
    LibModel.builtin, Ssz.builtin, iterSource, toSeq, hova]
  rw [show k + state.validators.length + 24 = k + state.validators.length + 3 + 20 + 1 by omega]
  rw [Readable.process_effective_balance_updates, ← pebLoopN_eq _ 0 state hvlen]
  revert hfor
  generalize pebLoopN vrefs.length 0 state = R
  generalize execFor _ _ _ _ _ _ _ _ = E
  intro hfor
  rcases E with e | ⟨o, L', h'⟩ <;> rcases R with e' | s'
  · simp only [LoopOut] at hfor; simp [ResultMatches, hfor]
  · simp only [LoopOut] at hfor
  · cases o <;> simp only [LoopOut] at hfor
  · cases o <;> simp only [LoopOut] at hfor
    · obtain ⟨hc, ⟨j, s, ⟨-, hd', -, -, hrest⟩, -, rfl⟩ | hb⟩ := hfor
      · simp only [Except.bind_ok', ResultMatches, PebExpect]
        exact ⟨⟨trivial, hd', hrest⟩, hc.frame, hc.fresh, hc.paths⟩
      · exact hb.elim
    · exact hfor.2.elim

end SpecLean.Validation
