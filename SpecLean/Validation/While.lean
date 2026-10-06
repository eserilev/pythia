import SpecLean.Validation.Loop

/-!
# Generic `while` loops (SPEC 9.3)

The translator emits a `while` loop as `f.loopN c`: the condition (`return` the carried locals
when it is false), then the body, which ends in `if μ c' < μ c then f.loopN c' else throw .bug`.
`μ` is the measure from `tools/while_measures.txt`. Unfold the definition once and replace the
recursive call by a continuation `K`: that is `B K c`.

One iteration is the condition and the body, related to `B K s` for every `K` (`IterK`). A false
condition ends the iteration as a `break` does. A normal end must also lower the measure, as the
readable loop checks.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Encode

/-- One iteration of `execWhile`: the condition, then the body. A false condition gives `brk`,
so that it ends the loop. -/
def whileIter (env : Env) (m : Nat) (L : Locals) (h : Heap) (c : Expr) (body : List Stmt) :
    Res (Outcome × Locals × Heap) := do
  let (cv, h1) ← evalExpr env m L h c
  if ← truthyH h1 cv then execBlock env m L h1 body else pure (.brk, L, h1)

theorem execWhile_step (env : Env) (m : Nat) (L : Locals) (h : Heap) (c : Expr)
    (body : List Stmt) :
    execWhile env (m + 1) L h c body = (whileIter env m L h c body >>= fun r => match r with
      | (.brk, L2, h2) => pure (.normal, L2, h2)
      | (.ret v, L2, h2) => pure (.ret v, L2, h2)
      | (_, L2, h2) => execWhile env m L2 h2 c body) := by
  rw [execWhile]
  unfold whileIter
  rcases evalExpr env m L h c with e | ⟨cv, h1⟩
  · rfl
  · simp only [Except.bind_ok']
    rcases truthyH h1 cv with e | b
    · rfl
    · cases b
      · rfl
      · simp only [Except.bind_ok', ↓reduceIte]
        rcases execBlock env m L h1 body with e | ⟨o, L2, h2⟩
        · rfl
        · cases o <;> rfl

/-- The generic `while` loop. Fuel `n + Kf + 1` with `μ s ≤ n` is enough. -/
theorem while_sim {σ ρ : Type} (env : Env) (c : Expr) (body : List Stmt) (Kf : Nat)
    (μ : σ → Nat) (B : (σ → Except Fail ρ) → σ → Except Fail ρ) (loop : σ → Except Fail ρ)
    (hloop : ∀ s, loop s = B (fun s' => if μ s' < μ s then loop s' else throw .bug) s)
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (P : σ → Locals → Heap → Prop) (Pbrk : ρ → Locals → Heap → Prop)
    (Pret : Value → ρ → Locals → Heap → Prop)
    (hstep : ∀ n s L h, P s L h → ∀ K,
      IterK (Contract gfp fpf vs h) (fun s' L' h' => P s' L' h' ∧ μ s' < μ s) Pbrk Pret K
        (whileIter env (n + Kf) L h c body) (B K s)) :
    ∀ n s L h, P s L h → Contract gfp fpf vs h0 h → μ s ≤ n →
      LoopOut (fun r L h => Contract gfp fpf vs h0 h ∧ Pbrk r L h)
        (fun v r L h => Contract gfp fpf vs h0 h ∧ Pret v r L h)
        (execWhile env (n + Kf + 1) L h c body) (loop s) := by
  intro n
  induction n with
  | zero =>
    intro s L h hp hc hμ
    have hK := hstep 0 s L h hp (fun s' => if μ s' < μ s then loop s' else throw .bug)
    rw [execWhile_step, hloop]
    revert hK
    generalize whileIter env (0 + Kf) L h c body = R
    intro hK
    rcases R with e | ⟨o, L2, h2⟩
    · obtain ⟨he, hB⟩ := hK
      rw [hB]
      exact ⟨he, rfl⟩
    · cases o with
      | normal | cont =>
        obtain ⟨-, s', -, -, hlt⟩ := hK
        omega
      | brk =>
        obtain ⟨hc', r, hB, hb⟩ := hK
        rw [hB]
        exact ⟨hc.trans hsub hwf hc', hb⟩
      | ret v =>
        obtain ⟨hc', r, hB, hr⟩ := hK
        rw [hB]
        exact ⟨hc.trans hsub hwf hc', hr⟩
  | succ n ih =>
    intro s L h hp hc hμ
    have hK := hstep (n + 1) s L h hp (fun s' => if μ s' < μ s then loop s' else throw .bug)
    rw [execWhile_step, hloop]
    revert hK
    generalize whileIter env (n + 1 + Kf) L h c body = R
    intro hK
    rcases R with e | ⟨o, L2, h2⟩
    · obtain ⟨he, hB⟩ := hK
      rw [hB]
      exact ⟨he, rfl⟩
    · cases o with
      | normal | cont =>
        obtain ⟨hc', s', hB, hp', hlt⟩ := hK
        rw [hB]
        simp only [Except.bind_ok', if_pos hlt]
        rw [show n + 1 + Kf = n + Kf + 1 by omega]
        exact ih s' L2 h2 hp' (hc.trans hsub hwf hc') (by omega)
      | brk =>
        obtain ⟨hc', r, hB, hb⟩ := hK
        rw [hB]
        exact ⟨hc.trans hsub hwf hc', hb⟩
      | ret v =>
        obtain ⟨hc', r, hB, hr⟩ := hK
        rw [hB]
        exact ⟨hc.trans hsub hwf hc', hr⟩

end SpecLean.Validation
