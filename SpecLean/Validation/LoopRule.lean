import SpecLean.Validation.Loop
import SpecLean.Paths

/-!
# The loop rule of the tactic (SPEC 9.3)

The generator states one theorem for each loop through `for_rule`. The invariant `Inv` does not
depend on the index. The theorem gives `LoopEnd`: the contract from the heap at loop entry, and
the invariant at the end. A loop that writes the heap and a loop that keeps it use the same rule.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Encode

theorem RootsKept_refl (h : Heap) (vs : List Value) : RootsKept h h vs := fun _ _ e => e

theorem RootsKept_trans {h1 h2 h3 : Heap} {vs : List Value} (a : RootsKept h1 h2 vs)
    (b : RootsKept h2 h3 vs) : RootsKept h1 h3 vs :=
  fun k ty e => a k ty (b k ty e)

/-- A write that keeps the shape of the object keeps the classes of the roots. -/
theorem RootsKept_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') (vs : List Value) : RootsKept h (h.set a o') vs :=
  fun k ty e => (rootTy_skel ho hs vs k ty).mp e

/-- An error of the same class ends an iteration, in the form of `ResultMatches`. -/
theorem iterK_error {σ ρ : Type} {C : Heap → Prop} {Pn : σ → Locals → Heap → Prop}
    {Pb : ρ → Locals → Heap → Prop} {Pr : Value → ρ → Locals → Heap → Prop}
    {K : σ → Except Fail ρ} {e : SpecError} {f : Fail} (h : e ≠ .outOfFuel ∧ e.fail = f) :
    IterK C Pn Pb Pr K (.error e) (.error f) :=
  ⟨h.1, by rw [h.2]⟩

/-- A normal end of an iteration: the contract, and the invariant of the next state. -/
theorem iterK_normal {σ ρ : Type} {C : Heap → Prop} {Pn : σ → Locals → Heap → Prop}
    {Pb : ρ → Locals → Heap → Prop} {Pr : Value → ρ → Locals → Heap → Prop}
    {K : σ → Except Fail ρ} {L : Locals} {h : Heap} {s : σ} (hc : C h) (hp : Pn s L h) :
    IterK C Pn Pb Pr K (.ok (.normal, L, h)) (K s) :=
  ⟨hc, s, rfl, hp⟩

/-- The end of a loop that has no `break` and no `return`: `Q` of the readable result, or an
error of the same class. -/
def LoopEnd {ρ : Type} (Q : ρ → Locals → Heap → Prop) :
    Res (Outcome × Locals × Heap) → Except Fail ρ → Prop
  | .ok (.normal, L, h), .ok r => Q r L h
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

/-- The loop rule: `for_sim` with an invariant that does not depend on the index, and a loop
with no `break` and no `return`. -/
theorem for_rule {σ : Type} (env : Env) (t : Target) (body : List Stmt) (src : IterSrc)
    (Kf N : Nat) (B : (σ → Except Fail σ) → σ → Nat → Except Fail σ)
    (loop : Nat → σ → Except Fail σ)
    (hloop : ∀ i s, loop i s = if i < N then B (loop (i + 1)) s i else pure s)
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (Inv : σ → Locals → Heap → Prop)
    (hitem : ∀ i s L h, Inv s L h → i < N → ∃ x, iterItem h src i = .ok (some x))
    (hend : ∀ i s L h, Inv s L h → N ≤ i → iterItem h src i = .ok none)
    (hstep : ∀ n i s L h x, Inv s L h → i < N → iterItem h src i = .ok (some x) → ∀ K,
      IterK (Contract gfp fpf vs h) Inv (fun _ _ _ => False) (fun _ _ _ _ => False) K (do
        let (L1, h1) ← assignTarget env (n + Kf) L h t x
        execBlock env (n + Kf) L1 h1 body) (B K s i))
    (n : Nat) (hn : N ≤ n) (s : σ) (L : Locals) (hi : Inv s L h0) :
    LoopEnd (fun r L h => Frame h0 h vs fpf ∧ Fresh h0 h ∧ NoNewPaths h0 h vs gfp ∧
        RootsKept h0 h vs ∧ Inv r L h)
      (execFor env (n + Kf + 1) L h0 t src 0 body) (loop 0 s) := by
  have := for_sim env t body src Kf N B id loop hloop hsub hwf (fun _ => Inv)
    (fun _ _ _ => False) (fun _ _ _ _ => False) hitem hend hstep n 0 s L h0 hi
    (Contract.refl _ _ _ h0) (by omega)
  revert this
  generalize execFor env (n + Kf + 1) L h0 t src 0 body = E
  generalize loop 0 s = R
  intro this
  rcases E with e | ⟨o, L', h'⟩ <;> rcases R with f | r
  · exact this
  · exact this
  · cases o <;> exact this
  · cases o <;> simp only [LoopOut] at this
    · obtain ⟨hc, ⟨j, s', hp, -, rfl⟩ | hb⟩ := this
      · exact ⟨hc.frame, hc.fresh, hc.paths, hc.roots, hp⟩
      · exact hb.elim
    · exact this.2.elim

/-- `for x in lst`, where `lst` is the list at `a` at loop entry, and the body keeps its length. -/
theorem for_live_rule {σ : Type} (env : Env) (t : Target) (body : List Stmt) (a : Nat)
    (Kf N : Nat) (B : (σ → Except Fail σ) → σ → Nat → Except Fail σ)
    (loop : Nat → σ → Except Fail σ)
    (hloop : ∀ i s, loop i s = if i < N then B (loop (i + 1)) s i else pure s)
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (Inv : σ → Locals → Heap → Prop)
    (hlen : ∀ s L h, Inv s L h → ListLen h a N)
    (hstep : ∀ n i s L h x, Inv s L h → i < N → seqItem h (.live a) i = .ok (some x) → ∀ K,
      IterK (Contract gfp fpf vs h) Inv (fun _ _ _ => False) (fun _ _ _ _ => False) K (do
        let (L1, h1) ← assignTarget env (n + Kf) L h t x
        execBlock env (n + Kf) L1 h1 body) (B K s i))
    (n : Nat) (hn : N ≤ n) (s : σ) (L : Locals) (hi : Inv s L h0) :
    LoopEnd (fun r L h => Frame h0 h vs fpf ∧ Fresh h0 h ∧ NoNewPaths h0 h vs gfp ∧
        RootsKept h0 h vs ∧ Inv r L h)
      (execFor env (n + Kf + 1) L h0 t (.seq (.live a)) 0 body) (loop 0 s) :=
  for_rule env t body (.seq (.live a)) Kf N B loop hloop hsub hwf Inv
    (fun _ s L h hp hi => seqItem_live_some (hlen s L h hp) hi)
    (fun _ s L h hp hi => seqItem_live_none (hlen s L h hp) hi)
    hstep n hn s L hi

/-- `for i, x in enumerate(lst)`. -/
theorem for_enum_rule {σ : Type} (env : Env) (t : Target) (body : List Stmt) (a : Nat)
    (Kf N : Nat) (B : (σ → Except Fail σ) → σ → Nat → Except Fail σ)
    (loop : Nat → σ → Except Fail σ)
    (hloop : ∀ i s, loop i s = if i < N then B (loop (i + 1)) s i else pure s)
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (Inv : σ → Locals → Heap → Prop)
    (hlen : ∀ s L h, Inv s L h → ListLen h a N)
    (hstep : ∀ n i s L h x, Inv s L h → i < N → seqItem h (.live a) i = .ok (some x) → ∀ K,
      IterK (Contract gfp fpf vs h) Inv (fun _ _ _ => False) (fun _ _ _ _ => False) K (do
        let (L1, h1) ← assignTarget env (n + Kf) L h t (enumItem i x)
        execBlock env (n + Kf) L1 h1 body) (B K s i))
    (n : Nat) (hn : N ≤ n) (s : σ) (L : Locals) (hi : Inv s L h0) :
    LoopEnd (fun r L h => Frame h0 h vs fpf ∧ Fresh h0 h ∧ NoNewPaths h0 h vs gfp ∧
        RootsKept h0 h vs ∧ Inv r L h)
      (execFor env (n + Kf + 1) L h0 t (.enum (.live a)) 0 body) (loop 0 s) :=
  for_rule env t body (.enum (.live a)) Kf N B loop hloop hsub hwf Inv
    (fun i s L h hp hi => by
      obtain ⟨x, hx⟩ := seqItem_live_some (hlen s L h hp) hi
      exact ⟨enumItem i x, by simp [iterItem, hx]⟩)
    (fun i s L h hp hi => by simp [iterItem, seqItem_live_none (hlen s L h hp) hi])
    (fun n i s L h x hp hi hx => by
      obtain ⟨y, hy⟩ := seqItem_live_some (hlen s L h hp) hi
      have : x = enumItem i y := by simp [iterItem, hy] at hx; exact hx.symm
      subst this
      exact hstep n i s L h y hp hi hy)
    n hn s L hi

end SpecLean.Validation
