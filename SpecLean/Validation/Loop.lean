import SpecLean.Lemmas
import SpecLean.Compose

/-!
# Generic `for` loops (SPEC 9.3)

The translator emits each `for` loop as `f.loopN n i c`: if `i < n`, the body, which ends in
`f.loopN n (i + 1) c'`, else the carried locals. `n` is the length at loop entry. Unfold the
definition once and replace the recursive call by a continuation `K`: that is the body `B K c i`.

The interpreter loop is `execFor` over the reference that the loop takes at entry. It reads the
length at each step. So the lemmas need the body to keep the length (`ListLen`).

One iteration is related to `B K s i` for every `K`, so the proof of one iteration never sees
the rest of the loop. A step ends in one of four ways:

- normal or `continue`: `B K s i = K s'` with the invariant at `i + 1`;
- `break`: `B K s i` is a result;
- `return v`: `B K s i` is a result;
- an error of the same class.

Each step also proves the contract of SPEC 9.2 from the heap at its start (`Contract`). The
lemma chains the steps, so the loop gets the contract from the heap at loop entry.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Encode

/-! ## The contract of a run -/

/-- The contract of a run from `h` to `h'` (SPEC 9.2): the frame of `fpf`, fresh addresses, no
new paths over the global footprint `gfp`, and roots that keep their class. -/
structure Contract (gfp fpf : Footprint) (vs : List Value) (h h' : Heap) : Prop where
  frame : Frame h h' vs fpf
  fresh : Fresh h h'
  paths : NoNewPaths h h' vs gfp
  roots : RootsKept h h' vs

theorem Contract.refl (gfp fpf : Footprint) (vs : List Value) (h : Heap) :
    Contract gfp fpf vs h h :=
  ⟨Frame_refl h vs fpf, Fresh_refl h, NoNewPaths_refl h vs gfp, fun _ _ e => e⟩

/-- An old object at an `fpf` path after a run was at an `fpf` path before it. -/
theorem atFp_back {h1 h2 : Heap} {vs : List Value} {gfp fpf : Footprint}
    (hsub : ∀ p ∈ fpf, p ∈ gfp) (hwf : HeapWF h1) (hn : NoNewPaths h1 h2 vs gfp)
    (hr : RootsKept h1 h2 vs) {a : Nat} (ha : h1.objs a ≠ none) (hat : AtFp h2 vs fpf a) :
    AtFp h1 vs fpf a := by
  obtain ⟨k, pat, q, hpat, hty, hm, e⟩ := hat
  have hlt : a < h1.next := Nat.lt_of_not_le fun hle => ha (hwf a hle)
  obtain ⟨φ, hφ⟩ := hn
  obtain ⟨e1, hpres, -⟩ := hφ k q a e hlt ⟨k, pat, hsub pat hpat, q, hm, e⟩
  exact ⟨k, pat, φ k q, hpat, hr k pat.ty hty, hpres pat (hsub pat hpat) hm, e1⟩

/-- Two runs in a row. The footprint is a part of the global footprint. -/
theorem Contract.trans {gfp fpf : Footprint} {vs : List Value} {h1 h2 h3 : Heap}
    (hsub : ∀ p ∈ fpf, p ∈ gfp) (hwf : HeapWF h1) (a : Contract gfp fpf vs h1 h2)
    (b : Contract gfp fpf vs h2 h3) : Contract gfp fpf vs h1 h3 where
  frame := by
    intro x hx hn
    have e12 := a.frame x hx hn
    rw [b.frame x (by rw [e12]; exact hx)
      (fun h2x => hn (atFp_back hsub hwf a.paths a.roots hx h2x)), e12]
  fresh := Fresh_trans a.fresh b.fresh
  paths := NoNewPaths_trans a.fresh a.paths b.paths
  roots := fun k ty e => a.roots k ty (b.roots k ty e)

/-! ## One iteration and the whole loop -/

/-- One iteration of the interpreter against the readable body `r = B K s i`, for a fixed
continuation `K`. `C h'` is the contract from the heap at the start of the iteration. -/
def IterK {σ ρ : Type} (C : Heap → Prop) (Pnext : σ → Locals → Heap → Prop)
    (Pbrk : ρ → Locals → Heap → Prop) (Pret : Value → ρ → Locals → Heap → Prop)
    (K : σ → Except Fail ρ) : Res (Outcome × Locals × Heap) → Except Fail ρ → Prop
  | .ok (.normal, L', h'), r | .ok (.cont, L', h'), r => C h' ∧ ∃ s', r = K s' ∧ Pnext s' L' h'
  | .ok (.brk, L', h'), r => C h' ∧ ∃ x, r = .ok x ∧ Pbrk x L' h'
  | .ok (.ret v, L', h'), r => C h' ∧ ∃ x, r = .ok x ∧ Pret v x L' h'
  | .error e, r => e ≠ .outOfFuel ∧ r = .error e.fail

/-- The result of a whole loop: a normal end, a `return`, or an error of the same class. -/
def LoopOut {ρ : Type} (Pend : ρ → Locals → Heap → Prop) (Pret : Value → ρ → Locals → Heap → Prop) :
    Res (Outcome × Locals × Heap) → Except Fail ρ → Prop
  | .ok (.normal, L, h), .ok r => Pend r L h
  | .ok (.ret v, L, h), .ok r => Pret v r L h
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

/-- A step proved as a `StepRel` against a readable step `r` gives `IterK` for the body
`r >>= K`. A body that ends only normally or with an error has this form. -/
theorem iterK_of_stepRel {σ ρ : Type} {C : Heap → Prop} {R Pn : σ → Locals → Heap → Prop}
    {Pb : ρ → Locals → Heap → Prop} {Pr : Value → ρ → Locals → Heap → Prop}
    {K : σ → Except Fail ρ} {run : Res (Outcome × Locals × Heap)} {r : Except Fail σ}
    (hs : StepRel R run r) (hR : ∀ s L h, R s L h → C h ∧ Pn s L h) :
    IterK C Pn Pb Pr K run (r >>= K) := by
  rcases run with e | ⟨o, L, h⟩ <;> rcases r with f | s
  · obtain ⟨he, hf⟩ := hs
    exact ⟨he, by rw [hf]; rfl⟩
  · simp [StepRel] at hs
  · cases o <;> simp [StepRel] at hs
  · cases o <;> simp only [StepRel] at hs
    obtain ⟨hc, hp⟩ := hR s L h hs
    exact ⟨hc, s, by simp, hp⟩

/-- One iteration of `execFor`: the target, the body, then the outcome. -/
theorem execFor_step (env : Env) (m : Nat) (L : Locals) (h : Heap) (t : Target) (src : IterSrc)
    (i : Nat) (body : List Stmt) {x : Value} (hx : iterItem h src i = .ok (some x)) :
    execFor env (m + 1) L h t src i body = ((do
      let (L1, h1) ← assignTarget env m L h t x
      execBlock env m L1 h1 body) >>= fun r => match r with
        | (.brk, L2, h2) => pure (.normal, L2, h2)
        | (.ret v, L2, h2) => pure (.ret v, L2, h2)
        | (_, L2, h2) => execFor env m L2 h2 t src (i + 1) body) := by
  rw [execFor, hx]
  simp only [Except.bind_ok']
  rcases assignTarget env m L h t x with e | ⟨L1, h1⟩
  · rfl
  · simp only [Except.bind_ok']
    rcases execBlock env m L1 h1 body with e | ⟨o, L2, h2⟩
    · rfl
    · cases o <;> rfl

/-- The generic `for` loop. `hitem` and `hend` say where the items end, `hstep` relates one
iteration to the readable body. Fuel `n + Kf + 1` with `N - i ≤ n` is enough. -/
theorem for_sim {σ ρ : Type} (env : Env) (t : Target) (body : List Stmt) (src : IterSrc)
    (Kf N : Nat) (B : (σ → Except Fail ρ) → σ → Nat → Except Fail ρ) (fin : σ → ρ)
    (loop : Nat → σ → Except Fail ρ)
    (hloop : ∀ i s, loop i s = if i < N then B (loop (i + 1)) s i else pure (fin s))
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (P : Nat → σ → Locals → Heap → Prop) (Pbrk : ρ → Locals → Heap → Prop)
    (Pret : Value → ρ → Locals → Heap → Prop)
    (hitem : ∀ i s L h, P i s L h → i < N → ∃ x, iterItem h src i = .ok (some x))
    (hend : ∀ i s L h, P i s L h → N ≤ i → iterItem h src i = .ok none)
    (hstep : ∀ n i s L h x, P i s L h → i < N → iterItem h src i = .ok (some x) → ∀ K,
      IterK (Contract gfp fpf vs h) (P (i + 1)) Pbrk Pret K (do
        let (L1, h1) ← assignTarget env (n + Kf) L h t x
        execBlock env (n + Kf) L1 h1 body) (B K s i)) :
    ∀ n i s L h, P i s L h → Contract gfp fpf vs h0 h → N - i ≤ n →
      LoopOut (fun r L h => Contract gfp fpf vs h0 h ∧
          ((∃ j s, P j s L h ∧ N ≤ j ∧ r = fin s) ∨ Pbrk r L h))
        (fun v r L h => Contract gfp fpf vs h0 h ∧ Pret v r L h)
        (execFor env (n + Kf + 1) L h t src i body) (loop i s) := by
  intro n
  induction n with
  | zero =>
    intro i s L h hp hc hn
    have hi : N ≤ i := by omega
    rw [execFor, hend i s L h hp hi, hloop, if_neg (by omega)]
    exact ⟨hc, .inl ⟨i, s, hp, hi, rfl⟩⟩
  | succ n ih =>
    intro i s L h hp hc hn
    by_cases hi : i < N
    · obtain ⟨x, hx⟩ := hitem i s L h hp hi
      have hK := hstep (n + 1) i s L h x hp hi hx (loop (i + 1))
      rw [execFor_step env (n + 1 + Kf) L h t src i body hx, hloop, if_pos hi]
      revert hK
      generalize (do
        let (L1, h1) ← assignTarget env (n + 1 + Kf) L h t x
        execBlock env (n + 1 + Kf) L1 h1 body) = R
      intro hK
      rcases R with e | ⟨o, L2, h2⟩
      · obtain ⟨he, hB⟩ := hK
        rw [hB]
        exact ⟨he, rfl⟩
      · cases o with
        | normal | cont =>
          obtain ⟨hc', s', hB, hp'⟩ := hK
          rw [hB]
          simp only [Except.bind_ok']
          rw [show n + 1 + Kf = n + Kf + 1 by omega]
          exact ih (i + 1) s' L2 h2 hp' (hc.trans hsub hwf hc') (by omega)
        | brk =>
          obtain ⟨hc', r, hB, hb⟩ := hK
          rw [hB]
          exact ⟨hc.trans hsub hwf hc', .inr hb⟩
        | ret v =>
          obtain ⟨hc', r, hB, hr⟩ := hK
          rw [hB]
          exact ⟨hc.trans hsub hwf hc', hr⟩
    · rw [execFor, hend i s L h hp (by omega), hloop, if_neg hi]
      exact ⟨hc, .inl ⟨i, s, hp, by omega, rfl⟩⟩

/-! ## Live lists: the body keeps the length -/

/-- The object at `a` is a list of length `N`. -/
def ListLen (h : Heap) (a N : Nat) : Prop :=
  ∃ k e l xs, h.objs a = some (.list k e l xs) ∧ xs.length = N

/-- An item of a list that is not a byte list is its element. -/
theorem seqItem_live_eq {h : Heap} {a i : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} (ho : h.objs a = some (.list k e l xs))
    (hb : ¬(k = .list ∧ e = .uint (.width 8))) : seqItem h (.live a) i = .ok xs[i]? := by
  simp only [seqItem, ho]
  split
  · rename_i he; cases he; exact absurd ⟨rfl, rfl⟩ hb
  · rename_i he; cases he; rfl
  · exact (‹∀ (kind : ListKind) (elem : SszTy) (limit : Option Nat) (ys : List Value),
      some (HeapObj.list k e l xs) = some (HeapObj.list kind elem limit ys) → False›
      k e l xs rfl).elim

/-- An item of a byte list is its element as an `int`. -/
theorem seqItem_live_bytes {h : Heap} {a i : Nat} {l : Option Nat} {xs : List Value}
    (ho : h.objs a = some (.list .list (.uint (.width 8)) l xs)) :
    seqItem h (.live a) i = .ok (xs[i]?.map byteInt) := by
  simp only [seqItem, ho]

theorem seqItem_live_none {h : Heap} {a N i : Nat} (hl : ListLen h a N) (hi : N ≤ i) :
    seqItem h (.live a) i = .ok none := by
  obtain ⟨k, e, l, xs, ho, rfl⟩ := hl
  have hx : xs[i]? = none := List.getElem?_eq_none_iff.mpr hi
  by_cases hb : k = .list ∧ e = .uint (.width 8)
  · obtain ⟨rfl, rfl⟩ := hb; rw [seqItem_live_bytes ho, hx]; rfl
  · rw [seqItem_live_eq ho hb, hx]

theorem seqItem_live_some {h : Heap} {a N i : Nat} (hl : ListLen h a N) (hi : i < N) :
    ∃ x, seqItem h (.live a) i = .ok (some x) := by
  obtain ⟨k, e, l, xs, ho, rfl⟩ := hl
  have hx : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
  by_cases hb : k = .list ∧ e = .uint (.width 8)
  · obtain ⟨rfl, rfl⟩ := hb; rw [seqItem_live_bytes ho, hx]; exact ⟨_, rfl⟩
  · rw [seqItem_live_eq ho hb, hx]; exact ⟨_, rfl⟩

/-- `for x in lst`, where `lst` is the list at `a` at loop entry. -/
theorem for_live_sim {σ ρ : Type} (env : Env) (t : Target) (body : List Stmt) (a : Nat)
    (Kf N : Nat) (B : (σ → Except Fail ρ) → σ → Nat → Except Fail ρ) (fin : σ → ρ)
    (loop : Nat → σ → Except Fail ρ)
    (hloop : ∀ i s, loop i s = if i < N then B (loop (i + 1)) s i else pure (fin s))
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (P : Nat → σ → Locals → Heap → Prop) (Pbrk : ρ → Locals → Heap → Prop)
    (Pret : Value → ρ → Locals → Heap → Prop)
    (hlen : ∀ i s L h, P i s L h → ListLen h a N)
    (hstep : ∀ n i s L h x, P i s L h → i < N → seqItem h (.live a) i = .ok (some x) → ∀ K,
      IterK (Contract gfp fpf vs h) (P (i + 1)) Pbrk Pret K (do
        let (L1, h1) ← assignTarget env (n + Kf) L h t x
        execBlock env (n + Kf) L1 h1 body) (B K s i)) :
    ∀ n i s L h, P i s L h → Contract gfp fpf vs h0 h → N - i ≤ n →
      LoopOut (fun r L h => Contract gfp fpf vs h0 h ∧
          ((∃ j s, P j s L h ∧ N ≤ j ∧ r = fin s) ∨ Pbrk r L h))
        (fun v r L h => Contract gfp fpf vs h0 h ∧ Pret v r L h)
        (execFor env (n + Kf + 1) L h t (.seq (.live a)) i body) (loop i s) :=
  for_sim env t body (.seq (.live a)) Kf N B fin loop hloop hsub hwf P Pbrk Pret
    (fun i s L h hp hi => seqItem_live_some (hlen i s L h hp) hi)
    (fun i s L h hp hi => seqItem_live_none (hlen i s L h hp) hi)
    (fun n i s L h x hp hi hx => hstep n i s L h x hp hi hx)

/-- `for i, x in enumerate(lst)`. The target gets `(i, x)`. -/
theorem for_enum_sim {σ ρ : Type} (env : Env) (t : Target) (body : List Stmt) (a : Nat)
    (Kf N : Nat) (B : (σ → Except Fail ρ) → σ → Nat → Except Fail ρ) (fin : σ → ρ)
    (loop : Nat → σ → Except Fail ρ)
    (hloop : ∀ i s, loop i s = if i < N then B (loop (i + 1)) s i else pure (fin s))
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (P : Nat → σ → Locals → Heap → Prop) (Pbrk : ρ → Locals → Heap → Prop)
    (Pret : Value → ρ → Locals → Heap → Prop)
    (hlen : ∀ i s L h, P i s L h → ListLen h a N)
    (hstep : ∀ n i s L h x, P i s L h → i < N → seqItem h (.live a) i = .ok (some x) → ∀ K,
      IterK (Contract gfp fpf vs h) (P (i + 1)) Pbrk Pret K (do
        let (L1, h1) ← assignTarget env (n + Kf) L h t (enumItem i x)
        execBlock env (n + Kf) L1 h1 body) (B K s i)) :
    ∀ n i s L h, P i s L h → Contract gfp fpf vs h0 h → N - i ≤ n →
      LoopOut (fun r L h => Contract gfp fpf vs h0 h ∧
          ((∃ j s, P j s L h ∧ N ≤ j ∧ r = fin s) ∨ Pbrk r L h))
        (fun v r L h => Contract gfp fpf vs h0 h ∧ Pret v r L h)
        (execFor env (n + Kf + 1) L h t (.enum (.live a)) i body) (loop i s) :=
  for_sim env t body (.enum (.live a)) Kf N B fin loop hloop hsub hwf P Pbrk Pret
    (fun i s L h hp hi => by
      obtain ⟨x, hx⟩ := seqItem_live_some (hlen i s L h hp) hi
      exact ⟨enumItem i x, by simp [iterItem, hx]⟩)
    (fun i s L h hp hi => by simp [iterItem, seqItem_live_none (hlen i s L h hp) hi])
    (fun n i s L h x hp hi hx => by
      obtain ⟨y, hy⟩ := seqItem_live_some (hlen i s L h hp) hi
      have : x = enumItem i y := by simp [iterItem, hy] at hx; exact hx.symm
      subst this
      exact hstep n i s L h y hp hi hy)

/-- The items of `zip` over live lists of length `N`, as one result. -/
theorem zip_items {h : Heap} {N i : Nat} :
    ∀ (as : List Nat), (∀ a ∈ as, ListLen h a N) →
      ∃ items : List (Option Value), (as.map Seq.live).mapM (seqItem h · i) = .ok items ∧
        items.length = as.length ∧
        (i < N → ∀ o ∈ items, o.isSome) ∧ (N ≤ i → ∀ o ∈ items, o = none)
  | [], _ => ⟨[], rfl, rfl, by simp, by simp⟩
  | a :: as, hl => by
    obtain ⟨items, hm, hlen, hs, hn⟩ := zip_items (i := i) as (fun b hb => hl b (by simp [hb]))
    by_cases hi : i < N
    · obtain ⟨x, hx⟩ := seqItem_live_some (hl a (by simp)) hi
      refine ⟨some x :: items, ?_, by simp [hlen], fun _ o ho => ?_, fun hn' => absurd hn' (by omega)⟩
      · simp only [List.map_cons, List.mapM_cons, hx, hm, Except.bind_ok', Except.pure_ok']
      · simp at ho; rcases ho with rfl | ho
        · rfl
        · exact hs hi o ho
    · have hx := seqItem_live_none (hl a (by simp)) (Nat.le_of_not_lt hi)
      refine ⟨none :: items, ?_, by simp [hlen], fun hi' => absurd hi' hi, fun hn' o ho => ?_⟩
      · simp only [List.map_cons, List.mapM_cons, hx, hm, Except.bind_ok', Except.pure_ok']
      · simp at ho; rcases ho with rfl | ho
        · rfl
        · exact hn hn' o ho

/-- `for x, y in zip(lst1, lst2, ...)` over lists that all keep the length `N`. -/
theorem for_zip_sim {σ ρ : Type} (env : Env) (t : Target) (body : List Stmt) (as : List Nat)
    (strict : Bool) (has : as ≠ [])
    (Kf N : Nat) (B : (σ → Except Fail ρ) → σ → Nat → Except Fail ρ) (fin : σ → ρ)
    (loop : Nat → σ → Except Fail ρ)
    (hloop : ∀ i s, loop i s = if i < N then B (loop (i + 1)) s i else pure (fin s))
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (P : Nat → σ → Locals → Heap → Prop) (Pbrk : ρ → Locals → Heap → Prop)
    (Pret : Value → ρ → Locals → Heap → Prop)
    (hlen : ∀ i s L h, P i s L h → ∀ a ∈ as, ListLen h a N)
    (hstep : ∀ n i s L h x, P i s L h → i < N →
      iterItem h (.zip (as.map Seq.live) strict) i = .ok (some x) → ∀ K,
      IterK (Contract gfp fpf vs h) (P (i + 1)) Pbrk Pret K (do
        let (L1, h1) ← assignTarget env (n + Kf) L h t x
        execBlock env (n + Kf) L1 h1 body) (B K s i)) :
    ∀ n i s L h, P i s L h → Contract gfp fpf vs h0 h → N - i ≤ n →
      LoopOut (fun r L h => Contract gfp fpf vs h0 h ∧
          ((∃ j s, P j s L h ∧ N ≤ j ∧ r = fin s) ∨ Pbrk r L h))
        (fun v r L h => Contract gfp fpf vs h0 h ∧ Pret v r L h)
        (execFor env (n + Kf + 1) L h t (.zip (as.map Seq.live) strict) i body) (loop i s) :=
  for_sim env t body _ Kf N B fin loop hloop hsub hwf P Pbrk Pret
    (fun i s L h hp hi => by
      obtain ⟨items, hm, -, hs, -⟩ := zip_items (i := i) as (hlen i s L h hp)
      exact ⟨_, by simp only [iterItem, hm, Except.bind_ok']; rw [if_pos (by simpa using hs hi)]; rfl⟩)
    (fun i s L h hp hi => by
      obtain ⟨items, hm, hl, -, hn⟩ := zip_items (i := i) as (hlen i s L h hp)
      have hne : items ≠ [] := by
        intro e; subst e; exact has (List.length_eq_zero_iff.mp hl.symm)
      have hall : items.all Option.isSome = false := by
        obtain ⟨o, os, rfl⟩ := List.exists_cons_of_ne_nil hne
        simp [hn hi o (by simp)]
      have hany : items.any Option.isSome = false := by
        simp only [List.any_eq_false]; intro o ho; simp [hn hi o ho]
      simp only [iterItem, hm, Except.bind_ok', hall, hany, Bool.and_false]
      rfl)
    hstep

end SpecLean.Validation
