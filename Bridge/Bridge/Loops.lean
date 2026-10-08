import Bridge.Tactic

/-!
# Generic loop lemmas

The readable Lean writes a Python `for` loop as a recursion `f.loopN … n i …` on an index `i`.
The hand spec writes it as a Lean `for` loop, that is `forIn items r B`. One lemma per shape
relates the two:

- `sim_loop`: the index loop against `forIn` with an invariant `Inv i c r` on the readable loop
  variables `c` and the hand accumulator `r`. The caller proves one loop step and the end.
  The epoch loops over the validators use it with these invariants:
  - one list field `F` of the state changes in place on both sides
    (`process_slashings`, `process_inactivity_updates`): `state = { st0 with F := X }` and
    `r = X.map conv`;
  - the hand loop builds a new list and the readable loop sets item `i`
    (`process_effective_balance_updates`): `state = { st0 with F := P ++ st0.F.drop i }` and
    `r = P.map conv`, with `P.length = i`.
- `sum_loop`: an index loop that adds the amounts of the items that pass a test.
- `forIn_append`: a hand `for` loop that appends to a list is a `filterMapM`, so it meets the
  readable comprehension (`sim_filterMapM_gen`).
-/

namespace Pythia.Bridge

open SpecLean SpecLean.Rd

/-! ## Arithmetic and monad steps used by the loop bodies -/

theorem u64add_eq (a b : Nat) : EpochProofs.Spec.uint64Add a b =
    if a + b < 2 ^ 64 then .ok (a + b) else .error .overflow := by
  unfold EpochProofs.Spec.uint64Add EpochProofs.Spec.UINT64_SIZE; split <;> rfl

theorem u64mul_eq (a b : Nat) : EpochProofs.Spec.uint64Mul a b =
    if a * b < 2 ^ 64 then .ok (a * b) else .error .overflow := by
  unfold EpochProofs.Spec.uint64Mul EpochProofs.Spec.UINT64_SIZE; split <;> rfl

theorem u64sub_le (a b : Nat) (h : b ≤ a) : EpochProofs.Spec.uint64Sub a b = .ok (a - b) := by
  unfold EpochProofs.Spec.uint64Sub; rw [if_pos h]; rfl

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

theorem uop_sub_ok {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) (hle : b ≤ a)
    (ha : a < 2 ^ 64) : (uOp .sub (a : Int) (b : Int) : SpecM α) = .ok (UintC.ofNat (a - b)) := by
  unfold uOp
  simp only [erase, intArith, mapError_ok, ok_bind]
  rw [show (a : Int) - (b : Int) = ((a - b : Nat) : Int) by omega, uOf_ok _ hb (by omega)]

/-- A readable `uOp .add` and the hand `uint64Add` of the same values: both give the sum, or
both overflow. -/
theorem sim_add_bind {α β β' : Type} [UintC α] (hb : UintC.bits α = 64) {g : β → β'} (a b : Nat)
    {K : α → SpecM β} {L : Nat → HM β'}
    (hK : a + b < 2 ^ 64 → Sim g (K (UintC.ofNat (a + b))) (L (a + b))) :
    Sim g ((uOp .add (a : Int) (b : Int) : SpecM α) >>= K) (EpochProofs.Spec.uint64Add a b >>= L) := by
  rw [uop_add_eq hb, u64add_eq]
  by_cases h : a + b < 2 ^ 64
  · rw [if_pos h, if_pos h, ok_bind, ok_bind]; exact hK h
  · rw [if_neg h, if_neg h, err_bind, err_bind]; rfl

/-- The same for `uOp .mul` and `uint64Mul`. -/
theorem sim_mul_bind {α β β' : Type} [UintC α] (hb : UintC.bits α = 64) {g : β → β'} (a b : Nat)
    {K : α → SpecM β} {L : Nat → HM β'}
    (hK : a * b < 2 ^ 64 → Sim g (K (UintC.ofNat (a * b))) (L (a * b))) :
    Sim g ((uOp .mul (a : Int) (b : Int) : SpecM α) >>= K) (EpochProofs.Spec.uint64Mul a b >>= L) := by
  rw [uop_mul_eq hb, u64mul_eq]
  by_cases h : a * b < 2 ^ 64
  · rw [if_pos h, if_pos h, ok_bind, ok_bind]; exact hK h
  · rw [if_neg h, if_neg h, err_bind, err_bind]; rfl

theorem pyMin2_ok {α : Type} [UintC α] [PyOrd α] (a b : α) :
    pyMin [a, b] = .ok (if PyOrd.lt b a = true then b else a) := rfl

/-- A readable result that the caller projects (`(l).2.2`). -/
theorem sim_bind_proj {α β γ : Type} {g : β → γ} {A : SpecM α} {k : α → β} {H : HM γ}
    (h : Sim (fun x => g (k x)) A H) : Sim g (A >>= fun x => pure (k x)) H := by
  unfold Sim at *
  cases A with
  | error e => exact h
  | ok a => exact h

/-- The hand result of a callee that cannot fail, read from its bridge statement. -/
theorem ok_of_sim {α β : Type} {f : α → β} {A : SpecM α} {B : HM β} {a : α}
    (hs : Sim f A B) (ha : A = .ok a) : B = .ok (f a) := by
  unfold Sim at hs; rw [ha] at hs
  cases B with
  | error e => cases hs
  | ok b => cases hs; rfl

/-! ## Lists -/

theorem zipIdx_map' {α β : Type} (f : α → β) (l : List α) (n : Nat) :
    (l.map f).zipIdx n = (l.zipIdx n).map (fun p => (f p.1, p.2)) := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih => simp [ih]

theorem getElem?_zipIdx_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
    ((l.map f).zipIdx)[i]? = some (f l[i], i) := by
  simp [hi]

theorem mapM_const_ok {α β : Type} (xs : List α) (b : β) :
    xs.mapM (fun _ => (Except.ok b : SpecM β)) = .ok (List.replicate xs.length b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.mapM_cons, ih]; rfl

/-- `range(n)` as a list of integers. -/
theorem pyRange_zero (n : Nat) :
    pyRange 0 (n : Int) 1 = .ok ((List.range n).map fun (i : Nat) => (i : Int)) := by
  unfold pyRange
  rw [if_neg (by decide)]
  simp; rfl

/-- The prefix `P` of new items, then the old items from index `i`. -/
theorem split_at {α : Type} (P l : List α) (i : Nat) (hi : i < l.length) :
    P ++ l.drop i = P ++ l[i] :: l.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi]

theorem lget_split {α : Type} (P l : List α) (i : Nat) (hP : P.length = i) (hi : i < l.length) :
    lget (P ++ l.drop i) (i : Int) = .ok l[i] := by
  rw [split_at P l i hi, lget_ok _ _ (by simp; omega)]
  congr 1
  rw [List.getElem_append_right (by omega)]
  simp [hP]

theorem lset_split {α : Type} (P l : List α) (i : Nat) (x : α) (hP : P.length = i)
    (hi : i < l.length) : lset (P ++ l.drop i) (i : Int) x = .ok ((P ++ [x]) ++ l.drop (i + 1)) := by
  rw [split_at P l i hi, lset_ok _ _ _ (by simp; omega), List.set_append_right _ _ (by omega)]
  simp [hP]
  rw [List.drop_eq_getElem_cons hi]; rfl

/-! ## The index loop against `forIn` -/

/-- What the hand loop does after one step: stop with `K`, or go on with `k`. -/
def loopNext {R β : Type} (K : R → HM β) (k : R → HM β) : ForInStep R → HM β
  | .done r => K r
  | .yield r => k r

theorem forIn_cons_bind {γ R β : Type} (x : γ) (xs : List γ) (r : R)
    (B : γ → R → HM (ForInStep R)) (K : R → HM β) :
    (forIn (x :: xs) r B >>= K) = (B x r >>= loopNext K fun r' => forIn xs r' B >>= K) := by
  rw [List.forIn_cons]
  cases B x r with
  | error e => rfl
  | ok s => cases s <;> rfl

/-- The readable index loop `L i c` against the hand loop `forIn (items.drop i) r B`, then `K`.
`Inv i c r` relates the readable loop variables `c` and the hand accumulator `r` before step
`i`. `hstep` is one step: it may use the claim for step `i + 1` (`ih`). `hend` is the end of
the loop. -/
theorem sim_loop {C R O β γ : Type} {g : O → β} (n : Nat) (items : List γ) (hn : items.length = n)
    (L : Nat → C → SpecM O) (B : γ → R → HM (ForInStep R)) (K : R → HM β)
    (Inv : Nat → C → R → Prop)
    (hstep : ∀ i x c r, i < n → items[i]? = some x → Inv i c r →
      (∀ c' r', Inv (i + 1) c' r' → Sim g (L (i + 1) c') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i c) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ c r, Inv n c r → Sim g (L n c) (K r))
    (i : Nat) (hi : i ≤ n) (c : C) (r : R) (h : Inv i c r) :
    Sim g (L i c) (forIn (items.drop i) r B >>= K) := by
  by_cases hlt : i < n
  · have hx : items[i]? = some items[i] := List.getElem?_eq_getElem (by omega)
    rw [List.drop_eq_getElem_cons (by omega), forIn_cons_bind]
    exact hstep i _ c r hlt hx h fun c' r' h' =>
      sim_loop n items hn L B K Inv hstep hend (i + 1) hlt c' r' h'
  · have hi' : i = n := by omega
    subst hi'
    rw [List.drop_eq_nil_of_le (by omega)]
    exact hend c r h
termination_by n - i

/-- `sim_loop` from the start, for a loop over all items. -/
theorem sim_loop0 {C R O β γ : Type} {g : O → β} (n : Nat) (items : List γ) (hn : items.length = n)
    (L : Nat → C → SpecM O) (B : γ → R → HM (ForInStep R)) (K : R → HM β)
    (Inv : Nat → C → R → Prop)
    (hstep : ∀ i x c r, i < n → items[i]? = some x → Inv i c r →
      (∀ c' r', Inv (i + 1) c' r' → Sim g (L (i + 1) c') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i c) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ c r, Inv n c r → Sim g (L n c) (K r))
    (c : C) (r : R) (h : Inv 0 c r) : Sim g (L 0 c) (forIn items r B >>= K) := by
  have := sim_loop n items hn L B K Inv hstep hend 0 (Nat.zero_le _) c r h
  rwa [List.drop_zero] at this

/-- `sim_loop0` for a readable loop with 1 loop variable. -/
theorem sim_loopv1 {V1 R O β γ : Type} {g : O → β} (n : Nat) (items : List γ)
    (hn : items.length = n) (L : Nat → V1 → SpecM O) (B : γ → R → HM (ForInStep R))
    (K : R → HM β) (Inv : Nat → V1 → R → Prop)
    (hstep : ∀ i x v1 r, i < n → items[i]? = some x → Inv i v1 r →
      (∀ v1' r', Inv (i + 1) v1' r' →
        Sim g (L (i + 1) v1') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i v1) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ v1 r, Inv n v1 r → Sim g (L n v1) (K r))
    (v1 : V1) (r : R) (h : Inv 0 v1 r) : Sim g (L 0 v1) (forIn items r B >>= K) :=
  sim_loop0 (C := V1) n items hn (fun i c => L i c) B K (fun i c r => Inv i c r)
    (fun i x c r hi hx hc ih => hstep i x c r hi hx hc fun v1' r' h' => ih v1' r' h')
    (fun c r hc => hend c r hc) v1 r h

/-- `sim_loop0` for a readable loop with 2 loop variables. -/
theorem sim_loopv2 {V1 V2 R O β γ : Type} {g : O → β} (n : Nat) (items : List γ)
    (hn : items.length = n) (L : Nat → V1 → V2 → SpecM O) (B : γ → R → HM (ForInStep R))
    (K : R → HM β) (Inv : Nat → V1 → V2 → R → Prop)
    (hstep : ∀ i x v1 v2 r, i < n → items[i]? = some x → Inv i v1 v2 r →
      (∀ v1' v2' r', Inv (i + 1) v1' v2' r' →
        Sim g (L (i + 1) v1' v2') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i v1 v2) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ v1 v2 r, Inv n v1 v2 r → Sim g (L n v1 v2) (K r))
    (v1 : V1) (v2 : V2) (r : R) (h : Inv 0 v1 v2 r) : Sim g (L 0 v1 v2) (forIn items r B >>= K) :=
  sim_loop0 (C := V1 × V2) n items hn (fun i c => L i (c.1) (c.2)) B K (fun i c r => Inv i (c.1) (c.2) r)
    (fun i x c r hi hx hc ih => hstep i x (c.1) (c.2) r hi hx hc fun v1' v2' r' h' => ih (v1', v2') r' h')
    (fun c r hc => hend (c.1) (c.2) r hc) (v1, v2) r h

/-- `sim_loop0` for a readable loop with 3 loop variables. -/
theorem sim_loopv3 {V1 V2 V3 R O β γ : Type} {g : O → β} (n : Nat) (items : List γ)
    (hn : items.length = n) (L : Nat → V1 → V2 → V3 → SpecM O) (B : γ → R → HM (ForInStep R))
    (K : R → HM β) (Inv : Nat → V1 → V2 → V3 → R → Prop)
    (hstep : ∀ i x v1 v2 v3 r, i < n → items[i]? = some x → Inv i v1 v2 v3 r →
      (∀ v1' v2' v3' r', Inv (i + 1) v1' v2' v3' r' →
        Sim g (L (i + 1) v1' v2' v3') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i v1 v2 v3) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ v1 v2 v3 r, Inv n v1 v2 v3 r → Sim g (L n v1 v2 v3) (K r))
    (v1 : V1) (v2 : V2) (v3 : V3) (r : R) (h : Inv 0 v1 v2 v3 r) : Sim g (L 0 v1 v2 v3) (forIn items r B >>= K) :=
  sim_loop0 (C := V1 × V2 × V3) n items hn (fun i c => L i (c.1) (c.2.1) (c.2.2)) B K (fun i c r => Inv i (c.1) (c.2.1) (c.2.2) r)
    (fun i x c r hi hx hc ih => hstep i x (c.1) (c.2.1) (c.2.2) r hi hx hc fun v1' v2' v3' r' h' => ih (v1', v2', v3') r' h')
    (fun c r hc => hend (c.1) (c.2.1) (c.2.2) r hc) (v1, v2, v3) r h

/-- `sim_loop0` for a readable loop with 4 loop variables. -/
theorem sim_loopv4 {V1 V2 V3 V4 R O β γ : Type} {g : O → β} (n : Nat) (items : List γ)
    (hn : items.length = n) (L : Nat → V1 → V2 → V3 → V4 → SpecM O) (B : γ → R → HM (ForInStep R))
    (K : R → HM β) (Inv : Nat → V1 → V2 → V3 → V4 → R → Prop)
    (hstep : ∀ i x v1 v2 v3 v4 r, i < n → items[i]? = some x → Inv i v1 v2 v3 v4 r →
      (∀ v1' v2' v3' v4' r', Inv (i + 1) v1' v2' v3' v4' r' →
        Sim g (L (i + 1) v1' v2' v3' v4') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i v1 v2 v3 v4) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ v1 v2 v3 v4 r, Inv n v1 v2 v3 v4 r → Sim g (L n v1 v2 v3 v4) (K r))
    (v1 : V1) (v2 : V2) (v3 : V3) (v4 : V4) (r : R) (h : Inv 0 v1 v2 v3 v4 r) : Sim g (L 0 v1 v2 v3 v4) (forIn items r B >>= K) :=
  sim_loop0 (C := V1 × V2 × V3 × V4) n items hn (fun i c => L i (c.1) (c.2.1) (c.2.2.1) (c.2.2.2)) B K (fun i c r => Inv i (c.1) (c.2.1) (c.2.2.1) (c.2.2.2) r)
    (fun i x c r hi hx hc ih => hstep i x (c.1) (c.2.1) (c.2.2.1) (c.2.2.2) r hi hx hc fun v1' v2' v3' v4' r' h' => ih (v1', v2', v3', v4') r' h')
    (fun c r hc => hend (c.1) (c.2.1) (c.2.2.1) (c.2.2.2) r hc) (v1, v2, v3, v4) r h

/-- `sim_loop0` for a readable loop with 5 loop variables. -/
theorem sim_loopv5 {V1 V2 V3 V4 V5 R O β γ : Type} {g : O → β} (n : Nat) (items : List γ)
    (hn : items.length = n) (L : Nat → V1 → V2 → V3 → V4 → V5 → SpecM O) (B : γ → R → HM (ForInStep R))
    (K : R → HM β) (Inv : Nat → V1 → V2 → V3 → V4 → V5 → R → Prop)
    (hstep : ∀ i x v1 v2 v3 v4 v5 r, i < n → items[i]? = some x → Inv i v1 v2 v3 v4 v5 r →
      (∀ v1' v2' v3' v4' v5' r', Inv (i + 1) v1' v2' v3' v4' v5' r' →
        Sim g (L (i + 1) v1' v2' v3' v4' v5') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i v1 v2 v3 v4 v5) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ v1 v2 v3 v4 v5 r, Inv n v1 v2 v3 v4 v5 r → Sim g (L n v1 v2 v3 v4 v5) (K r))
    (v1 : V1) (v2 : V2) (v3 : V3) (v4 : V4) (v5 : V5) (r : R) (h : Inv 0 v1 v2 v3 v4 v5 r) : Sim g (L 0 v1 v2 v3 v4 v5) (forIn items r B >>= K) :=
  sim_loop0 (C := V1 × V2 × V3 × V4 × V5) n items hn (fun i c => L i (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2)) B K (fun i c r => Inv i (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2) r)
    (fun i x c r hi hx hc ih => hstep i x (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2) r hi hx hc fun v1' v2' v3' v4' v5' r' h' => ih (v1', v2', v3', v4', v5') r' h')
    (fun c r hc => hend (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2) r hc) (v1, v2, v3, v4, v5) r h

/-- `sim_loop0` for a readable loop with 6 loop variables. -/
theorem sim_loopv6 {V1 V2 V3 V4 V5 V6 R O β γ : Type} {g : O → β} (n : Nat) (items : List γ)
    (hn : items.length = n) (L : Nat → V1 → V2 → V3 → V4 → V5 → V6 → SpecM O) (B : γ → R → HM (ForInStep R))
    (K : R → HM β) (Inv : Nat → V1 → V2 → V3 → V4 → V5 → V6 → R → Prop)
    (hstep : ∀ i x v1 v2 v3 v4 v5 v6 r, i < n → items[i]? = some x → Inv i v1 v2 v3 v4 v5 v6 r →
      (∀ v1' v2' v3' v4' v5' v6' r', Inv (i + 1) v1' v2' v3' v4' v5' v6' r' →
        Sim g (L (i + 1) v1' v2' v3' v4' v5' v6') (forIn (items.drop (i + 1)) r' B >>= K)) →
      Sim g (L i v1 v2 v3 v4 v5 v6) (B x r >>= loopNext K fun r' => forIn (items.drop (i + 1)) r' B >>= K))
    (hend : ∀ v1 v2 v3 v4 v5 v6 r, Inv n v1 v2 v3 v4 v5 v6 r → Sim g (L n v1 v2 v3 v4 v5 v6) (K r))
    (v1 : V1) (v2 : V2) (v3 : V3) (v4 : V4) (v5 : V5) (v6 : V6) (r : R) (h : Inv 0 v1 v2 v3 v4 v5 v6 r) : Sim g (L 0 v1 v2 v3 v4 v5 v6) (forIn items r B >>= K) :=
  sim_loop0 (C := V1 × V2 × V3 × V4 × V5 × V6) n items hn (fun i c => L i (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2.1) (c.2.2.2.2.2)) B K (fun i c r => Inv i (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2.1) (c.2.2.2.2.2) r)
    (fun i x c r hi hx hc ih => hstep i x (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2.1) (c.2.2.2.2.2) r hi hx hc fun v1' v2' v3' v4' v5' v6' r' h' => ih (v1', v2', v3', v4', v5', v6') r' h')
    (fun c r hc => hend (c.1) (c.2.1) (c.2.2.1) (c.2.2.2.1) (c.2.2.2.2.1) (c.2.2.2.2.2) r hc) (v1, v2, v3, v4, v5, v6) r h

/-! ## Sums and appends -/

/-- A readable index loop that adds the amounts of the items that pass a test, against the hand
`for` loop over the same items. -/
theorem sum_loop {α β δ : Type} [UintC δ] (hbits : UintC.bits δ = 64) (xs : List α) (ab : α → β)
    (cond : α → Bool) (cond' : β → Bool) (amt : α → δ) (amt' : β → Nat)
    (hc : ∀ x, cond' (ab x) = cond x) (ha : ∀ x, amt' (ab x) = UintC.val (amt x))
    (L : Nat → δ → SpecM δ)
    (hL : ∀ i b, L i b = if i < xs.length then
        (lget xs (i : Int) >>= fun x => if cond x = true then
          (lget xs (i : Int) >>= fun y => uOp .add (uv b) (uv (amt y)) >>= fun b' => L (i + 1) b')
        else L (i + 1) b)
      else pure b)
    (B : β → Nat → EpochProofs.Spec.SpecM (ForInStep Nat))
    (hB : ∀ w r, B w r = if cond' w = true then
        (EpochProofs.Spec.uint64Add r (amt' w) >>= fun r' => pure (ForInStep.yield r'))
      else pure (ForInStep.yield r))
    (i : Nat) (b : δ) (hb : UintC.val b < 2 ^ 64) :
    SimI (fun x : δ => UintC.val x < 2 ^ 64) UintC.val (L i b)
      (forIn ((xs.map ab).drop i) (UintC.val b) B) := by
  rw [hL]
  by_cases hi : i < xs.length
  · rw [if_pos hi]
    have hd : (xs.map ab).drop i = ab xs[i] :: (xs.map ab).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
    rw [hd, List.forIn_cons, hB, lget_ok _ _ hi, ok_bind, hc, ha]
    have ih := fun b' (hb' : UintC.val b' < 2 ^ 64) =>
      sum_loop hbits xs ab cond cond' amt amt' hc ha L hL B hB (i + 1) b' hb'
    generalize xs[i] = w at *
    by_cases hcw : cond w = true
    · rw [if_pos hcw, if_pos hcw, ok_bind, show uv b = ((UintC.val b : Nat) : Int) from rfl,
        show uv (amt w) = ((UintC.val (amt w) : Nat) : Int) from rfl, uop_add_eq hbits, u64add_eq]
      by_cases ho : UintC.val b + UintC.val (amt w) < 2 ^ 64
      · rw [if_pos ho, if_pos ho, ok_bind, ok_bind]
        have := ih (UintC.ofNat (UintC.val b + UintC.val (amt w))) (by rw [UintC.val_ofNat]; exact ho)
        rwa [UintC.val_ofNat] at this
      · rw [if_neg ho, if_neg ho, err_bind, err_bind]
        exact ⟨rfl, fun x hx => by cases hx⟩
    · rw [if_neg hcw, if_neg hcw]
      exact ih b hb
  · rw [if_neg hi]
    have hd : (xs.map ab).drop i = [] := by simp; omega
    rw [hd]
    exact ⟨rfl, fun x hx => by cases hx; exact hb⟩
termination_by xs.length - i

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

/-! ## The loop tactic -/

/-- `bridge_loop (Inv)` on a goal `Sim g (f.loopN … n 0 v₁ … vₖ >>= k) (forIn items r B >>= K)`:
apply `sim_loopvₖ` with the invariant `Inv`. The goals left are `hn` (the lengths), `step` (one
step), `fin` (the end of the loop) and `init` (the invariant at the start). The readable loop
has the index parameter `i_` after the bound `n`, then its loop variables. -/
syntax "bridge_loop" "(" term ")" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_loop ($inv)) => withMainContext do
    evalTactic (← `(tactic| first | apply sim_bind_pure | apply sim_bind_proj))
    withMainContext do
    let g ← getMainGoal
    let some (r, _) ← simSides g | throwError "bridge_loop: not a Sim goal"
    let some fn := r.getAppFn.constName? | throwError "bridge_loop: not a loop call"
    let ty := (← getConstInfo fn).type
    let names ← forallTelescope ty fun xs _ => xs.mapM fun x => x.fvarId!.getUserName
    let args := r.getAppArgs
    unless names.size == args.size do throwError "bridge_loop: partial call of {fn}"
    let some idx := names.findIdx? (· == `i_) | throwError "bridge_loop: no index in {fn}"
    let k := args.size - idx - 1
    let L := mkAppN r.getAppFn (args.extract 0 idx)
    let n := args[idx - 1]!
    let LS ← Term.exprToSyntax L
    let nS ← Term.exprToSyntax n
    let lem := mkIdent (Name.mkSimple s!"sim_loopv{k}")
    evalTactic (← `(tactic| refine $lem:ident (n := $nS) (L := $LS) (Inv := $inv)
      (hn := ?hn) (hstep := ?step) (hend := ?fin) (h := ?init) ..))

/-- In a loop step with `hi : i < xs.length` and `hx : items[i]? = some x`: replace `x` by item `i`
of the readable list, and add `lget xs i = .ok xs[i]`. -/
macro "bridge_item" hi:ident hx:ident : tactic => `(tactic| (
  simp only [bridge_abs, List.getElem?_map, List.getElem?_zipIdx, zipIdx_map', Nat.zero_add,
    List.getElem?_eq_getElem $hi, Option.map_some, Option.some.injEq] at $hx:ident
  subst $hx:ident
  have := lget_ok _ _ $hi))

end Pythia.Bridge
