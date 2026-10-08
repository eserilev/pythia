import SpecLean.Interp
import SpecLean.Ssz

/-!
# A run never fills a free address below `next`

New objects come at `next` (`Heap.alloc`), and each write (`Heap.set`) goes to an object that
exists. So a free address below `next` stays free.
-/

namespace SpecLean.NoFill

open SpecLean

/-- `h'` comes from `h` by allocations and writes to objects: `next` grows, and a free address
below `next` stays free. -/
def Keeps (h h' : Heap) : Prop :=
  h.next ≤ h'.next ∧ ∀ a, a < h.next → h.objs a = none → h'.objs a = none

theorem keeps_refl (h : Heap) : Keeps h h := ⟨Nat.le_refl _, fun _ _ e => e⟩

theorem keeps_trans {h1 h2 h3 : Heap} (a : Keeps h1 h2) (b : Keeps h2 h3) : Keeps h1 h3 :=
  ⟨Nat.le_trans a.1 b.1, fun x hx e => b.2 x (Nat.lt_of_lt_of_le hx a.1) (a.2 x hx e)⟩

theorem keeps_alloc (h : Heap) (o : HeapObj) : Keeps h (h.alloc o).2 := by
  refine ⟨by simp [Heap.alloc], fun b hb e => ?_⟩
  simp [Heap.alloc, Nat.ne_of_lt hb, e]

theorem keeps_set {h h1 : Heap} (hk : Keeps h h1) {a : Nat} (ha : h.objs a ≠ none ∨ h1.objs a ≠ none)
    (o : HeapObj) : Keeps h (h1.set a o) := by
  refine ⟨by simpa [Heap.set] using hk.1, fun b hb e => ?_⟩
  have hb1 := hk.2 b hb e
  have hne : b ≠ a := by
    rintro rfl
    rcases ha with ha | ha
    · exact ha e
    · exact ha hb1
  simp [Heap.set, hne, hb1]

/-- Every heap of an ok result keeps `h`. -/
def KR {α : Type} (h : Heap) (r : Res (α × Heap)) : Prop := ∀ x h', r = .ok (x, h') → Keeps h h'

def KH (h : Heap) (r : Res Heap) : Prop := ∀ h', r = .ok h' → Keeps h h'

theorem kr_err {α : Type} (h : Heap) (e : SpecError) : KR (α := α) h (.error e) := by
  intro x h' hr; cases hr

theorem kr_ok {α : Type} {h h' : Heap} (x : α) (hk : Keeps h h') : KR h (.ok (x, h')) := by
  intro y h'' hr; cases hr; exact hk

theorem kr_bind {α β : Type} {h : Heap} {a : Res (α × Heap)} {f : α × Heap → Res (β × Heap)}
    (ha : KR h a) (hf : ∀ x h1, Keeps h h1 → KR h (f (x, h1))) : KR h (a >>= f) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok p =>
    obtain ⟨x, h1⟩ := p
    exact hf x h1 (ha x h1 rfl) y h' hr

theorem kr_bindv {α β : Type} {h : Heap} {a : Res α} {f : α → Res (β × Heap)}
    (hf : ∀ x, KR h (f x)) : KR h (a >>= f) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok x => exact hf x y h' hr

theorem kr_map {α β : Type} {h : Heap} {a : Res (α × Heap)} (g : α → β) (ha : KR h a) :
    KR h ((fun p => (g p.1, p.2)) <$> a) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok p => obtain ⟨x, h1⟩ := p; cases hr; exact ha x h1 rfl

section core

variable [LibModel]

theorem copyList_keeps (d : Nat) (hP : ∀ h v, KR h (deepCopy d h v)) :
    ∀ (xs : List Value) (h : Heap), KR h (copyList d h xs)
  | [], h => by rw [copyList]; exact kr_ok _ (keeps_refl h)
  | x :: xs, h => by
    rw [copyList]
    refine kr_bind (hP h x) fun y h1 hk1 => ?_
    refine kr_bind (fun z h2 e => keeps_trans hk1 (copyList_keeps d hP xs h1 z h2 e)) fun ys h2 hk2 => ?_
    exact kr_ok _ hk2

theorem deepCopy_keeps : ∀ (d : Nat) (h : Heap) (v : Value), KR h (deepCopy d h v)
  | 0, h, v => by rw [deepCopy]; exact kr_err _ _
  | d + 1, h, v => by
    have hQ := copyList_keeps d (deepCopy_keeps d)
    cases v with
    | ref a =>
      rw [deepCopy]
      split
      · refine kr_bind (hQ _ h) fun fs' h1 hk1 => ?_
        exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _))
      · refine kr_bind (hQ _ h) fun fs' h1 hk1 => ?_
        exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _))
      · exact kr_err _ _
    | _ => simp only [deepCopy]; exact kr_ok _ (keeps_refl h)

theorem kh_err (h : Heap) (e : SpecError) : KH h (.error e) := by
  intro h' hr; cases hr

theorem kh_ok {h h' : Heap} (hk : Keeps h h') : KH h (.ok h') := by
  intro h'' hr; cases hr; exact hk

theorem kh_bindv {α : Type} {h : Heap} {a : Res α} {f : α → Res Heap} (hf : ∀ x, KH h (f x)) :
    KH h (a >>= f) := by
  intro h' hr
  cases a with
  | error e => cases hr
  | ok x => exact hf x h' hr

theorem kh_bind {α : Type} {h : Heap} {a : Res (α × Heap)} {f : α × Heap → Res Heap}
    (ha : KR h a) (hf : ∀ x h1, Keeps h h1 → KH h (f (x, h1))) : KH h (a >>= f) := by
  intro h' hr
  cases a with
  | error e => cases hr
  | ok p =>
    obtain ⟨x, h1⟩ := p
    exact hf x h1 (ha x h1 rfl) h' hr

theorem kr_alloc {α : Type} (h : Heap) (o : HeapObj) (f : Nat → α) :
    KR h (.ok (f (h.alloc o).1, (h.alloc o).2)) := kr_ok _ (keeps_alloc h o)

theorem kr_pure_alloc (h : Heap) (xs : List Value) : KR h (pure (allocPyList h xs)) :=
  kr_ok _ (keeps_alloc h _)

theorem kr_ok_alloc (h : Heap) (xs : List Value) : KR h (.ok (allocPyList h xs)) :=
  kr_ok _ (keeps_alloc h _)

theorem kr_pure_set' {α : Type} {h h' : Heap} (x : α) (hk : Keeps h h') : KR h (pure (x, h')) :=
  kr_ok x hk

theorem kr_of_kh {α : Type} {h : Heap} {a : Res Heap} (x : α) (ha : KH h a) :
    KR h (a >>= fun h' => pure (x, h')) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok h1 =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr; exact ha _ rfl

theorem kr_pure_h {α : Type} (h : Heap) (x : α) : KR h (pure (x, h)) := kr_ok _ (keeps_refl h)

/-- One step of a `KR` or `KH` goal: an error, a result at the same heap or after one new
object, a bind, or a case split. -/
syntax "kr_step" : tactic
macro_rules
  | `(tactic| kr_step) => `(tactic| first
    | exact kr_err _ _
    | exact kh_err _ _
    | exact kr_ok _ (keeps_refl _)
    | exact kr_pure_h _ _
    | exact kh_ok (keeps_refl _)
    | exact kr_ok _ (keeps_alloc _ _)
    | exact kr_pure_alloc _ _
    | exact kr_ok_alloc _ _
    | (refine kr_bindv fun _ => ?_)
    | (refine kh_bindv fun _ => ?_)
    | (dsimp only)
    | split
    | (refine kr_bind ?_ fun _ _ _ => ?_; exact kr_pure_h _ _)
    | (exact kh_ok (keeps_set (keeps_refl _) (.inl (by simp_all)) _))
    | (exact kr_ok _ (keeps_set (keeps_refl _) (.inl (by simp_all)) _))
    | (exact kh_ok (keeps_set (by assumption) (.inl (by simp_all)) _))
    | (exact kr_pure_set' _ (keeps_set (keeps_refl _) (.inl (by simp_all)) _)))

/-- The library adds objects at `next` and writes only to objects that exist. -/
structure LibKeeps : Prop where
  coerce : ∀ env f h t v r, LibModel.coerce env f h t v = some r → KR (α := Value) h r
  binopH : ∀ env h op x y r, LibModel.binopH env h op x y = some r → KR (α := Value) h r
  construct : ∀ env h t args kws, KR h (LibModel.construct env h t args kws)
  method : ∀ env h self m args r, LibModel.method env h self m args = some r → KR (α := Value) h r
  append : ∀ env h a v r, LibModel.append env h a v = some r → KH h r
  setSlice : ∀ env h a lo hi ins r, LibModel.setSlice env h a lo hi ins = some r → KH h r
  builtin : ∀ env h b args kws r, LibModel.builtin env h b args kws = some r → KR (α := Value) h r

section lib

variable (hL : LibKeeps)
include hL

theorem coerceWith_keeps (env : Env) (f : Bool) (h : Heap) (t : SszTy) (v : Value) :
    KR h (coerceWith env f h t v) := by
  unfold coerceWith
  split
  · next r hr => exact hL.coerce env f h t v r hr
  · exact kr_ok _ (keeps_refl h)

theorem setItem_keeps (env : Env) (h : Heap) (o iv v : Value) : KH h (setItem env h o iv v) := by
  unfold setItem
  split
  · next a =>
    split
    · next kind elem limit xs ho =>
      refine kh_bindv fun i => ?_
      have fin : ∀ v' h1, Keeps h h1 → KH h (match normIndex xs.length i with
          | some k => Except.ok (h1.set a (HeapObj.list kind elem limit (xs.set k v')))
          | none => Except.error SpecError.indexError) := by
        intro v' h1 hk1
        split
        · exact kh_ok (keeps_set hk1 (.inl (by rw [ho]; simp)) _)
        · exact kh_err _ _
      dsimp only
      split
      · refine kh_bind ?_ fun v' h1 hk1 => fin v' h1 hk1
        intro y h' hr
        cases hc : coerceByte v with
        | error e => rw [hc] at hr; cases hr
        | ok w => rw [hc] at hr; cases hr; exact keeps_refl h
      · exact kh_bind (coerceWith_keeps hL env false h elem v) fun v' h1 hk1 => fin v' h1 hk1
    · next es ho =>
      refine kh_bindv fun k => ?_
      split
      · exact kh_ok (keeps_set (keeps_refl h) (.inl (by rw [ho]; simp)) _)
      · exact kh_ok (keeps_set (keeps_refl h) (.inl (by rw [ho]; simp)) _)
    · exact kh_err _ _
  · exact kh_err _ _

theorem applyBuiltin_keeps (env : Env) (h : Heap) (b : Builtin) (args : List Value)
    (kws : List (Name × Value)) : KR h (applyBuiltin env h b args kws) := by
  unfold applyBuiltin
  split
  · next r hr => exact hL.builtin env h b args kws r hr
  · repeat kr_step

theorem appendItem_keeps (env : Env) (h : Heap) (a : Nat) (v : Value) : KH h (appendItem env h a v) := by
  unfold appendItem
  split
  · next r hr => exact hL.append env h a v r hr
  · repeat kr_step

theorem foldl_append_keeps (env : Env) (a : Nat) :
    ∀ (ys : List Value) (h : Heap), KH h (ys.foldlM (fun h y => appendItem env h a y) h)
  | [], h => by simp only [List.foldlM]; exact kh_ok (keeps_refl h)
  | y :: ys, h => by
    simp only [List.foldlM]
    intro h' hr
    cases ha : appendItem env h a y with
    | error e => rw [ha] at hr; cases hr
    | ok h1 =>
      rw [ha] at hr
      exact keeps_trans (appendItem_keeps hL env h a y h1 ha) (foldl_append_keeps env a ys h1 h' hr)

theorem setSlice_keeps (env : Env) (h : Heap) (o : Value) (lo hi : Option Value) (vals : Value) :
    KH h (setSlice env h o lo hi vals) := by
  unfold setSlice
  repeat (first | kr_step | (next r hr => exact hL.setSlice _ _ _ _ _ _ r hr))

theorem setAttr_keeps (env : Env) (h : Heap) (o : Value) (f : Name) (v : Value) :
    KH h (setAttr env h o f v) := by
  unfold setAttr
  repeat (first | (refine kh_bind (coerceWith_keeps hL _ _ _ _ _) fun _ _ _ => ?_) | kr_step)

theorem seqBinop_keeps (env : Env) (h : Heap) (op : BinOp) (x y : Value) (r : Res (Value × Heap))
    (hr : seqBinop env h op x y = some r) : KR h r := by
  unfold seqBinop at hr
  split at hr
  · simp only [Option.some.injEq] at hr; subst hr
    split
    · next r' hr' => exact hL.binopH env h op _ _ r' hr'
    · repeat kr_step
  · simp only [Option.some.injEq] at hr; subst hr
    split
    · next r' hr' => exact hL.binopH env h op _ _ r' hr'
    · repeat kr_step
  · cases hr

theorem seqAugAdd_keeps (h : Heap) (op : BinOp) (x y : Value) (r : Res (Value × Heap))
    (hr : seqAugAdd h op x y = some r) : KR h r := by
  unfold seqAugAdd at hr
  split at hr
  · split at hr
    · simp only [Option.some.injEq] at hr; subst hr
      repeat kr_step
    · cases hr
  · cases hr

theorem applyDataclass_keeps (env : Env) (h : Heap) (ty : Name) (args : List Value)
    (kws : List (Name × Value)) : KR h (applyDataclass env h ty args kws) := by
  unfold applyDataclass
  repeat kr_step

theorem applyMethod_keeps (env : Env) (h : Heap) (self : Value) (m : Name) (args : List Value) :
    KR h (applyMethod env h self m args) := by
  unfold applyMethod
  split
  · next r hr => exact hL.method env h self m args r hr
  · repeat (first | exact kr_of_kh _ (appendItem_keeps hL _ _ _ _) | exact kr_of_kh _ (foldl_append_keeps hL _ _ _ _) | kr_step)

theorem getSlice_keeps (c : Name) (h : Heap) (o : Value) (lo hi : Option Value) :
    KR h (getSlice c h o lo hi) := by
  unfold getSlice
  repeat kr_step

end lib

end core

/-! ## The SSZ library -/

section ssz

open Ssz

theorem defaultList_keeps (env : Env) (d : Nat) (hP : ∀ h t, KR h (defaultOf env d h t)) :
    ∀ (ts : List SszTy) (h : Heap), KR h (defaultList env d h ts)
  | [], h => by rw [defaultList]; exact kr_ok _ (keeps_refl h)
  | t :: ts, h => by
    rw [defaultList]
    refine kr_bind (hP h t) fun y h1 hk1 => ?_
    refine kr_bind (fun z h2 e => keeps_trans hk1 (defaultList_keeps env d hP ts h1 z h2 e)) fun ys h2 hk2 => ?_
    exact kr_ok _ hk2

theorem defaultOf_keeps (env : Env) : ∀ (d : Nat) (h : Heap) (t : SszTy), KR h (defaultOf env d h t)
  | 0, h, t => by rw [defaultOf.eq_def]; exact kr_err _ _
  | d + 1, h, t => by
    have hQ := defaultList_keeps env d (defaultOf_keeps env d)
    rw [defaultOf.eq_def]; dsimp only
    repeat (first
      | (refine kr_bind (hQ _ _) fun _ h1 hk1 => ?_; exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _)))
      | kr_step)

theorem coerceAll_keeps (env : Env) (d : Nat) (hP : ∀ f h t v, KR h (coerceH env f d h t v)) :
    ∀ (xs : List Value) (h : Heap) (e : SszTy), KR h (coerceAll env d h e xs)
  | [], h, e => by rw [coerceAll]; exact kr_ok _ (keeps_refl h)
  | x :: xs, h, e => by
    rw [coerceAll]
    refine kr_bind (hP false h e x) fun y h1 hk1 => ?_
    refine kr_bind (fun z h2 hz => keeps_trans hk1 (coerceAll_keeps env d hP xs h1 e z h2 hz)) fun ys h2 hk2 => ?_
    exact kr_ok _ hk2

theorem newList_keeps (env : Env) (d : Nat) (hP : ∀ f h t v, KR h (coerceH env f d h t v))
    (h : Heap) (k : ListKind) (e : SszTy) (l : Option Nat) (xs : List Value) :
    KR h (newList env d h k e l xs) := by
  rw [newList]
  refine kr_bindv fun _ => ?_
  have fin : ∀ ys h1, Keeps h h1 → KR h ((fun (p : List Value × Heap) =>
      match h1.alloc (.list k e l p.1) with | (a, h2) => (pure (Value.ref a, h2) : Res (Value × Heap))) (ys, h1)) := by
    intro ys h1 hk1; exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _))
  dsimp only
  split
  · refine kr_bind ?_ fun ys h1 hk1 => kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _))
    intro y h' hr
    cases hc : xs.mapM coerceByte with
    | error e => rw [hc] at hr; cases hr
    | ok w => rw [hc] at hr; cases hr; exact keeps_refl h
  · exact kr_bind (coerceAll_keeps env d hP xs h e) fun ys h1 hk1 => kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _))

theorem coerceH_keeps (env : Env) : ∀ (d : Nat) (f : Bool) (h : Heap) (t : SszTy) (v : Value),
    KR h (coerceH env f d h t v)
  | 0, f, h, t, v => by rw [coerceH.eq_def]; exact kr_err _ _
  | d + 1, f, h, t, v => by
    have hN := newList_keeps env d (coerceH_keeps env d)
    rw [coerceH.eq_def]; dsimp only
    repeat (first | exact hN _ _ _ _ _ | kr_step)

theorem build_keeps (env : Env) :
    ∀ (ps : List ((Name × SszTy) × Option Value)) (h : Heap), KR h (construct.build env h ps)
  | [], h => by simp only [construct.build]; exact kr_ok _ (keeps_refl h)
  | ((_, ft), gv) :: rest, h => by
    simp only [construct.build]
    have tail : ∀ y h1, Keeps h h1 → KR h (do
        let __discr ← construct.build env (y, h1).snd rest
        pure ((y, h1).fst :: __discr.fst, __discr.snd)) := by
      intro y h1 hk1
      dsimp only
      refine kr_bind (fun z h2 hz => keeps_trans hk1 (build_keeps env rest h1 z h2 hz)) fun ys h2 hk2 => ?_
      exact kr_ok _ hk2
    split
    · exact kr_bind (coerceH_keeps env _ _ _ _ _) tail
    · exact kr_bind (defaultOf_keeps env _ _ _) tail

theorem construct_keeps (env : Env) (h : Heap) (t : SszTy) (args : List Value) (kws : List (Name × Value)) :
    KR h (construct env h t args kws) := by
  unfold construct
  repeat (first
    | exact newList_keeps env _ (coerceH_keeps env _) _ _ _ _ _
    | exact defaultOf_keeps env _ _ _
    | (refine kr_bind (build_keeps env _ _) fun _ h1 hk1 => ?_; exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _)))
    | (intro _ _ hr; first
        | (have := newList_keeps env depthBound (coerceH_keeps env _) _ _ _ _ _ _ _ (by
            revert hr; split <;> intro hr <;> first | exact hr | cases hr); exact this))
    | kr_step)

theorem byteListAdd_keeps (env : Env) (h : Heap) (op : BinOp) (x y : Value) (r : Res (Value × Heap))
    (hr : byteListAdd env h op x y = some r) : KR h r := by
  unfold byteListAdd at hr
  dsimp only at hr
  split at hr
  · simp only [Option.some.injEq] at hr; subst hr; repeat kr_step
  · simp only [Option.some.injEq] at hr; subst hr; repeat kr_step
  · cases hr

theorem binopH_keeps (env : Env) (h : Heap) (op : BinOp) (x y : Value) (r : Res (Value × Heap))
    (hr : binopH env h op x y = some r) : KR h r := by
  unfold binopH at hr
  dsimp only at hr
  cases hb : byteListAdd env h op x y with
  | some r' =>
    rw [hb] at hr; simp only [Option.some_or, Option.some.injEq] at hr; subst hr
    exact byteListAdd_keeps env h op x y r' hb
  | none =>
    rw [hb] at hr; simp only [Option.none_or] at hr
    split at hr
    · cases hr
    · simp only [Option.some.injEq] at hr; subst hr
      repeat (first | exact newList_keeps env _ (coerceH_keeps env _) _ _ _ _ _ | kr_step)
    · simp only [Option.some.injEq] at hr; subst hr
      repeat (first | exact newList_keeps env _ (coerceH_keeps env _) _ _ _ _ _ | kr_step)
    · cases hr

theorem method_keeps (env : Env) (h : Heap) (self : Value) (m : Name) (args : List Value)
    (r : Res (Value × Heap)) (hr : method env h self m args = some r) : KR h r := by
  unfold method at hr
  revert hr
  repeat (first
    | (intro hr; simp only [Option.some.injEq] at hr; subst hr;
        first | exact deepCopy_keeps _ _ _ | exact defaultOf_keeps env _ _ _ | (repeat kr_step))
    | (intro hr; cases hr)
    | split)

theorem coerceByte_kr (h : Heap) (v : Value) : KR h ((·, h) <$> coerceByte v) := by
  intro y h' hr
  cases hc : coerceByte v with
  | error e => rw [hc] at hr; cases hr
  | ok w => rw [hc] at hr; cases hr; exact keeps_refl h

theorem append_keeps (env : Env) (h : Heap) (a : Nat) (v : Value) (r : Res Heap)
    (hr : append env h a v = some r) : KH h r := by
  unfold append at hr
  split at hr
  · cases hr
  · simp only [Option.some.injEq] at hr; subst hr
    split
    · exact kh_err _ _
    · exact kh_err _ _
    · try dsimp only
      split
      · refine kh_bind (coerceByte_kr h v) fun v' h1 hk1 => ?_
        refine kh_bindv fun _ => ?_
        exact kh_ok (keeps_set hk1 (.inl (by simp_all)) _)
      · refine kh_bind (coerceH_keeps env _ _ _ _ _) fun v' h1 hk1 => ?_
        refine kh_bindv fun _ => ?_
        exact kh_ok (keeps_set hk1 (.inl (by simp_all)) _)
  · cases hr

theorem sszSetSlice_keeps (env : Env) (h : Heap) (a lo hi : Nat) (ins : List Value) (r : Res Heap)
    (hr : Ssz.setSlice env h a lo hi ins = some r) : KH h r := by
  unfold Ssz.setSlice at hr
  split at hr
  · cases hr
  · simp only [Option.some.injEq] at hr; subst hr
    try dsimp only
    split
    · refine kh_bind ?_ fun v' h1 hk1 => ?_
      · intro y h' hr
        cases hc : ins.mapM coerceByte with
        | error e => rw [hc] at hr; cases hr
        | ok w => rw [hc] at hr; cases hr; exact keeps_refl h
      · refine kh_bindv fun _ => ?_
        exact kh_ok (keeps_set hk1 (.inl (by simp_all)) _)
    · refine kh_bind (coerceAll_keeps env _ (coerceH_keeps env _) _ _ _) fun v' h1 hk1 => ?_
      refine kh_bindv fun _ => ?_
      exact kh_ok (keeps_set hk1 (.inl (by simp_all)) _)
  · cases hr

theorem sszBuiltin_keeps (env : Env) (h : Heap) (b : Builtin) (args : List Value) (kws : List (Name × Value))
    (r : Res (Value × Heap)) (hr : Ssz.builtin env h b args kws = some r) : KR h r := by
  unfold Ssz.builtin at hr
  revert hr
  repeat (first
    | (intro hr; simp only [Option.some.injEq] at hr; subst hr; repeat kr_step)
    | (intro hr; cases hr)
    | split)

theorem sszCoerce_keeps (env : Env) (f : Bool) (h : Heap) (t : SszTy) (v : Value) (r : Res (Value × Heap))
    (hr : Ssz.coerce env f h t v = some r) : KR h r := by
  unfold Ssz.coerce at hr
  split at hr
  · cases hr
  · simp only [Option.some.injEq] at hr; subst hr; exact coerceH_keeps env _ _ _ _ _

/-- The SSZ library adds objects at `next` and writes only to objects that exist. -/
theorem ssz_libKeeps : @LibKeeps Ssz.model where
  coerce := sszCoerce_keeps
  binopH := binopH_keeps
  construct := construct_keeps
  method := method_keeps
  append := append_keeps
  setSlice := sszSetSlice_keeps
  builtin := sszBuiltin_keeps

end ssz

/-! ## The interpreter -/

/-- Every ok result holds a heap (`get`) that keeps `h`. -/
def KG {β : Type} (get : β → Heap) (h : Heap) (r : Res β) : Prop := ∀ p, r = .ok p → Keeps h (get p)

theorem kg_err {β : Type} (get : β → Heap) (h : Heap) (e : SpecError) : KG get h (.error e) := by
  intro p hr; cases hr

theorem kg_pure {β : Type} {get : β → Heap} {h : Heap} (p : β) (hk : Keeps h (get p)) :
    KG get h (pure p) := by
  intro q hr; cases hr; exact hk

theorem kg_bind {β γ : Type} {ga : β → Heap} {gb : γ → Heap} {h : Heap} {a : Res β} {f : β → Res γ}
    (ha : KG ga h a) (hf : ∀ p, Keeps h (ga p) → KG gb h (f p)) : KG gb h (a >>= f) := by
  intro q hr
  cases a with
  | error e => cases hr
  | ok p => exact hf p (ha p rfl) q hr

theorem kg_bindv {α γ : Type} {gb : γ → Heap} {h : Heap} {a : Res α} {f : α → Res γ}
    (hf : ∀ x, KG gb h (f x)) : KG gb h (a >>= f) := by
  intro q hr
  cases a with
  | error e => cases hr
  | ok x => exact hf x q hr

theorem kg_mono {β : Type} {get : β → Heap} {h h1 : Heap} {r : Res β} (hk : Keeps h h1)
    (hr : KG get h1 r) : KG get h r := fun p e => keeps_trans hk (hr p e)

theorem kg_of_kr {α : Type} {h : Heap} {r : Res (α × Heap)} (hr : KR h r) : KG Prod.snd h r :=
  fun p e => by obtain ⟨x, h'⟩ := p; exact hr x h' e

theorem foldlM_keeps {α : Type} (f : Heap → α → Res Heap) (hf : ∀ h x, KH h (f h x)) :
    ∀ (xs : List α) (h : Heap), KH h (xs.foldlM f h)
  | [], h => by simp only [List.foldlM]; exact kh_ok (keeps_refl h)
  | x :: xs, h => by
    simp only [List.foldlM]
    intro h' hr
    cases ha : f h x with
    | error e => rw [ha] at hr; cases hr
    | ok h1 => rw [ha] at hr; exact keeps_trans (hf h x h1 ha) (foldlM_keeps f hf xs h1 h' hr)

theorem kg_of_kh {h : Heap} {r : Res Heap} (hr : KH h r) : KG id h r := fun p e => hr p e

/-- A step of a `KG` goal. The heads of binds use the hypotheses `hX` in the context. -/
syntax "kg_step" : tactic
macro_rules
  | `(tactic| kg_step) => `(tactic| first
    | exact kg_err _ _ _
    | (exact kg_pure _ (by assumption))
    | (exact kg_pure _ (keeps_trans (by assumption) (keeps_alloc _ _)))
    | (exact kg_pure _ (keeps_refl _))
    | (refine kg_bindv fun _ => ?_)
    | (dsimp only)
    | split)

section interp

variable [LibModel] (env : Env) (hL : LibKeeps)

/-- Each function that lowers the fuel keeps the heap at fuel `n`. -/
structure Base (n : Nat) : Prop where
  expr : ∀ L h e, KG Prod.snd h (evalExpr env n L h e)
  items : ∀ L h t ifs rest elt st src i, KG (fun p => p.2.2) h (compItems env n L h t ifs rest elt st src i)
  fn : ∀ ps body base vs kws h, KG Prod.snd h (callFn env n ps body base vs kws h)
  filter : ∀ f xs h, KG Prod.snd h (filterItems env n f xs h)
  map : ∀ f xs h, KG Prod.snd h (mapItems env n f xs h)
  target : ∀ L h t v, KG Prod.snd h (assignTarget env n L h t v)
  stmt : ∀ L h s, KG (fun p => p.2.2) h (execStmt env n L h s)
  forLoop : ∀ L h t src i body, KG (fun p => p.2.2) h (execFor env n L h t src i body)
  whileLoop : ∀ L h c body, KG (fun p => p.2.2) h (execWhile env n L h c body)

theorem base_zero : Base env 0 where
  expr L h e := by rw [evalExpr]; exact kg_err _ _ _
  items := by intro L h t ifs rest elt st src i; rw [compItems]; exact kg_err _ _ _
  fn := by intro ps body base vs kws h; rw [callFn]; exact kg_err _ _ _
  filter := by intro f xs h; rw [filterItems]; exact kg_err _ _ _
  map := by intro f xs h; rw [mapItems]; exact kg_err _ _ _
  target := by intro L h t v; rw [assignTarget]; exact kg_err _ _ _
  stmt := by intro L h s; rw [execStmt]; exact kg_err _ _ _
  forLoop := by intro L h t src i body; rw [execFor]; exact kg_err _ _ _
  whileLoop := by intro L h c body; rw [execWhile]; exact kg_err _ _ _

section derived

variable {env} {n : Nat} (B : Base env n)
include B

theorem opt_keeps (L : Locals) (h : Heap) (o : Option Expr) : KG Prod.snd h (evalOpt env n L h o) := by
  cases o with
  | none => rw [evalOpt]; exact kg_pure _ (keeps_refl h)
  | some e =>
    rw [evalOpt]
    exact kg_bind (B.expr L h e) fun p hp => kg_pure _ hp

theorem list_keeps (L : Locals) : ∀ (es : List Expr) (h : Heap), KG Prod.snd h (evalList env n L h es)
  | [], h => by rw [evalList]; exact kg_pure _ (keeps_refl h)
  | e :: es, h => by
    rw [evalList]
    refine kg_bind (B.expr L h e) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    exact kg_bind (kg_mono hp (list_keeps L es h1)) fun q hq => kg_pure _ hq

theorem args_keeps (L : Locals) : ∀ (as : List Arg) (h : Heap),
    KG (fun p => p.2.2) h (evalArgs env n L h as)
  | [], h => by rw [evalArgs]; exact kg_pure _ (keeps_refl h)
  | a :: as, h => by
    rw [evalArgs.eq_def]; dsimp only
    cases a with
    | pos e =>
      refine kg_bind (B.expr L h e) fun p hp => ?_
      obtain ⟨v, h1⟩ := p
      exact kg_bind (kg_mono hp (args_keeps L as h1)) fun q hq => kg_pure _ hq
    | starred e =>
      refine kg_bind (B.expr L h e) fun p hp => ?_
      obtain ⟨v, h1⟩ := p
      refine kg_bindv fun _ => ?_
      exact kg_bind (kg_mono hp (args_keeps L as h1)) fun q hq => kg_pure _ hq
    | kw k e =>
      refine kg_bind (B.expr L h e) fun p hp => ?_
      obtain ⟨v, h1⟩ := p
      exact kg_bind (kg_mono hp (args_keeps L as h1)) fun q hq => kg_pure _ hq

theorem cmp_keeps (L : Locals) : ∀ (rest : List (CmpOp × Expr)) (h : Heap) (x : Value),
    KG Prod.snd h (evalCmp env n L h x rest)
  | [], h, x => by rw [evalCmp]; exact kg_pure _ (keeps_refl h)
  | (op, e) :: rest, h, x => by
    rw [evalCmp]
    refine kg_bind (B.expr L h e) fun p hp => ?_
    obtain ⟨y, h1⟩ := p
    refine kg_bindv fun b => ?_
    split
    · exact kg_mono hp (cmp_keeps L rest h1 y)
    · exact kg_pure _ hp

theorem boolop_keeps (L : Locals) (op : BoolOp) : ∀ (es : List Expr) (h : Heap),
    KG Prod.snd h (evalBoolOp env n L h op es)
  | [], h => by rw [evalBoolOp]; exact kg_err _ _ _
  | e :: es, h => by
    rw [evalBoolOp]
    refine kg_bind (B.expr L h e) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    dsimp only
    split
    · exact kg_pure _ hp
    · refine kg_bindv fun b => ?_
      split
      · exact kg_pure _ hp
      · exact kg_pure _ hp
      · exact kg_mono hp (boolop_keeps L op es h1)

theorem ifs_keeps (L : Locals) : ∀ (cs : List Expr) (h : Heap), KG Prod.snd h (evalIfs env n L h cs)
  | [], h => by rw [evalIfs]; exact kg_pure _ (keeps_refl h)
  | c :: cs, h => by
    rw [evalIfs]
    refine kg_bind (B.expr L h c) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    refine kg_bindv fun b => ?_
    split
    · exact kg_mono hp (ifs_keeps L cs h1)
    · exact kg_pure _ hp

theorem comp_keeps (L : Locals) (h : Heap) (gs : List Comprehension) (elt : Expr) (st : Option Bool) :
    KG (fun p => p.2.2) h (compLoop env n L h gs elt st) := by
  cases gs with
  | nil =>
    rw [compLoop]
    refine kg_bind (B.expr L h elt) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    dsimp only
    split
    · exact kg_bindv fun _ => kg_pure _ hp
    · exact kg_pure _ hp
  | cons g gs =>
    obtain ⟨t, it, ifs⟩ := g
    rw [compLoop]
    refine kg_bind (B.expr L h it) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    exact kg_bindv fun src => kg_mono hp (B.items L h1 t ifs gs elt st src 0)

theorem filter_lift : ∀ (f : Value) (xs : List Value) (h : Heap), KG Prod.snd h (filterItems env n f xs h) :=
  B.filter

include hL in
theorem call_keeps (f : Value) (vs : List Value) (kws : List (Name × Value)) (h : Heap) :
    KG Prod.snd h (callValue env n f vs kws h) := by
  rw [callValue.eq_def]
  all_goals repeat (first
    | exact B.fn _ _ _ _ _ _
    | exact kg_of_kr (applyBuiltin_keeps hL _ _ _ _ _)
    | exact kg_of_kr (hL.construct _ _ _ _ _)
    | exact kg_of_kr (applyDataclass_keeps hL _ _ _ _ _)
    | exact kg_of_kr (applyMethod_keeps hL _ _ _ _ _)
    | (refine kg_bind (B.filter _ _ _) fun p hp => kg_pure _ hp)
    | (refine kg_bind (B.map _ _ _) fun p hp => ?_; exact kg_bindv fun _ => kg_pure _ (keeps_trans hp (keeps_alloc _ _)))
    | (simp only [frame_eq])
    | kg_step)

theorem targets_keeps (L : Locals) : ∀ (ts : List Target) (vs : List Value) (h : Heap),
    KG Prod.snd h (assignTargets env n L h ts vs)
  | t :: ts, v :: vs, h => by
    rw [assignTargets]
    refine kg_bind (B.target L h t v) fun p hp => ?_
    obtain ⟨L1, h1⟩ := p
    exact kg_mono hp (targets_keeps L1 ts vs h1)
  | [], _, h => by rw [assignTargets]; exact kg_pure _ (keeps_refl h)
  | _ :: _, [], h => by rw [assignTargets]; exact kg_pure _ (keeps_refl h)

theorem all_keeps : ∀ (L : Locals) (ts : List Target) (v : Value) (h : Heap),
    KG Prod.snd h (assignAll env n L h ts v)
  | L, [], v, h => by rw [assignAll]; exact kg_pure _ (keeps_refl h)
  | L, t :: ts, v, h => by
    rw [assignAll]
    refine kg_bind (B.target L h t v) fun p hp => ?_
    obtain ⟨L1, h1⟩ := p
    exact kg_mono hp (all_keeps L1 ts v h1)

theorem block_keeps : ∀ (L : Locals) (ss : List Stmt) (h : Heap),
    KG (fun p => p.2.2) h (execBlock env n L h ss)
  | L, [], h => by rw [execBlock]; exact kg_pure _ (keeps_refl h)
  | L, s :: ss, h => by
    rw [execBlock]
    refine kg_bind (B.stmt L h s) fun p hp => ?_
    obtain ⟨o, L1, h1⟩ := p
    dsimp only
    split
    · exact kg_mono hp (block_keeps L1 ss h1)
    · exact kg_pure _ hp

end derived

section succ

variable {env} {n : Nat} (B : Base env n)
include B hL

theorem expr_succ (L : Locals) (h : Heap) (e : Expr) : KG Prod.snd h (evalExpr env (n + 1) L h e) := by
  rw [evalExpr.eq_def]
  dsimp only
  have h0 := keeps_refl h
  cases e
  all_goals repeat (first
    | (refine kg_bind (kg_mono (by assumption) (B.expr _ _ _)) fun p hp => ?_; obtain ⟨_, _⟩ := p)
    | (refine kg_bind (kg_mono (by assumption) (opt_keeps B _ _ _)) fun p hp => ?_; obtain ⟨_, _⟩ := p)
    | (refine kg_bind (kg_mono (by assumption) (list_keeps B _ _ _)) fun p hp => ?_; obtain ⟨_, _⟩ := p)
    | (refine kg_bind (kg_mono (by assumption) (args_keeps B _ _ _)) fun p hp => ?_; obtain ⟨_, _, _⟩ := p)
    | (refine kg_bind (kg_mono (by assumption) (comp_keeps B _ _ _ _ _)) fun p hp => ?_; obtain ⟨_, _, _⟩ := p)
    | exact kg_mono (by assumption) (cmp_keeps B _ _ _ _)
    | exact kg_mono (by assumption) (boolop_keeps B _ _ _ _)
    | exact kg_mono (by assumption) (call_keeps hL B _ _ _ _)
    | exact kg_mono (by assumption) (B.expr _ _ _)
    | exact kg_mono (by assumption) (kg_of_kr (getSlice_keeps hL _ _ _ _ _))
    | (next r hr => exact kg_mono (by assumption) (kg_of_kr (seqBinop_keeps hL _ _ _ _ _ r hr)))
    | (refine kg_bind (kg_mono (keeps_trans (by assumption) (keeps_alloc _ _))
          (kg_of_kh (foldlM_keeps _ (fun _ kv => by obtain ⟨_, _⟩ := kv; exact setItem_keeps hL _ _ _ _ _) _ _)))
          fun p hp => kg_pure _ hp)
    | (exact kg_pure _ (keeps_trans (by assumption) (keeps_alloc _ _)))
    | kg_step)

/-- A step of a statement goal at fuel `n + 1`: the heads at fuel `n`, the heap writes, or `kg_step`. -/
syntax "kg_stmt" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| kg_stmt) => `(tactic| first
    | (refine kg_bind (kg_mono (by assumption) (B.expr _ _ _)) fun p hp => ?_; obtain ⟨_, _⟩ := p; try dsimp only at hp)
    | (refine kg_bind (kg_mono (by assumption) (opt_keeps B _ _ _)) fun p hp => ?_; obtain ⟨_, _⟩ := p; try dsimp only at hp)
    | (refine kg_bind (kg_mono (by assumption) (B.target _ _ _ _)) fun p hp => ?_; obtain ⟨_, _⟩ := p; try dsimp only at hp)
    | (refine kg_bind (kg_mono (by assumption) (all_keeps B _ _ _ _)) fun p hp => ?_; obtain ⟨_, _⟩ := p; try dsimp only at hp)
    | (refine kg_bind (kg_mono (by assumption) (block_keeps B _ _ _)) fun p hp => ?_; obtain ⟨_, _, _⟩ := p; try dsimp only at hp)
    | (refine kg_bind (kg_mono (by assumption) (kg_of_kh (setAttr_keeps hL _ _ _ _ _))) fun p hp => ?_)
    | (refine kg_bind (kg_mono (by assumption) (kg_of_kh (setItem_keeps hL _ _ _ _ _))) fun p hp => ?_)
    | (refine kg_bind (kg_mono (by assumption) (kg_of_kh (setSlice_keeps hL _ _ _ _ _ _))) fun p hp => ?_)
    | (refine kg_bind (kg_mono (by assumption) (kg_of_kr (seqAugAdd_keeps hL _ _ _ _ _ (by assumption))))
        fun p hp => ?_; obtain ⟨_, _⟩ := p; try dsimp only at hp)
    | (refine kg_bind (kg_mono (by assumption) (kg_of_kr (seqBinop_keeps hL _ _ _ _ _ _ (by assumption))))
        fun p hp => ?_; obtain ⟨_, _⟩ := p; try dsimp only at hp)
    | exact kg_mono (by assumption) (targets_keeps B _ _ _ _)
    | exact kg_mono (by assumption) (block_keeps B _ _ _)
    | exact kg_mono (by assumption) (B.forLoop _ _ _ _ _ _)
    | exact kg_mono (by assumption) (B.whileLoop _ _ _ _)
    | (exact kg_pure _ (keeps_trans (by assumption) (keeps_alloc _ _)))
    | kg_step)

theorem items_succ (L : Locals) (h : Heap) (t : Target) (ifs : List Expr) (rest : List Comprehension)
    (elt : Expr) (st : Option Bool) (src : IterSrc) (i : Nat) :
    KG (fun p => p.2.2) h (compItems env (n + 1) L h t ifs rest elt st src i) := by
  rw [compItems]
  have h0 := keeps_refl h
  refine kg_bindv fun ox => ?_
  split
  · exact kg_pure _ h0
  · refine kg_bind (B.target L h t _) fun p hp => ?_
    obtain ⟨L1, h1⟩ := p
    refine kg_bind (kg_mono hp (ifs_keeps B L1 ifs h1)) fun q hq => ?_
    obtain ⟨keep, h2⟩ := q
    dsimp only
    have tail : ∀ r : List Value × Bool × Heap, Keeps h r.2.2 →
        KG (fun p => p.2.2) h (if r.2.1 = true then pure (r.1, true, r.2.2) else do
          let d ← compItems env n L1 r.2.2 t ifs rest elt st src (i + 1)
          pure (r.1 ++ d.1, d.2.1, d.2.2)) := by
      intro r hr
      split
      · exact kg_pure _ hr
      · exact kg_bind (kg_mono hr (B.items L1 r.2.2 t ifs rest elt st src (i + 1))) fun r2 hr2 => kg_pure _ hr2
    split
    · exact kg_bind (kg_mono hq (comp_keeps B L1 h2 rest elt st)) tail
    · exact kg_bind (kg_pure _ hq) tail

theorem fn_succ (ps : Params) (body : ClosureBody) (base : Locals) (vs : List Value)
    (kws : List (Name × Value)) (h : Heap) : KG Prod.snd h (callFn env (n + 1) ps body base vs kws h) := by
  rw [callFn]
  refine kg_bind (list_keeps B _ _ h) fun p hp => ?_
  obtain ⟨ds, h0⟩ := p
  refine kg_bindv fun L0 => ?_
  dsimp only
  split
  · exact kg_mono hp (B.expr _ _ _)
  · refine kg_bind (kg_mono hp (block_keeps B _ _ _)) fun q hq => ?_
    obtain ⟨o, L1, h1⟩ := q
    dsimp only
    split <;> exact kg_pure _ hq

theorem filter_succ (f : Value) : ∀ (xs : List Value) (h : Heap), KG Prod.snd h (filterItems env (n + 1) f xs h)
  | [], h => by rw [filterItems]; exact kg_pure _ (keeps_refl h)
  | x :: xs, h => by
    rw [filterItems]
    refine kg_bind (call_keeps hL B _ _ _ h) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    refine kg_bindv fun keep => ?_
    refine kg_bind (kg_mono hp (filter_succ f xs h1)) fun q hq => ?_
    exact kg_pure _ hq

theorem map_succ (f : Value) : ∀ (xs : List Value) (h : Heap), KG Prod.snd h (mapItems env (n + 1) f xs h)
  | [], h => by rw [mapItems]; exact kg_pure _ (keeps_refl h)
  | x :: xs, h => by
    rw [mapItems]
    refine kg_bind (call_keeps hL B _ _ _ h) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    refine kg_bind (kg_mono hp (map_succ f xs h1)) fun q hq => ?_
    exact kg_pure _ hq

theorem target_succ (L : Locals) (h : Heap) (t : Target) (v : Value) :
    KG Prod.snd h (assignTarget env (n + 1) L h t v) := by
  rw [assignTarget.eq_def]; dsimp only
  have h0 := keeps_refl h
  cases t
  repeat' kg_stmt

theorem stmt_succ (L : Locals) (h : Heap) (st : Stmt) :
    KG (fun p => p.2.2) h (execStmt env (n + 1) L h st) := by
  rw [execStmt.eq_def]; dsimp only
  have h0 := keeps_refl h
  cases st
  repeat' kg_stmt

theorem for_succ (L : Locals) (h : Heap) (t : Target) (src : IterSrc) (i : Nat) (body : List Stmt) :
    KG (fun p => p.2.2) h (execFor env (n + 1) L h t src i body) := by
  rw [execFor]
  have h0 := keeps_refl h
  repeat kg_stmt

theorem while_succ (L : Locals) (h : Heap) (c : Expr) (body : List Stmt) :
    KG (fun p => p.2.2) h (execWhile env (n + 1) L h c body) := by
  rw [execWhile]
  have h0 := keeps_refl h
  repeat kg_stmt

end succ

include hL in
theorem base_succ {n : Nat} (B : Base env n) : Base env (n + 1) where
  expr := expr_succ hL B
  items := items_succ hL B
  fn := fn_succ hL B
  filter := filter_succ hL B
  map := map_succ hL B
  target := target_succ hL B
  stmt := stmt_succ hL B
  forLoop := for_succ hL B
  whileLoop := while_succ hL B

include hL in
theorem base_all : ∀ n, Base env n
  | 0 => base_zero env
  | n + 1 => base_succ env hL (base_all n)

include hL in
/-- A call never puts an object at a free address below `next`. -/
theorem callFn_noFill {n : Nat} {ps : Params} {body : ClosureBody} {base : Locals} {vs : List Value}
    {kws : List (Name × Value)} {h h' : Heap} {v : Value}
    (hr : callFn env n ps body base vs kws h = .ok (v, h')) :
    ∀ a, a < h.next → h.objs a = none → h'.objs a = none :=
  ((base_all env hL n).fn ps body base vs kws h (v, h') hr).2

end interp

end SpecLean.NoFill
