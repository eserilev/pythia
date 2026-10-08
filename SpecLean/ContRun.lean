import SpecLean.Interp
import SpecLean.Ssz

/-!
# A run keeps the field count of each container

Each container object has the field count of its class in `env.containers`, if its class is
there. A run keeps this: new containers get one value per field, a copy keeps the count, and a
field write keeps the count. The walk over the interpreter is the one of `NoFill`.
-/

namespace SpecLean.ContRun

open SpecLean

/-- Each container object of the heap has the field count of its class. -/
def CW (env : Env) (h : Heap) : Prop :=
  ∀ a ty fs ffs, h.objs a = some (.container ty fs) → env.containers.lookup ty = some ffs →
    fs.length = ffs.length

/-- An object that `CW` allows. -/
def ObjOK (env : Env) (o : HeapObj) : Prop :=
  ∀ ty fs, o = .container ty fs → ∀ ffs, env.containers.lookup ty = some ffs → fs.length = ffs.length

theorem objOK_list (env : Env) (k : ListKind) (e : SszTy) (l : Option Nat) (xs : List Value) :
    ObjOK env (.list k e l xs) := fun _ _ e => by cases e

/-- A goal `ObjOK env o` for an object that is not a container. -/
syntax "objok" : tactic
macro_rules
  | `(tactic| objok) => `(tactic| first
    | exact objOK_list _ _ _ _ _
    | (intro _ _ e; cases e; done)
    | assumption)

/-- `h'` comes from `h` by steps that keep `CW`. -/
def Keeps (env : Env) (h h' : Heap) : Prop := CW env h → CW env h'

variable {env : Env}

theorem keeps_refl (h : Heap) : Keeps env h h := fun c => c

theorem keeps_trans {h1 h2 h3 : Heap} (a : Keeps env h1 h2) (b : Keeps env h2 h3) : Keeps env h1 h3 :=
  fun c => b (a c)

theorem keeps_alloc (h : Heap) (o : HeapObj) (ho : ObjOK env o) : Keeps env h (h.alloc o).2 := by
  intro c a ty fs ffs hx hl
  simp only [Heap.alloc] at hx
  split at hx
  · cases hx; exact ho ty fs rfl ffs hl
  · exact c a ty fs ffs hx hl

theorem keeps_set {h h1 : Heap} (hk : Keeps env h h1) (a : Nat) (o : HeapObj) (ho : ObjOK env o) :
    Keeps env h (h1.set a o) := by
  intro c b ty fs ffs hx hl
  simp only [Heap.set] at hx
  split at hx
  · cases hx; exact ho ty fs rfl ffs hl
  · exact hk c b ty fs ffs hx hl

/-- Every heap of an ok result keeps `h`. -/
def KR (env : Env) {α : Type} (h : Heap) (r : Res (α × Heap)) : Prop := ∀ x h', r = .ok (x, h') → Keeps env h h'

def KH (env : Env) (h : Heap) (r : Res Heap) : Prop := ∀ h', r = .ok h' → Keeps env h h'

theorem kr_err {α : Type} (h : Heap) (e : SpecError) : KR env (α := α) h (.error e) := by
  intro x h' hr; cases hr

theorem kr_ok {α : Type} {h h' : Heap} (x : α) (hk : Keeps env h h') : KR env h (.ok (x, h')) := by
  intro y h'' hr; cases hr; exact hk

theorem kr_bind {α β : Type} {h : Heap} {a : Res (α × Heap)} {f : α × Heap → Res (β × Heap)}
    (ha : KR env h a) (hf : ∀ x h1, Keeps env h h1 → KR env h (f (x, h1))) : KR env h (a >>= f) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok p =>
    obtain ⟨x, h1⟩ := p
    exact hf x h1 (ha x h1 rfl) y h' hr

theorem kr_bindv {α β : Type} {h : Heap} {a : Res α} {f : α → Res (β × Heap)}
    (hf : ∀ x, KR env h (f x)) : KR env h (a >>= f) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok x => exact hf x y h' hr

theorem kr_map {α β : Type} {h : Heap} {a : Res (α × Heap)} (g : α → β) (ha : KR env h a) :
    KR env h ((fun p => (g p.1, p.2)) <$> a) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok p => obtain ⟨x, h1⟩ := p; cases hr; exact ha x h1 rfl

section core

variable [LibModel]

/-! ## Field counts -/

theorem keeps_alloc' {h h1 : Heap} (hk : Keeps env h h1) (o : HeapObj) (ho : CW env h → ObjOK env o) :
    Keeps env h (h1.alloc o).2 := fun c => keeps_alloc h1 o (ho c) (hk c)

theorem keeps_set' {h h1 : Heap} (hk : Keeps env h h1) (a : Nat) (o : HeapObj)
    (ho : CW env h → ObjOK env o) : Keeps env h (h1.set a o) :=
  fun c => keeps_set (keeps_refl h1) a o (ho c) (hk c)

theorem kr_bindE {α β : Type} {h : Heap} {a : Res (α × Heap)} {f : α × Heap → Res (β × Heap)}
    (ha : KR env h a) (hf : ∀ x h1, a = .ok (x, h1) → Keeps env h h1 → KR env h (f (x, h1))) :
    KR env h (a >>= f) := by
  intro y h' hr
  cases e : a with
  | error e' => rw [e] at hr; cases hr
  | ok p => obtain ⟨x, h1⟩ := p; rw [e] at hr; exact hf x h1 e (ha x h1 e) y h' hr

theorem kr_bindvE {α β : Type} {h : Heap} {a : Res α} {f : α → Res (β × Heap)}
    (hf : ∀ x, a = .ok x → KR env h (f x)) : KR env h (a >>= f) := by
  intro y h' hr
  cases e : a with
  | error e' => rw [e] at hr; cases hr
  | ok x => rw [e] at hr; exact hf x e y h' hr

theorem except_bind_ok {ε α β : Type} {a : Except ε α} {f : α → Except ε β} {y : β}
    (e : a >>= f = .ok y) : ∃ x, a = .ok x ∧ f x = .ok y := by
  cases a with
  | error _ => cases e
  | ok x => exact ⟨x, rfl, e⟩

theorem except_mapM_length {α β ε : Type} {f : α → Except ε β} :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ys.length = xs.length
  | [], ys, e => by cases e; rfl
  | x :: xs, ys, e => by
    rw [List.mapM_cons] at e
    obtain ⟨y, -, e⟩ := except_bind_ok e
    obtain ⟨zs, e2, e⟩ := except_bind_ok e
    cases e
    simp [except_mapM_length xs zs e2]

theorem ctorFields_length {fields : List Name} {args : List Value} {kws : List (Name × Value)}
    {g : List (Option Value)} (e : ctorFields fields args kws = .ok g) : g.length = fields.length := by
  unfold ctorFields at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e; simp


theorem copyList_length (d : Nat) : ∀ (xs : List Value) (h : Heap) (ys : List Value) (h' : Heap),
    copyList d h xs = .ok (ys, h') → ys.length = xs.length
  | [], h, ys, h', e => by rw [copyList] at e; cases e; rfl
  | x :: xs, h, ys, h', e => by
    rw [copyList] at e
    obtain ⟨⟨y, h1⟩, -, e⟩ := except_bind_ok e
    dsimp only at e
    obtain ⟨⟨zs, h2⟩, e2, e⟩ := except_bind_ok e
    cases e
    simp [copyList_length d xs h1 zs h2 e2]

theorem copyList_keeps (d : Nat) (hP : ∀ h v, KR env h (deepCopy d h v)) :
    ∀ (xs : List Value) (h : Heap), KR env h (copyList d h xs)
  | [], h => by rw [copyList]; exact kr_ok _ (keeps_refl h)
  | x :: xs, h => by
    rw [copyList]
    refine kr_bind (hP h x) fun y h1 hk1 => ?_
    refine kr_bind (fun z h2 e => keeps_trans hk1 (copyList_keeps d hP xs h1 z h2 e)) fun ys h2 hk2 => ?_
    exact kr_ok _ hk2

theorem deepCopy_keeps : ∀ (d : Nat) (h : Heap) (v : Value), KR env h (deepCopy d h v)
  | 0, h, v => by rw [deepCopy]; exact kr_err _ _
  | d + 1, h, v => by
    have hQ := copyList_keeps d (deepCopy_keeps d)
    cases v with
    | ref a =>
      rw [deepCopy]
      split
      · refine kr_bindE (hQ _ h) fun fs' h1 e hk1 => ?_
        refine kr_ok _ (keeps_alloc' hk1 _ fun c _ _ eo ffs hl => ?_)
        cases eo
        rw [copyList_length d _ h fs' h1 e]
        exact c _ _ _ _ (by assumption) hl
      · refine kr_bind (hQ _ h) fun fs' h1 hk1 => ?_
        exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _ (by objok)))
      · exact kr_err _ _
    | _ => simp only [deepCopy]; exact kr_ok _ (keeps_refl h)

theorem kh_err (h : Heap) (e : SpecError) : KH env h (.error e) := by
  intro h' hr; cases hr

theorem kh_ok {h h' : Heap} (hk : Keeps env h h') : KH env h (.ok h') := by
  intro h'' hr; cases hr; exact hk

theorem kh_bindv {α : Type} {h : Heap} {a : Res α} {f : α → Res Heap} (hf : ∀ x, KH env h (f x)) :
    KH env h (a >>= f) := by
  intro h' hr
  cases a with
  | error e => cases hr
  | ok x => exact hf x h' hr

theorem kh_bind {α : Type} {h : Heap} {a : Res (α × Heap)} {f : α × Heap → Res Heap}
    (ha : KR env h a) (hf : ∀ x h1, Keeps env h h1 → KH env h (f (x, h1))) : KH env h (a >>= f) := by
  intro h' hr
  cases a with
  | error e => cases hr
  | ok p =>
    obtain ⟨x, h1⟩ := p
    exact hf x h1 (ha x h1 rfl) h' hr

theorem kr_alloc {α : Type} (h : Heap) (o : HeapObj) (ho : ObjOK env o) (f : Nat → α) :
    KR env h (.ok (f (h.alloc o).1, (h.alloc o).2)) := kr_ok _ (keeps_alloc h o ho)

theorem kr_pure_alloc (h : Heap) (xs : List Value) : KR env h (pure (allocPyList h xs)) :=
  kr_ok _ (keeps_alloc h _ (by objok))

theorem kr_ok_alloc (h : Heap) (xs : List Value) : KR env h (.ok (allocPyList h xs)) :=
  kr_ok _ (keeps_alloc h _ (by objok))

theorem kr_pure_set' {α : Type} {h h' : Heap} (x : α) (hk : Keeps env h h') : KR env h (pure (x, h')) :=
  kr_ok x hk

theorem kr_of_kh {α : Type} {h : Heap} {a : Res Heap} (x : α) (ha : KH env h a) :
    KR env h (a >>= fun h' => pure (x, h')) := by
  intro y h' hr
  cases a with
  | error e => cases hr
  | ok h1 =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr; exact ha _ rfl

theorem kr_pure_h {α : Type} (h : Heap) (x : α) : KR env h (pure (x, h)) := kr_ok _ (keeps_refl h)
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
    | exact kr_ok _ (keeps_alloc _ _ (by objok))
    | exact kr_pure_alloc _ _
    | exact kr_ok_alloc _ _
    | (refine kr_bindv fun _ => ?_)
    | (refine kh_bindv fun _ => ?_)
    | (dsimp only)
    | split
    | (refine kr_bind ?_ fun _ _ _ => ?_; exact kr_pure_h _ _)
    | (exact kh_ok (keeps_set (keeps_refl _) _ _ (by objok)))
    | (exact kr_ok _ (keeps_set (keeps_refl _) _ _ (by objok)))
    | (exact kh_ok (keeps_set (by assumption) _ _ (by objok)))
    | (exact kr_pure_set' _ (keeps_set (keeps_refl _) _ _ (by objok))))

/-- The library adds objects at `next` and writes only to objects that exist. -/
structure LibKeeps : Prop where
  coerce : ∀ env f h t v r, LibModel.coerce env f h t v = some r → KR env (α := Value) h r
  binopH : ∀ env h op x y r, LibModel.binopH env h op x y = some r → KR env (α := Value) h r
  construct : ∀ env h t args kws, KR env h (LibModel.construct env h t args kws)
  method : ∀ env h self m args r, LibModel.method env h self m args = some r → KR env (α := Value) h r
  append : ∀ env h a v r, LibModel.append env h a v = some r → KH env h r
  setSlice : ∀ env h a lo hi ins r, LibModel.setSlice env h a lo hi ins = some r → KH env h r
  builtin : ∀ env h b args kws r, LibModel.builtin env h b args kws = some r → KR env (α := Value) h r

section lib

variable (hL : LibKeeps)
include hL

theorem coerceWith_keeps (env : Env) (f : Bool) (h : Heap) (t : SszTy) (v : Value) :
    KR env h (coerceWith env f h t v) := by
  unfold coerceWith
  split
  · next r hr => exact hL.coerce env f h t v r hr
  · exact kr_ok _ (keeps_refl h)

theorem setItem_keeps (env : Env) (h : Heap) (o iv v : Value) : KH env h (setItem env h o iv v) := by
  unfold setItem
  split
  · next a =>
    split
    · next kind elem limit xs ho =>
      refine kh_bindv fun i => ?_
      have fin : ∀ v' h1, Keeps env h h1 → KH env h (match normIndex xs.length i with
          | some k => Except.ok (h1.set a (HeapObj.list kind elem limit (xs.set k v')))
          | none => Except.error SpecError.indexError) := by
        intro v' h1 hk1
        split
        · exact kh_ok (keeps_set hk1 _ _ (by objok))
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
      · exact kh_ok (keeps_set (keeps_refl h) _ _ (by objok))
      · exact kh_ok (keeps_set (keeps_refl h) _ _ (by objok))
    · exact kh_err _ _
  · exact kh_err _ _

theorem applyBuiltin_keeps (env : Env) (h : Heap) (b : Builtin) (args : List Value)
    (kws : List (Name × Value)) : KR env h (applyBuiltin env h b args kws) := by
  unfold applyBuiltin
  split
  · next r hr => exact hL.builtin env h b args kws r hr
  · repeat kr_step

theorem appendItem_keeps (env : Env) (h : Heap) (a : Nat) (v : Value) : KH env h (appendItem env h a v) := by
  unfold appendItem
  split
  · next r hr => exact hL.append env h a v r hr
  · repeat kr_step

theorem foldl_append_keeps (env : Env) (a : Nat) :
    ∀ (ys : List Value) (h : Heap), KH env h (ys.foldlM (fun h y => appendItem env h a y) h)
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
    KH env h (setSlice env h o lo hi vals) := by
  unfold setSlice
  repeat (first | kr_step | (next r hr => exact hL.setSlice _ _ _ _ _ _ r hr))

theorem setAttr_keeps (env : Env) (h : Heap) (o : Value) (f : Name) (v : Value) :
    KH env h (setAttr env h o f v) := by
  unfold setAttr
  repeat (first
    | (refine kh_bind (coerceWith_keeps hL _ _ _ _ _) fun _ _ _ => ?_)
    | (exact kh_ok (keeps_set' (by assumption) _ _ fun c _ _ eo _ hl => by
        cases eo; rw [List.length_set]; exact c _ _ _ _ (by assumption) hl))
    | kr_step)

theorem seqBinop_keeps (env : Env) (h : Heap) (op : BinOp) (x y : Value) (r : Res (Value × Heap))
    (hr : seqBinop env h op x y = some r) : KR env h r := by
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
    (hr : seqAugAdd h op x y = some r) : KR env h r := by
  unfold seqAugAdd at hr
  split at hr
  · split at hr
    · simp only [Option.some.injEq] at hr; subst hr
      repeat kr_step
    · cases hr
  · cases hr

theorem applyDataclass_keeps (env : Env) (h : Heap) (ty : Name) (args : List Value)
    (kws : List (Name × Value)) : KR env h (applyDataclass env h ty args kws) := by
  unfold applyDataclass
  repeat (first
    | (refine kr_bindvE fun _ _ => ?_)
    | (exact kr_ok _ (keeps_alloc _ _ (by
        intro _ _ eo ffs hl; cases eo
        rw [except_mapM_length _ _ (by assumption), ctorFields_length (by assumption)]
        simp_all)))
    | kr_step)

theorem applyMethod_keeps (env : Env) (h : Heap) (self : Value) (m : Name) (args : List Value) :
    KR env h (applyMethod env h self m args) := by
  unfold applyMethod
  split
  · next r hr => exact hL.method env h self m args r hr
  · repeat (first | exact kr_of_kh _ (appendItem_keeps hL _ _ _ _) | exact kr_of_kh _ (foldl_append_keeps hL _ _ _ _) | kr_step)

theorem getSlice_keeps (c : Name) (h : Heap) (o : Value) (lo hi : Option Value) :
    KR env h (getSlice c h o lo hi) := by
  unfold getSlice
  repeat kr_step

end lib

end core

/-! ## The SSZ library -/

section ssz

open Ssz

theorem defaultList_keeps (env : Env) (d : Nat) (hP : ∀ h t, KR env h (defaultOf env d h t)) :
    ∀ (ts : List SszTy) (h : Heap), KR env h (defaultList env d h ts)
  | [], h => by rw [defaultList]; exact kr_ok _ (keeps_refl h)
  | t :: ts, h => by
    rw [defaultList]
    refine kr_bind (hP h t) fun y h1 hk1 => ?_
    refine kr_bind (fun z h2 e => keeps_trans hk1 (defaultList_keeps env d hP ts h1 z h2 e)) fun ys h2 hk2 => ?_
    exact kr_ok _ hk2

theorem defaultList_length (env : Env) (d : Nat) : ∀ (ts : List SszTy) (h : Heap) (ys : List Value) (h' : Heap),
    defaultList env d h ts = .ok (ys, h') → ys.length = ts.length
  | [], h, ys, h', e => by rw [defaultList] at e; cases e; rfl
  | t :: ts, h, ys, h', e => by
    rw [defaultList] at e
    obtain ⟨⟨y, h1⟩, -, e⟩ := except_bind_ok e
    dsimp only at e
    obtain ⟨⟨zs, h2⟩, e2, e⟩ := except_bind_ok e
    cases e
    simp [defaultList_length env d ts h1 zs h2 e2]

theorem build_length (env : Env) : ∀ (ps : List ((Name × SszTy) × Option Value)) (h : Heap)
    (ys : List Value) (h' : Heap), construct.build env h ps = .ok (ys, h') → ys.length = ps.length
  | [], h, ys, h', e => by simp only [construct.build] at e; cases e; rfl
  | ((_, ft), gv) :: rest, h, ys, h', e => by
    simp only [construct.build] at e
    cases gv <;> dsimp only at e
    all_goals
      obtain ⟨⟨v, h1⟩, -, e⟩ := except_bind_ok e
      dsimp only at e
      obtain ⟨⟨vs, h2⟩, e2, e⟩ := except_bind_ok e
      cases e
      simp [build_length env rest h1 vs h2 e2]

theorem defaultOf_keeps (env : Env) : ∀ (d : Nat) (h : Heap) (t : SszTy), KR env h (defaultOf env d h t)
  | 0, h, t => by rw [defaultOf.eq_def]; exact kr_err _ _
  | d + 1, h, t => by
    have hQ := defaultList_keeps env d (defaultOf_keeps env d)
    rw [defaultOf.eq_def]; dsimp only
    repeat (first
      | (refine kr_bindE (hQ _ _) fun _ h1 e hk1 => ?_; exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _ (by
          first | objok | (intro _ _ eo ffs hl; cases eo; rw [defaultList_length _ _ _ _ _ _ e]; simp_all)))))
      | kr_step)

theorem coerceAll_keeps (env : Env) (d : Nat) (hP : ∀ f h t v, KR env h (coerceH env f d h t v)) :
    ∀ (xs : List Value) (h : Heap) (e : SszTy), KR env h (coerceAll env d h e xs)
  | [], h, e => by rw [coerceAll]; exact kr_ok _ (keeps_refl h)
  | x :: xs, h, e => by
    rw [coerceAll]
    refine kr_bind (hP false h e x) fun y h1 hk1 => ?_
    refine kr_bind (fun z h2 hz => keeps_trans hk1 (coerceAll_keeps env d hP xs h1 e z h2 hz)) fun ys h2 hk2 => ?_
    exact kr_ok _ hk2

theorem newList_keeps (env : Env) (d : Nat) (hP : ∀ f h t v, KR env h (coerceH env f d h t v))
    (h : Heap) (k : ListKind) (e : SszTy) (l : Option Nat) (xs : List Value) :
    KR env h (newList env d h k e l xs) := by
  rw [newList]
  refine kr_bindv fun _ => ?_
  have fin : ∀ ys h1, Keeps env h h1 → KR env h ((fun (p : List Value × Heap) =>
      match h1.alloc (.list k e l p.1) with | (a, h2) => (pure (Value.ref a, h2) : Res (Value × Heap))) (ys, h1)) := by
    intro ys h1 hk1; exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _ (by objok)))
  dsimp only
  split
  · refine kr_bind ?_ fun ys h1 hk1 => kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _ (by objok)))
    intro y h' hr
    cases hc : xs.mapM coerceByte with
    | error e => rw [hc] at hr; cases hr
    | ok w => rw [hc] at hr; cases hr; exact keeps_refl h
  · exact kr_bind (coerceAll_keeps env d hP xs h e) fun ys h1 hk1 => kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _ (by objok)))

theorem coerceH_keeps (env : Env) : ∀ (d : Nat) (f : Bool) (h : Heap) (t : SszTy) (v : Value),
    KR env h (coerceH env f d h t v)
  | 0, f, h, t, v => by rw [coerceH.eq_def]; exact kr_err _ _
  | d + 1, f, h, t, v => by
    have hN := newList_keeps env d (coerceH_keeps env d)
    rw [coerceH.eq_def]; dsimp only
    repeat (first | exact hN _ _ _ _ _ | kr_step)

theorem build_keeps (env : Env) :
    ∀ (ps : List ((Name × SszTy) × Option Value)) (h : Heap), KR env h (construct.build env h ps)
  | [], h => by simp only [construct.build]; exact kr_ok _ (keeps_refl h)
  | ((_, ft), gv) :: rest, h => by
    simp only [construct.build]
    have tail : ∀ y h1, Keeps env h h1 → KR env h (do
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
    KR env h (construct env h t args kws) := by
  unfold construct
  repeat (first
    | exact newList_keeps env _ (coerceH_keeps env _) _ _ _ _ _
    | exact defaultOf_keeps env _ _ _
    | exact kr_err _ _
    | (refine kr_bindE (build_keeps env _ _) fun _ h1 e hk1 => ?_; exact kr_ok _ (keeps_trans hk1 (keeps_alloc h1 _ (by
        intro _ _ eo ffs hl; cases eo
        rw [build_length env _ _ _ _ e, List.length_zip, ctorFields_length (by assumption)]
        simp_all))))
    | (refine kr_bindvE fun _ _ => ?_)
    | (intro _ _ hr; first
        | (have := newList_keeps env depthBound (coerceH_keeps env _) _ _ _ _ _ _ _ (by
            revert hr; split <;> intro hr <;> first | exact hr | cases hr); exact this))
    | kr_step)

theorem byteListAdd_keeps (env : Env) (h : Heap) (op : BinOp) (x y : Value) (r : Res (Value × Heap))
    (hr : byteListAdd env h op x y = some r) : KR env h r := by
  unfold byteListAdd at hr
  dsimp only at hr
  split at hr
  · simp only [Option.some.injEq] at hr; subst hr; repeat kr_step
  · simp only [Option.some.injEq] at hr; subst hr; repeat kr_step
  · cases hr

theorem binopH_keeps (env : Env) (h : Heap) (op : BinOp) (x y : Value) (r : Res (Value × Heap))
    (hr : binopH env h op x y = some r) : KR env h r := by
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
    (r : Res (Value × Heap)) (hr : method env h self m args = some r) : KR env h r := by
  unfold method at hr
  revert hr
  repeat (first
    | (intro hr; simp only [Option.some.injEq] at hr; subst hr;
        first | exact deepCopy_keeps _ _ _ | exact defaultOf_keeps env _ _ _ | (repeat kr_step))
    | (intro hr; cases hr)
    | split)

theorem coerceByte_kr (h : Heap) (v : Value) : KR env h ((·, h) <$> coerceByte v) := by
  intro y h' hr
  cases hc : coerceByte v with
  | error e => rw [hc] at hr; cases hr
  | ok w => rw [hc] at hr; cases hr; exact keeps_refl h

theorem append_keeps (env : Env) (h : Heap) (a : Nat) (v : Value) (r : Res Heap)
    (hr : append env h a v = some r) : KH env h r := by
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
        exact kh_ok (keeps_set hk1 _ _ (by objok))
      · refine kh_bind (coerceH_keeps env _ _ _ _ _) fun v' h1 hk1 => ?_
        refine kh_bindv fun _ => ?_
        exact kh_ok (keeps_set hk1 _ _ (by objok))
  · cases hr

theorem sszSetSlice_keeps (env : Env) (h : Heap) (a lo hi : Nat) (ins : List Value) (r : Res Heap)
    (hr : Ssz.setSlice env h a lo hi ins = some r) : KH env h r := by
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
        exact kh_ok (keeps_set hk1 _ _ (by objok))
    · refine kh_bind (coerceAll_keeps env _ (coerceH_keeps env _) _ _ _) fun v' h1 hk1 => ?_
      refine kh_bindv fun _ => ?_
      exact kh_ok (keeps_set hk1 _ _ (by objok))
  · cases hr

theorem sszBuiltin_keeps (env : Env) (h : Heap) (b : Builtin) (args : List Value) (kws : List (Name × Value))
    (r : Res (Value × Heap)) (hr : Ssz.builtin env h b args kws = some r) : KR env h r := by
  unfold Ssz.builtin at hr
  revert hr
  repeat (first
    | (intro hr; simp only [Option.some.injEq] at hr; subst hr; repeat kr_step)
    | (intro hr; cases hr)
    | split)

theorem sszCoerce_keeps (env : Env) (f : Bool) (h : Heap) (t : SszTy) (v : Value) (r : Res (Value × Heap))
    (hr : Ssz.coerce env f h t v = some r) : KR env h r := by
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
def KG (env : Env) {β : Type} (get : β → Heap) (h : Heap) (r : Res β) : Prop := ∀ p, r = .ok p → Keeps env h (get p)

theorem kg_err {β : Type} (get : β → Heap) (h : Heap) (e : SpecError) : KG env get h (.error e) := by
  intro p hr; cases hr

theorem kg_pure {β : Type} {get : β → Heap} {h : Heap} (p : β) (hk : Keeps env h (get p)) :
    KG env get h (pure p) := by
  intro q hr; cases hr; exact hk

theorem kg_bind {β γ : Type} {ga : β → Heap} {gb : γ → Heap} {h : Heap} {a : Res β} {f : β → Res γ}
    (ha : KG env ga h a) (hf : ∀ p, Keeps env h (ga p) → KG env gb h (f p)) : KG env gb h (a >>= f) := by
  intro q hr
  cases a with
  | error e => cases hr
  | ok p => exact hf p (ha p rfl) q hr

theorem kg_bindv {α γ : Type} {gb : γ → Heap} {h : Heap} {a : Res α} {f : α → Res γ}
    (hf : ∀ x, KG env gb h (f x)) : KG env gb h (a >>= f) := by
  intro q hr
  cases a with
  | error e => cases hr
  | ok x => exact hf x q hr

theorem kg_mono {β : Type} {get : β → Heap} {h h1 : Heap} {r : Res β} (hk : Keeps env h h1)
    (hr : KG env get h1 r) : KG env get h r := fun p e => keeps_trans hk (hr p e)

theorem kg_of_kr {α : Type} {h : Heap} {r : Res (α × Heap)} (hr : KR env h r) : KG env Prod.snd h r :=
  fun p e => by obtain ⟨x, h'⟩ := p; exact hr x h' e

theorem foldlM_keeps {α : Type} (f : Heap → α → Res Heap) (hf : ∀ h x, KH env h (f h x)) :
    ∀ (xs : List α) (h : Heap), KH env h (xs.foldlM f h)
  | [], h => by simp only [List.foldlM]; exact kh_ok (keeps_refl h)
  | x :: xs, h => by
    simp only [List.foldlM]
    intro h' hr
    cases ha : f h x with
    | error e => rw [ha] at hr; cases hr
    | ok h1 => rw [ha] at hr; exact keeps_trans (hf h x h1 ha) (foldlM_keeps f hf xs h1 h' hr)

theorem kg_of_kh {h : Heap} {r : Res Heap} (hr : KH env h r) : KG env id h r := fun p e => hr p e

/-- A step of a `KG` goal. The heads of binds use the hypotheses `hX` in the context. -/
syntax "kg_step" : tactic
macro_rules
  | `(tactic| kg_step) => `(tactic| first
    | exact kg_err _ _ _
    | (exact kg_pure _ (by assumption))
    | (exact kg_pure _ (keeps_trans (by assumption) (keeps_alloc _ _ (by objok))))
    | (exact kg_pure _ (keeps_refl _))
    | (refine kg_bindv fun _ => ?_)
    | (dsimp only)
    | split)

section interp

variable [LibModel] (env : Env) (hL : LibKeeps)

/-- Each function that lowers the fuel keeps the heap at fuel `n`. -/
structure Base (n : Nat) : Prop where
  expr : ∀ L h e, KG env Prod.snd h (evalExpr env n L h e)
  items : ∀ L h t ifs rest elt st src i, KG env (fun p => p.2.2) h (compItems env n L h t ifs rest elt st src i)
  fn : ∀ ps body base vs kws h, KG env Prod.snd h (callFn env n ps body base vs kws h)
  filter : ∀ f xs h, KG env Prod.snd h (filterItems env n f xs h)
  map : ∀ f xs h, KG env Prod.snd h (mapItems env n f xs h)
  target : ∀ L h t v, KG env Prod.snd h (assignTarget env n L h t v)
  stmt : ∀ L h s, KG env (fun p => p.2.2) h (execStmt env n L h s)
  forLoop : ∀ L h t src i body, KG env (fun p => p.2.2) h (execFor env n L h t src i body)
  whileLoop : ∀ L h c body, KG env (fun p => p.2.2) h (execWhile env n L h c body)

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

theorem opt_keeps (L : Locals) (h : Heap) (o : Option Expr) : KG env Prod.snd h (evalOpt env n L h o) := by
  cases o with
  | none => rw [evalOpt]; exact kg_pure _ (keeps_refl h)
  | some e =>
    rw [evalOpt]
    exact kg_bind (B.expr L h e) fun p hp => kg_pure _ hp

theorem list_keeps (L : Locals) : ∀ (es : List Expr) (h : Heap), KG env Prod.snd h (evalList env n L h es)
  | [], h => by rw [evalList]; exact kg_pure _ (keeps_refl h)
  | e :: es, h => by
    rw [evalList]
    refine kg_bind (B.expr L h e) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    exact kg_bind (kg_mono hp (list_keeps L es h1)) fun q hq => kg_pure _ hq

theorem args_keeps (L : Locals) : ∀ (as : List Arg) (h : Heap),
    KG env (fun p => p.2.2) h (evalArgs env n L h as)
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
    KG env Prod.snd h (evalCmp env n L h x rest)
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
    KG env Prod.snd h (evalBoolOp env n L h op es)
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

theorem ifs_keeps (L : Locals) : ∀ (cs : List Expr) (h : Heap), KG env Prod.snd h (evalIfs env n L h cs)
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
    KG env (fun p => p.2.2) h (compLoop env n L h gs elt st) := by
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

theorem filter_lift : ∀ (f : Value) (xs : List Value) (h : Heap), KG env Prod.snd h (filterItems env n f xs h) :=
  B.filter

include hL in
theorem call_keeps (f : Value) (vs : List Value) (kws : List (Name × Value)) (h : Heap) :
    KG env Prod.snd h (callValue env n f vs kws h) := by
  rw [callValue.eq_def]
  all_goals repeat (first
    | exact B.fn _ _ _ _ _ _
    | exact kg_of_kr (applyBuiltin_keeps hL _ _ _ _ _)
    | exact kg_of_kr (hL.construct _ _ _ _ _)
    | exact kg_of_kr (applyDataclass_keeps hL _ _ _ _ _)
    | exact kg_of_kr (applyMethod_keeps hL _ _ _ _ _)
    | (refine kg_bind (B.filter _ _ _) fun p hp => kg_pure _ hp)
    | (refine kg_bind (B.map _ _ _) fun p hp => ?_; exact kg_bindv fun _ => kg_pure _ (keeps_trans hp (keeps_alloc _ _ (by objok))))
    | (simp only [frame_eq])
    | kg_step)

theorem targets_keeps (L : Locals) : ∀ (ts : List Target) (vs : List Value) (h : Heap),
    KG env Prod.snd h (assignTargets env n L h ts vs)
  | t :: ts, v :: vs, h => by
    rw [assignTargets]
    refine kg_bind (B.target L h t v) fun p hp => ?_
    obtain ⟨L1, h1⟩ := p
    exact kg_mono hp (targets_keeps L1 ts vs h1)
  | [], _, h => by rw [assignTargets]; exact kg_pure _ (keeps_refl h)
  | _ :: _, [], h => by rw [assignTargets]; exact kg_pure _ (keeps_refl h)

theorem all_keeps : ∀ (L : Locals) (ts : List Target) (v : Value) (h : Heap),
    KG env Prod.snd h (assignAll env n L h ts v)
  | L, [], v, h => by rw [assignAll]; exact kg_pure _ (keeps_refl h)
  | L, t :: ts, v, h => by
    rw [assignAll]
    refine kg_bind (B.target L h t v) fun p hp => ?_
    obtain ⟨L1, h1⟩ := p
    exact kg_mono hp (all_keeps L1 ts v h1)

theorem block_keeps : ∀ (L : Locals) (ss : List Stmt) (h : Heap),
    KG env (fun p => p.2.2) h (execBlock env n L h ss)
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

theorem expr_succ (L : Locals) (h : Heap) (e : Expr) : KG env Prod.snd h (evalExpr env (n + 1) L h e) := by
  rw [evalExpr.eq_def]
  dsimp only
  have h0 := keeps_refl (env := env) h
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
    | (refine kg_bind (kg_mono (keeps_trans (by assumption) (keeps_alloc _ _ (by objok)))
          (kg_of_kh (foldlM_keeps _ (fun _ kv => by obtain ⟨_, _⟩ := kv; exact setItem_keeps hL _ _ _ _ _) _ _)))
          fun p hp => kg_pure _ hp)
    | (exact kg_pure _ (keeps_trans (by assumption) (keeps_alloc _ _ (by objok))))
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
    | (exact kg_pure _ (keeps_trans (by assumption) (keeps_alloc _ _ (by objok))))
    | kg_step)

theorem items_succ (L : Locals) (h : Heap) (t : Target) (ifs : List Expr) (rest : List Comprehension)
    (elt : Expr) (st : Option Bool) (src : IterSrc) (i : Nat) :
    KG env (fun p => p.2.2) h (compItems env (n + 1) L h t ifs rest elt st src i) := by
  rw [compItems]
  have h0 := keeps_refl (env := env) h
  refine kg_bindv fun ox => ?_
  split
  · exact kg_pure _ h0
  · refine kg_bind (B.target L h t _) fun p hp => ?_
    obtain ⟨L1, h1⟩ := p
    refine kg_bind (kg_mono hp (ifs_keeps B L1 ifs h1)) fun q hq => ?_
    obtain ⟨keep, h2⟩ := q
    dsimp only
    have tail : ∀ r : List Value × Bool × Heap, Keeps env h r.2.2 →
        KG env (fun p => p.2.2) h (if r.2.1 = true then pure (r.1, true, r.2.2) else do
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
    (kws : List (Name × Value)) (h : Heap) : KG env Prod.snd h (callFn env (n + 1) ps body base vs kws h) := by
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

theorem filter_succ (f : Value) : ∀ (xs : List Value) (h : Heap), KG env Prod.snd h (filterItems env (n + 1) f xs h)
  | [], h => by rw [filterItems]; exact kg_pure _ (keeps_refl h)
  | x :: xs, h => by
    rw [filterItems]
    refine kg_bind (call_keeps hL B _ _ _ h) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    refine kg_bindv fun keep => ?_
    refine kg_bind (kg_mono hp (filter_succ f xs h1)) fun q hq => ?_
    exact kg_pure _ hq

theorem map_succ (f : Value) : ∀ (xs : List Value) (h : Heap), KG env Prod.snd h (mapItems env (n + 1) f xs h)
  | [], h => by rw [mapItems]; exact kg_pure _ (keeps_refl h)
  | x :: xs, h => by
    rw [mapItems]
    refine kg_bind (call_keeps hL B _ _ _ h) fun p hp => ?_
    obtain ⟨v, h1⟩ := p
    refine kg_bind (kg_mono hp (map_succ f xs h1)) fun q hq => ?_
    exact kg_pure _ hq

theorem target_succ (L : Locals) (h : Heap) (t : Target) (v : Value) :
    KG env Prod.snd h (assignTarget env (n + 1) L h t v) := by
  rw [assignTarget.eq_def]; dsimp only
  have h0 := keeps_refl (env := env) h
  cases t
  repeat' kg_stmt

theorem stmt_succ (L : Locals) (h : Heap) (st : Stmt) :
    KG env (fun p => p.2.2) h (execStmt env (n + 1) L h st) := by
  rw [execStmt.eq_def]; dsimp only
  have h0 := keeps_refl (env := env) h
  cases st
  repeat' kg_stmt

theorem for_succ (L : Locals) (h : Heap) (t : Target) (src : IterSrc) (i : Nat) (body : List Stmt) :
    KG env (fun p => p.2.2) h (execFor env (n + 1) L h t src i body) := by
  rw [execFor]
  have h0 := keeps_refl (env := env) h
  repeat kg_stmt

theorem while_succ (L : Locals) (h : Heap) (c : Expr) (body : List Stmt) :
    KG env (fun p => p.2.2) h (execWhile env (n + 1) L h c body) := by
  rw [execWhile]
  have h0 := keeps_refl (env := env) h
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
/-- A call keeps the field count of each container. -/
theorem callFn_cw {n : Nat} {ps : Params} {body : ClosureBody} {base : Locals} {vs : List Value}
    {kws : List (Name × Value)} {h h' : Heap} {v : Value}
    (hr : callFn env n ps body base vs kws h = .ok (v, h')) (hc : CW env h) : CW env h' :=
  (base_all env hL n).fn ps body base vs kws h (v, h') hr hc

end interp

end SpecLean.ContRun
