import SpecLean.Gen.Readable
import SpecLean.Validation.DecodeExtra
import SpecLean.Validation.Where

/-!
# `hash_tree_root` as an oracle on both sides

The interpreter calls the oracle field `sha.hashTreeRoot` on a heap value. The readable Lean calls
the oracle `Spec.hashTreeRoot` on its own encoding of the value, in a new heap (`htrObj`). The
proofs treat both as one oracle and assume one property of it (`OracleHtr`): it reads only the
content of a value (`Bis`). So a heap value and the encoding of its readable value get one root
(`htr_bridge`). `Htr.root` is only the executable oracle of the runner: `htrRoot_ext` and
`root_noOof` show that it has the assumed properties.

The decoders do not check the number of fields of a container. `Shaped` says that each
container object of the heap has the fields of its class, as every object that Python builds
does.
-/

namespace SpecLean.Validation.HtrBridge

open SpecLean SpecLean.Rd SpecLean.Rd.Gen

/-! ## The content of a value -/

/-- `v` in `h` and `v'` in `h'` have the same content to depth `d`: equal values that are not
references, and objects of the same class with items of the same content. -/
def Bis : Nat → Heap → Value → Heap → Value → Prop
  | 0, _, .ref _, _, .ref _ => True
  | d + 1, h, .ref a, h', .ref a' =>
    match h.objs a, h'.objs a' with
    | some (.container ty fs), some (.container ty' fs') =>
      ty = ty' ∧ fs.length = fs'.length ∧
        ∀ (i : Nat) x x', fs[i]? = some x → fs'[i]? = some x' → Bis d h x h' x'
    | some (.list k e l xs), some (.list k' e' l' xs') =>
      k = k' ∧ e = e' ∧ l = l' ∧ xs.length = xs'.length ∧
        ∀ (i : Nat) x x', xs[i]? = some x → xs'[i]? = some x' → Bis d h x h' x'
    | _, _ => False
  | _, _, .ref _, _, _ => False
  | _, _, _, _, .ref _ => False
  | _, _, v, _, v' => v = v'

theorem Bis_scalar {d : Nat} {h h' : Heap} {v v' : Value} (hv : ∀ a, v ≠ .ref a)
    (hb : Bis d h v h' v') : v' = v := by
  cases v <;> cases v' <;> cases d <;> simp_all [Bis]

theorem Bis_ref {d : Nat} {h h' : Heap} {a : Nat} {v' : Value} (hb : Bis d h (.ref a) h' v') :
    ∃ a', v' = .ref a' := by
  cases v' <;> cases d <;> simp_all [Bis]

theorem Bis_self_scalar (d : Nat) (h h' : Heap) {v : Value} (hv : ∀ a, v ≠ .ref a) :
    Bis d h v h' v := by
  cases v <;> cases d <;> simp_all [Bis]

theorem Bis_symm : ∀ d h v h' v', Bis d h v h' v' → Bis d h' v' h v := by
  intro d
  induction d with
  | zero =>
    intro h v h' v' hb
    by_cases hv : ∃ a, v = .ref a
    · obtain ⟨a, rfl⟩ := hv; obtain ⟨a', rfl⟩ := Bis_ref hb; simp [Bis]
    · rw [Bis_scalar (fun a e => hv ⟨a, e⟩) hb]; exact Bis_self_scalar 0 h' h (fun a e => hv ⟨a, e⟩)
  | succ d ih =>
    intro h v h' v' hb
    by_cases hv : ∃ a, v = .ref a
    · obtain ⟨a, rfl⟩ := hv
      obtain ⟨a', rfl⟩ := Bis_ref hb
      simp only [Bis] at hb ⊢
      split at hb
      · rename_i ty fs ty' fs' ho ho'
        obtain ⟨rfl, hl, hi⟩ := hb
        rw [ho, ho']
        exact ⟨rfl, hl.symm, fun i x' x hx' hx => ih h x h' x' (hi i x x' hx hx')⟩
      · rename_i k e l xs k' e' l' xs' ho ho'
        obtain ⟨rfl, rfl, rfl, hl, hi⟩ := hb
        rw [ho, ho']
        exact ⟨rfl, rfl, rfl, hl.symm, fun i x' x hx' hx => ih h x h' x' (hi i x x' hx hx')⟩
      · exact hb.elim
    · rw [Bis_scalar (fun a e => hv ⟨a, e⟩) hb]
      exact Bis_self_scalar _ h' h (fun a e => hv ⟨a, e⟩)

theorem Bis_trans : ∀ d h1 v1 h2 v2 h3 v3, Bis d h1 v1 h2 v2 → Bis d h2 v2 h3 v3 →
    Bis d h1 v1 h3 v3 := by
  intro d
  induction d with
  | zero =>
    intro h1 v1 h2 v2 h3 v3 b12 b23
    by_cases hv : ∃ a, v1 = .ref a
    · obtain ⟨a, rfl⟩ := hv; obtain ⟨a2, rfl⟩ := Bis_ref b12; obtain ⟨a3, rfl⟩ := Bis_ref b23
      simp [Bis]
    · have e2 := Bis_scalar (fun a e => hv ⟨a, e⟩) b12
      subst e2
      rw [Bis_scalar (fun a e => hv ⟨a, e⟩) b23]
      exact Bis_self_scalar 0 h1 h3 (fun a e => hv ⟨a, e⟩)
  | succ d ih =>
    intro h1 v1 h2 v2 h3 v3 b12 b23
    by_cases hv : ∃ a, v1 = .ref a
    · obtain ⟨a1, rfl⟩ := hv
      obtain ⟨a2, rfl⟩ := Bis_ref b12
      obtain ⟨a3, rfl⟩ := Bis_ref b23
      simp only [Bis] at b12 b23 ⊢
      split at b12
      · rename_i ty fs ty' fs' ho1 ho2
        obtain ⟨rfl, hl, hi⟩ := b12
        rw [ho2] at b23
        split at b23
        · rename_i ty2 fs2 ty3 fs3 hc ho3
          cases hc
          obtain ⟨rfl, hl', hi'⟩ := b23
          rw [ho1, ho3]
          refine ⟨rfl, hl.trans hl', fun i x z hx hz => ?_⟩
          obtain ⟨y, hy⟩ : ∃ y, fs'[i]? = some y :=
            ⟨fs'[i]'(by have := (List.getElem?_eq_some_iff.mp hx).1; omega),
              List.getElem?_eq_getElem _⟩
          exact ih _ _ _ _ _ _ (hi i x y hx hy) (hi' i y z hy hz)
        · simp at *
        · exact b23.elim
      · rename_i k e l xs k' e' l' xs' ho1 ho2
        obtain ⟨rfl, rfl, rfl, hl, hi⟩ := b12
        rw [ho2] at b23
        split at b23
        · simp at *
        · rename_i k2 e2 l2 xs2 k3 e3 l3 xs3 hc ho3
          cases hc
          obtain ⟨rfl, rfl, rfl, hl', hi'⟩ := b23
          rw [ho1, ho3]
          refine ⟨rfl, rfl, rfl, hl.trans hl', fun i x z hx hz => ?_⟩
          obtain ⟨y, hy⟩ : ∃ y, xs'[i]? = some y :=
            ⟨xs'[i]'(by have := (List.getElem?_eq_some_iff.mp hx).1; omega),
              List.getElem?_eq_getElem _⟩
          exact ih _ _ _ _ _ _ (hi i x y hx hy) (hi' i y z hy hz)
        · exact b23.elim
      · exact b12.elim
    · have e2 := Bis_scalar (fun a e => hv ⟨a, e⟩) b12
      subst e2
      rw [Bis_scalar (fun a e => hv ⟨a, e⟩) b23]
      exact Bis_self_scalar _ h1 h3 (fun a e => hv ⟨a, e⟩)

/-- `mapM` of two related lists with functions that agree on related items. -/
theorem mapM_rel {α : Type} {f g : Value → Res α} {R : Value → Value → Prop} :
    ∀ {xs ys : List Value}, xs.length = ys.length →
      (∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → R x y) → (∀ x y, R x y → f x = g y) →
      xs.mapM f = ys.mapM g
  | [], [], _, _, _ => rfl
  | x :: xs, y :: ys, hl, hr, hfg => by
    simp only [List.mapM_cons]
    rw [hfg x y (hr 0 x y rfl rfl),
      mapM_rel (by simpa using hl) (fun i a b ha hb => hr (i + 1) a b ha hb) hfg]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- A function that reads no object agrees on items with the same content. -/
theorem scalar_fn_rel {α : Type} (f : Value → α) (hf : ∀ a b, f (.ref a) = f (.ref b))
    {d : Nat} {h h' : Heap} {x x' : Value} (hb : Bis d h x h' x') : f x = f x' := by
  by_cases hx : ∃ a, x = .ref a
  · obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := Bis_ref hb
    exact hf a a'
  · rw [Bis_scalar (fun a e => hx ⟨a, e⟩) hb]

/-- `hash_tree_root` reads only the content of a value. -/
theorem root_bis (H : Htr.Hasher) :
    ∀ d h v h' v', Bis d h v h' v' → Htr.root H h d v = Htr.root H h' d v' := by
  intro d
  induction d with
  | zero => intro h v h' v' _; rfl
  | succ d ih =>
    intro h v h' v' hb
    by_cases hv : ∃ a, v = .ref a
    · obtain ⟨a, rfl⟩ := hv
      obtain ⟨a', rfl⟩ := Bis_ref hb
      simp only [Bis] at hb
      simp only [Htr.root]
      split at hb
      · rename_i ty fs ty' fs' ho ho'
        obtain ⟨rfl, hl, hi⟩ := hb
        rw [ho, ho']
        simp only
        rw [mapM_rel hl hi (fun x y hxy => ih h x h' y hxy)]
      · rename_i k e l xs k' e' l' xs' ho ho'
        obtain ⟨rfl, rfl, rfl, hl, hi⟩ := hb
        rw [ho, ho']
        simp only
        have hbit : xs.mapM Htr.bitOf = xs'.mapM Htr.bitOf :=
          mapM_rel hl hi fun x y hxy => scalar_fn_rel Htr.bitOf (fun _ _ => rfl) hxy
        have hpack : Htr.packBasic xs = Htr.packBasic xs' := by
          unfold Htr.packBasic
          congr 1
          exact (mapM_rel hl hi fun x y hxy => scalar_fn_rel
            (fun x => match Htr.basicBytes x with
              | some b => (Except.ok b : Res (List UInt8))
              | none => .error .unsupported) (fun _ _ => rfl) hxy)
        have hroots : xs.mapM (Htr.root H h d) = xs'.mapM (Htr.root H h' d) :=
          mapM_rel hl hi fun x y hxy => ih h x h' y hxy
        rw [hbit, hpack, hroots, hl]
      · exact hb.elim
    · rw [Bis_scalar (fun a e => hv ⟨a, e⟩) hb]
      cases v with
      | ref a => exact absurd ⟨a, rfl⟩ hv
      | lib lv => cases lv <;> rfl
      | _ => rfl

/-! ## `hash_tree_root` never runs out of fuel -/

/-- A result that is not `outOfFuel`. -/
def NoOof {α : Type} (r : Res α) : Prop := r ≠ .error .outOfFuel

theorem noOof_ok {α : Type} (a : α) : NoOof (.ok a : Res α) := fun e => by cases e

theorem noOof_pure {α : Type} (a : α) : NoOof (pure a : Res α) := fun e => by cases e

theorem noOof_bind {α β : Type} {x : Res α} {f : α → Res β} (hx : NoOof x)
    (hf : ∀ a, NoOof (f a)) : NoOof (x >>= f) := by
  cases x with
  | error e => intro he; exact hx (by simpa using he)
  | ok a => simpa using hf a

theorem noOof_mapM {α β : Type} {f : α → Res β} (hf : ∀ a, NoOof (f a)) :
    ∀ xs : List α, NoOof (xs.mapM f)
  | [] => by simp [NoOof]
  | x :: xs => by
    simp only [List.mapM_cons]
    exact noOof_bind (hf x) fun _ => noOof_bind (noOof_mapM hf xs) fun _ => noOof_ok _

theorem noOof_merkleize (H : Htr.Hasher) (cs : List (List UInt8)) (l : Option Nat) :
    NoOof (Htr.merkleize H cs l) := by
  unfold Htr.merkleize NoOof
  split
  · split <;> simp
  · simp

theorem noOof_bitOf (v : Value) : NoOof (Htr.bitOf v) := by
  unfold Htr.bitOf NoOof; split <;> simp

theorem noOof_packBasic (xs : List Value) : NoOof (Htr.packBasic xs) := by
  unfold Htr.packBasic
  refine noOof_bind (noOof_mapM (fun x => ?_) xs) fun _ => noOof_ok _
  unfold NoOof; split <;> simp

/-- `hash_tree_root` fails only with `unsupported` or `SSZValueError`, never `outOfFuel`. -/
theorem root_noOof (H : Htr.Hasher) : ∀ d h v, NoOof (Htr.root H h d v) := by
  intro d
  induction d with
  | zero => intro h v; simp [Htr.root, NoOof]
  | succ d ih =>
    intro h v
    simp only [Htr.root]
    repeat' (first
      | exact noOof_ok _
      | exact noOof_pure _
      | exact noOof_merkleize _ _ _
      | exact noOof_packBasic _
      | exact noOof_mapM (ih h) _
      | exact noOof_mapM noOof_bitOf _
      | (simp [NoOof]; done)
      | refine noOof_bind ?_ fun _ => ?_
      | split)

/-! ## The oracle -/

/-- The assumptions on the `hash_tree_root` oracle, stated once.

- `same`: the readable Lean calls the oracle of the interpreter.
- `ext`: the oracle reads only the content of a value. Two heap values with the same content
  have the same root. This is weaker than "the same decoded value": a decoder that forgets
  part of a value would make that version unsatisfiable.
- `noOof`: the oracle never runs out of fuel, and `len`: a root has 32 bytes. -/
structure OracleHtr [Spec] (sha : Oracle) : Prop where
  same : Spec.hashTreeRoot = sha.hashTreeRoot
  ext : ∀ h v h' v', Bis 64 h v h' v' → sha.hashTreeRoot h v = sha.hashTreeRoot h' v'
  noOof : ∀ h v, sha.hashTreeRoot h v ≠ .error .outOfFuel
  len : ∀ h v r, sha.hashTreeRoot h v = .ok r → r.length = 32

/-- The executable oracle `Htr.root` reads only the content of a value. -/
theorem htrRoot_ext (H : Htr.Hasher) :
    ∀ h v h' v', Bis 64 h v h' v' → Htr.root H h 64 v = Htr.root H h' 64 v' :=
  root_bis H 64

/-- The interpreter's oracle call on a heap value against the readable call on an object whose
encoding has the same content. -/
theorem htrObj_bridge [Spec] {sha : Oracle} (ho : OracleHtr sha) {h : Heap} {v : Value}
    {o : SszObj} (hb : Bis 64 h v (o.enc Heap.empty).2 (o.enc Heap.empty).1) :
    erase (sha.hashTreeRoot h v) = htrObj o := by
  unfold htrObj
  rw [ho.same, ho.ext h v _ _ hb]

theorem htr_bridge [Spec] {α : Type} {sha : Oracle} (ho : OracleHtr sha) (enc : Enc α)
    {h : Heap} {v : Value} {x : α}
    (hb : Bis 64 h v (enc x Heap.empty).2 (enc x Heap.empty).1) :
    erase (sha.hashTreeRoot h v) = htr enc x :=
  htrObj_bridge ho hb

/-! ## Decoded values against their encodings -/

/-- Each container object that `v` reaches has the fields of its class, as every object that
Python builds. -/
def Shaped (h : Heap) (v : Value) : Prop :=
  ∀ q c ty fs tys, Encode.follow h v q = some (.ref c) → h.objs c = some (.container ty fs) →
    Scope.containers.lookup ty = some tys → fs.length = tys.length

theorem decBytesT_some {α : Type} [BytesC α] {cls : Name} {h : Heap} {v : Value} {y : α}
    (hd : decBytesT cls h v = some y) : v = .bytes cls (BytesC.data y) := by
  cases v with
  | bytes c b =>
    simp only [decBytesT] at hd
    split at hd
    · rename_i hc; obtain ⟨rfl, -⟩ := hc; cases hd; rw [BytesC.data_ofBytes]
    · cases hd
  | _ => simp [decBytesT] at hd

/-- Two container objects with the same scalar fields have the same content. -/
theorem bis_container_scalars {h h' : Heap} {a a' : Nat} {ty : Name} {fs : List Value}
    (ho : h.objs a = some (.container ty fs)) (ho' : h'.objs a' = some (.container ty fs))
    (hs : ∀ x ∈ fs, ∀ c, x ≠ .ref c) (d : Nat) : Bis (d + 1) h (.ref a) h' (.ref a') := by
  simp only [Bis, ho, ho', true_and]
  intro i x x' hx hx'
  rw [hx] at hx'; cases hx'
  exact Bis_self_scalar d h h' (hs x (List.mem_of_getElem? hx))

/-- A container of two fields that decode as byte vectors of classes `c0` and `c1`. -/
theorem dec_two_bytes {α β : Type} [BytesC α] [BytesC β] {ty c0 c1 : Name} {h : Heap}
    {v : Value} {x0 : α} {x1 : β} {tys : List (Name × SszTy)} (hsh : Shaped h v)
    (hty : Scope.containers.lookup ty = some tys) (hlen : tys.length = 2)
    (hfs : ∃ fs, containerFieldsT ty h v = some fs ∧
      (∃ y, fs[0]? = some y ∧ decBytesT c0 h y = some x0) ∧
      (∃ y, fs[1]? = some y ∧ decBytesT c1 h y = some x1)) :
    ∃ a, v = .ref a ∧
      h.objs a = some (.container ty [.bytes c0 (BytesC.data x0), .bytes c1 (BytesC.data x1)]) := by
  obtain ⟨fs, hc, ⟨y0, hy0, h0⟩, ⟨y1, hy1, h1⟩⟩ := hfs
  obtain ⟨a, rfl, ho⟩ := containerFieldsT_some hc
  have hl := hsh [] a ty fs tys rfl ho hty
  rw [hlen] at hl
  match fs, hl with
  | [f0, f1], _ =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hy0 hy1
    subst hy0 hy1
    rw [decBytesT_some h0, decBytesT_some h1] at ho
    exact ⟨a, rfl, ho⟩

/-! ## `ForkData` and `SigningData` -/

theorem enc_ForkData_eq (x : ForkData) (h0 : Heap) :
    enc_ForkData x h0 = (.ref h0.next, (h0.alloc (.container Scope.Id.«ForkData»
      [.bytes Scope.Id.«Version» (BytesC.data x.current_version),
       .bytes Scope.Id.«Root» (BytesC.data x.genesis_validators_root)])).2) := rfl

theorem enc_SigningData_eq (x : SigningData) (h0 : Heap) :
    enc_SigningData x h0 = (.ref h0.next, (h0.alloc (.container Scope.Id.«SigningData»
      [.bytes Scope.Id.«Root» (BytesC.data x.object_root),
       .bytes Scope.Id.«Domain» (BytesC.data x.domain)])).2) := rfl

theorem bis_ForkData {h : Heap} {v : Value} {x : ForkData} (hsh : Shaped h v)
    (hd : dec_ForkData h v = some x) (d : Nat) (h0 : Heap) :
    Bis (d + 1) h v (enc_ForkData x h0).2 (enc_ForkData x h0).1 := by
  unfold dec_ForkData at hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨fs, hc, cv, h0', gvr, h1', rfl⟩ := hd
  obtain ⟨a, rfl, ho⟩ := dec_two_bytes (c0 := Scope.Id.«Version») (c1 := Scope.Id.«Root»)
    (x0 := cv) (x1 := gvr) hsh rfl rfl ⟨fs, hc, h0', h1'⟩
  rw [enc_ForkData_eq]
  exact bis_container_scalars ho Where.objs_alloc_self (by simp) d

theorem bis_SigningData {h : Heap} {v : Value} {x : SigningData} (hsh : Shaped h v)
    (hd : dec_SigningData h v = some x) (d : Nat) (h0 : Heap) :
    Bis (d + 1) h v (enc_SigningData x h0).2 (enc_SigningData x h0).1 := by
  unfold dec_SigningData at hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨fs, hc, r, h0', dm, h1', rfl⟩ := hd
  obtain ⟨a, rfl, ho⟩ := dec_two_bytes (c0 := Scope.Id.«Root») (c1 := Scope.Id.«Domain»)
    (x0 := r) (x1 := dm) hsh rfl rfl ⟨fs, hc, h0', h1'⟩
  rw [enc_SigningData_eq]
  exact bis_container_scalars ho Where.objs_alloc_self (by simp) d

theorem htr_ForkData [Spec] {sha : Oracle} (ho : OracleHtr sha) {h : Heap} {v : Value}
    {x : ForkData} (hsh : Shaped h v) (hd : dec_ForkData h v = some x) :
    erase (sha.hashTreeRoot h v) = htr enc_ForkData x :=
  htr_bridge ho enc_ForkData (bis_ForkData hsh hd 63 Heap.empty)

theorem htr_SigningData [Spec] {sha : Oracle} (ho : OracleHtr sha) {h : Heap} {v : Value}
    {x : SigningData} (hsh : Shaped h v) (hd : dec_SigningData h v = some x) :
    erase (sha.hashTreeRoot h v) = htr enc_SigningData x :=
  htr_bridge ho enc_SigningData (bis_SigningData hsh hd 63 Heap.empty)

/-- Two heap values that decode to one `ForkData` get one root. -/
theorem oracle_dec_ForkData [Spec] {sha : Oracle} (ho : OracleHtr sha) {h h' : Heap}
    {v v' : Value} {x : ForkData} (hs : Shaped h v) (hs' : Shaped h' v')
    (hd : dec_ForkData h v = some x) (hd' : dec_ForkData h' v' = some x) :
    sha.hashTreeRoot h v = sha.hashTreeRoot h' v' :=
  ho.ext _ _ _ _ (Bis_trans _ _ _ _ _ _ _ (bis_ForkData hs hd 63 Heap.empty)
    (Bis_symm _ _ _ _ _ (bis_ForkData hs' hd' 63 Heap.empty)))

end SpecLean.Validation.HtrBridge
