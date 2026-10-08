import SpecLean.Layer4.GenWrap
import SpecLean.Validation.HtrBridge
import SpecLean.Validation.BlsBridge

/-!
# Layer 4: from the readable decoders to the decoded trees

The generated theorems take a container argument as its decoded tree. The tactic takes it as a
readable value that `dec_X` decodes. These lemmas give the tree from the readable value, under
`ContWF`: each container object has the field count of its class.
-/

namespace SpecLean.Layer4.GenBridge

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd

/-- Each container object of the heap has the field count of its class. -/
def ContWF (h : Heap) : Prop :=
  ∀ a ty fs ffs, h.objs a = some (.container ty fs) → Scope.containers.lookup ty = some ffs →
    fs.length = ffs.length

/-- A heap where every container has the fields of its class gives `Shaped` for every value. -/
theorem shaped_of_contWF {h : Heap} (hc : ContWF h) (v : Value) : Validation.HtrBridge.Shaped h v :=
  fun _ c ty fs tys _ ho hl => hc c ty fs tys ho hl

/-- A field or an element decodes to a tree, at some depth. -/
def DecTo (h : Heap) (v : Value) (d : DV) : Prop := ∃ n, dec h n v = some d

theorem decTo_flat {h : Heap} {v : Value} (hv : Flat v = true) : DecTo h v (.leaf v) := ⟨0, dec_flat hv 0⟩

theorem uintT_dec {α : Type} [UintC α] {t : UintTy} {h : Heap} {v : Value} {y : α}
    (hd : decUintT t h v = some y) : DecTo h v (.leaf (.uint t (UintC.val y))) := by
  cases v with
  | lib l =>
    cases l with
    | uint t' n =>
      simp only [decUintT] at hd
      split at hd
      · next hc =>
        obtain ⟨rfl, -⟩ := hc
        cases hd
        rw [UintC.val_ofNat]
        exact decTo_flat rfl
      · cases hd
    | boolean _ => simp [decUintT] at hd
  | _ => simp [decUintT] at hd

theorem bytesT_dec {α : Type} [BytesC α] {c : Name} {h : Heap} {v : Value} {y : α}
    (hd : decBytesT c h v = some y) : DecTo h v (.leaf (.bytes c (BytesC.data y))) := by
  cases v with
  | bytes c' b =>
    simp only [decBytesT] at hd
    split at hd
    · next hc =>
      obtain ⟨rfl, -⟩ := hc
      cases hd
      rw [BytesC.data_ofBytes]
      exact decTo_flat rfl
    · cases hd
  | _ => simp [decBytesT] at hd

theorem boolean_dec {h : Heap} {v : Value} {y : Boolean} (hd : decBooleanV h v = some y) :
    DecTo h v (.leaf (.boolean y.val)) := by
  cases v with
  | lib l =>
    cases l with
    | boolean b => simp only [decBooleanV] at hd; cases hd; exact decTo_flat rfl
    | uint _ _ => simp [decBooleanV] at hd
  | _ => simp [decBooleanV] at hd

/-- The elements of a list, each decoded. -/
theorem mapM_dec {α : Type} {h : Heap} {f : Dec α} {g : α → DV}
    (hf : ∀ x y, f h x = some y → DecTo h x (g y)) :
    ∀ (xs : List Value) (ys : List α), xs.mapM (f h) = some ys →
      ∃ n, xs.mapM (dec h n) = some (ys.map g)
  | [], ys, e => by simp at e; subst e; exact ⟨0, rfl⟩
  | x :: xs, ys, e => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨y, hy, ys', hys', e⟩ := e
    simp at e; subst e
    obtain ⟨n1, h1⟩ := hf x y hy
    obtain ⟨n2, h2⟩ := mapM_dec hf xs ys' hys'
    refine ⟨max n1 n2, ?_⟩
    have e1 := dec_mono' h1 (Nat.le_max_left n1 n2)
    have e2 : xs.mapM (dec h (max n1 n2)) = some (ys'.map g) := by
      rw [← h2]
      exact (mapM_mono_dec h2 (Nat.le_max_right n1 n2))
    simp [List.mapM_cons, e1, e2]
where
  mapM_mono_dec {xs : List Value} {ds : List DV} {n n' : Nat} (e : xs.mapM (dec h n) = some ds)
      (hle : n ≤ n') : xs.mapM (dec h n') = xs.mapM (dec h n) := by
    induction xs generalizing ds with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at e
      obtain ⟨d, hd, ds', hds', -⟩ := e
      simp only [List.mapM_cons, dec_mono' hd hle, hd, ih hds']

theorem listT_dec {α : Type} {k : ListKind} {e : SszTy} {l : Option Nat} {f : Dec α}
    {g : α → DV} {h : Heap} {v : Value} {ys : List α} (hd : decListT k e l f h v = some ys)
    (hf : ∀ x y, f h x = some y → DecTo h x (g y)) : DecTo h v (.list k e l (ys.map g)) := by
  cases v with
  | ref a =>
    simp only [decListT] at hd
    split at hd
    · next xs ho =>
      split at hd
      · next hc =>
        obtain ⟨rfl, rfl, rfl⟩ := hc
        obtain ⟨n, hn⟩ := mapM_dec hf xs ys hd
        exact ⟨n + 1, by simp [dec, ho, hn]⟩
      · cases hd
    · cases hd
  | _ => simp [decListT] at hd

/-- The fields of a container, from `containerFieldsT`. -/
theorem fieldsT_some {ty : Name} {h : Heap} {v : Value} {fs : List Value}
    (hf : containerFieldsT ty h v = some fs) : ∃ a, v = .ref a ∧ h.objs a = some (.container ty fs) := by
  cases v with
  | ref a =>
    simp only [containerFieldsT] at hf
    split at hf
    · next ty' fs' ho =>
      split at hf
      · next hty => subst hty; cases hf; exact ⟨a, rfl, ho⟩
      · cases hf
    · cases hf
  | _ => simp [containerFieldsT] at hf

/-- A container from its decoded fields. -/
theorem cont_dec {h : Heap} {a : Nat} {ty : Name} {fs : List Value} {ds : List DV}
    (ho : h.objs a = some (.container ty fs)) (hds : ∃ n, fs.mapM (dec h n) = some ds) :
    DecTo h (.ref a) (.cont ty ds) := by
  obtain ⟨n, hn⟩ := hds
  exact ⟨n + 1, by simp [dec, ho, hn]⟩

theorem mapM_of_fields {h : Heap} :
    ∀ (fs : List Value) (ds : List DV), fs.length = ds.length →
      (∀ (i : Nat) (w : Value) (d : DV), fs[i]? = some w → ds[i]? = some d → DecTo h w d) →
      ∃ n, fs.mapM (dec h n) = some ds
  | [], [], _, _ => ⟨0, rfl⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | w :: fs, d :: ds, hl, hall => by
    obtain ⟨n1, h1⟩ := hall 0 w d rfl rfl
    obtain ⟨n2, h2⟩ := mapM_of_fields fs ds (by simpa using hl)
      (fun i w' d' hw hd => hall (i + 1) w' d' (by simpa using hw) (by simpa using hd))
    refine ⟨max n1 n2, ?_⟩
    have e1 := dec_mono' h1 (Nat.le_max_left n1 n2)
    have e2 : fs.mapM (dec h (max n1 n2)) = some ds := by
      rw [mapM_dec.mapM_mono_dec h2 (Nat.le_max_right n1 n2)]; exact h2
    simp [List.mapM_cons, e1, e2]

/-! ## Decoded values are in range -/

theorem uintT_ok {α : Type} [UintC α] {t : UintTy} {h : Heap} {v : Value} {y : α}
    (hd : decUintT t h v = some y) : UintC.val y < 2 ^ UintC.bits α := by
  cases v with
  | lib l =>
    cases l with
    | uint t' n =>
      simp only [decUintT] at hd
      split at hd
      · next hc => cases hd; rw [UintC.val_ofNat]; exact hc.2
      · cases hd
    | boolean _ => simp [decUintT] at hd
  | _ => simp [decUintT] at hd

theorem bytesT_ok {α : Type} [BytesC α] {c : Name} {h : Heap} {v : Value} {y : α}
    (hd : decBytesT c h v = some y) : (BytesC.data y).length = BytesC.len α := by
  cases v with
  | bytes c' b =>
    simp only [decBytesT] at hd
    split at hd
    · next hc => cases hd; rw [BytesC.data_ofBytes]; exact hc.2
    · cases hd
  | _ => simp [decBytesT] at hd

theorem mapM_ok {α : Type} {h : Heap} {f : Dec α} {P : α → Prop}
    (hf : ∀ x y, f h x = some y → P y) :
    ∀ (xs : List Value) (ys : List α), xs.mapM (f h) = some ys → ∀ y ∈ ys, P y
  | [], ys, e => by simp at e; subst e; simp
  | x :: xs, ys, e => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨y, hy, ys', hys', e⟩ := e
    simp at e; subst e
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hf x z hy
    · exact mapM_ok hf xs ys' hys' z hz

theorem listT_ok {α : Type} {k : ListKind} {e : SszTy} {l : Option Nat} {f : Dec α}
    {P : α → Prop} {h : Heap} {v : Value} {ys : List α} (hd : decListT k e l f h v = some ys)
    (hf : ∀ x y, f h x = some y → P y) : ∀ y ∈ ys, P y := by
  cases v with
  | ref a =>
    simp only [decListT] at hd
    split at hd
    · next xs ho =>
      split at hd
      · exact mapM_ok hf xs ys hd
      · cases hd
    · cases hd
  | _ => simp [decListT] at hd

/-- A container from its fields, each decoded. -/
theorem cont_of_fields {h : Heap} {a : Nat} {ty : Name} {fs : List Value} {ds : List DV}
    (ho : h.objs a = some (.container ty fs)) (hl : fs.length = ds.length)
    (hall : ∀ (i : Nat) (w : Value) (d : DV), fs[i]? = some w → ds[i]? = some d → DecTo h w d) :
    DecTo h (.ref a) (.cont ty ds) :=
  cont_dec ho (mapM_of_fields fs ds hl hall)

/-! ## `hash_tree_root`: the oracle on the decoded content -/

open Validation.HtrBridge in
/-- Two values that decode to one tree have the same content. -/
theorem Bis_of_dec : ∀ (m : Nat) {h h' : Heap} {v v' : Value} {n n' : Nat} {d : DV},
    dec h n v = some d → dec h' n' v' = some d → Bis m h v h' v'
  | m, h, h', v, v', n, n', .leaf u, e1, e2 => by
    obtain ⟨rfl, hu⟩ := dec_leaf e1
    obtain ⟨rfl, -⟩ := dec_leaf e2
    exact Bis_self_scalar m h h' (flat_nonref hu)
  | m, h, h', v, v', n, n', .cont ty ds, e1, e2 => by
    obtain ⟨a, k, fs, rfl, rfl, ho, hm⟩ := dec_cont e1
    obtain ⟨a', k', fs', rfl, rfl, ho', hm'⟩ := dec_cont e2
    cases m with
    | zero => simp [Bis]
    | succ m =>
      obtain ⟨hl, hp⟩ := (mapM_some_iff fs ds).mp hm
      obtain ⟨hl', hp'⟩ := (mapM_some_iff fs' ds).mp hm'
      simp only [Bis, ho, ho']
      refine ⟨by simp, by omega, fun i x x' hx hx' => ?_⟩
      have h1 := hp i x hx
      have h2 := hp' i x' hx'
      cases hdi : ds[i]? with
      | none =>
        have := (List.getElem?_eq_some_iff.mp hx).1
        rw [List.getElem?_eq_none_iff] at hdi; omega
      | some di => rw [hdi] at h1 h2; exact Bis_of_dec m h1 h2
  | m, h, h', v, v', n, n', .list k el l ds, e1, e2 => by
    obtain ⟨a, j, xs, rfl, rfl, ho, hm⟩ := dec_list e1
    obtain ⟨a', j', xs', rfl, rfl, ho', hm'⟩ := dec_list e2
    cases m with
    | zero => simp [Bis]
    | succ m =>
      obtain ⟨hl, hp⟩ := (mapM_some_iff xs ds).mp hm
      obtain ⟨hl', hp'⟩ := (mapM_some_iff xs' ds).mp hm'
      simp only [Bis, ho, ho']
      refine ⟨by simp, by simp, by simp, by omega, fun i x x' hx hx' => ?_⟩
      have h1 := hp i x hx
      have h2 := hp' i x' hx'
      cases hdi : ds[i]? with
      | none =>
        have := (List.getElem?_eq_some_iff.mp hx).1
        rw [List.getElem?_eq_none_iff] at hdi; omega
      | some di => rw [hdi] at h1 h2; exact Bis_of_dec m h1 h2
where
  mapM_get_none {f : Value → Option DV} {xs : List Value} {ds : List DV} (hm : xs.mapM f = some ds)
      {i : Nat} {x : Value} (hx : xs[i]? = some x) : f x = ds[i]? :=
    ((mapM_some_iff xs ds).mp hm).2 i x hx

/-- An oracle that reads only the content of a value reads only its decoded tree. -/
theorem htrDec_of_ext {sha : Oracle}
    (hx : ∀ h v h' v', Validation.HtrBridge.Bis 64 h v h' v' → sha.hashTreeRoot h v = sha.hashTreeRoot h' v')
    (hb : ∀ h f vs, (∀ v ∈ vs, Flat v = true) → sha.bls f h vs = sha.bls f Heap.empty vs) :
    Examples2.HtrDec (Scope.env sha) :=
  ⟨fun h v h' v' _ _ _ e1 e2 => hx h v h' v' (Bis_of_dec 64 e1 e2), hb⟩

/-- An encoder that adds objects and gives a value that decodes to `d`. -/
def EncDec (f : Heap → Value × Heap) (d : DV) : Prop :=
  ∀ h0, Ext h0 (f h0).2 ∧ Below (f h0).2 (f h0).1 ∧ ∃ n, dec (f h0).2 n (f h0).1 = some d

theorem encDec_flat {v : Value} (hv : Flat v = true) : EncDec (fun h => (v, h)) (.leaf v) :=
  fun h0 => ⟨Ext_refl h0, fun q a e => absurd e (fun e' => follow_nonref_ref (flat_nonref hv) e'),
    0, dec_flat hv 0⟩

/-- The fold of `encContainer` and `encList`. -/
def encFold (gs : List (Heap → Value × Heap)) (acc : List Value) (h : Heap) : List Value × Heap :=
  gs.foldl (fun (acc : List Value × Heap) f =>
    let (v, h1) := f acc.2
    (acc.1 ++ [v], h1)) (acc, h)

theorem encFold_cons (g : Heap → Value × Heap) (gs : List (Heap → Value × Heap)) (acc : List Value)
    (h : Heap) : encFold (g :: gs) acc h = encFold gs (acc ++ [(g h).1]) (g h).2 := rfl

theorem encContainer_eq (ty : Name) (fs : List (Heap → Value × Heap)) (h : Heap) :
    encContainer ty fs h =
      (.ref (encFold fs [] h).2.next, ((encFold fs [] h).2.alloc (.container ty (encFold fs [] h).1)).2) := rfl

theorem encList_eq {α : Type} (k : ListKind) (e : SszTy) (l : Option Nat) (f : Enc α) (xs : List α)
    (h : Heap) :
    encList k e l f xs h =
      (.ref (encFold (xs.map f) [] h).2.next,
        ((encFold (xs.map f) [] h).2.alloc (.list k e l (encFold (xs.map f) [] h).1)).2) := by
  unfold encList encFold; rw [List.foldl_map]; rfl

/-- The items of an encoder fold, one encoder per item. -/
theorem fold_spec : ∀ (gs : List (Heap → Value × Heap)) (ds : List DV), gs.length = ds.length →
    (∀ (i : Nat) g d, gs[i]? = some g → ds[i]? = some d → EncDec g d) →
    ∀ (acc : List Value) (h : Heap),
      Ext h (encFold gs acc h).2 ∧ (∀ v ∈ acc, Below h v → Below (encFold gs acc h).2 v) ∧
        ∃ vs n, (encFold gs acc h).1 = acc ++ vs ∧
          (∀ v ∈ vs, Below (encFold gs acc h).2 v) ∧ vs.mapM (dec (encFold gs acc h).2 n) = some ds
  | [], [], _, _, acc, h => ⟨Ext_refl h, fun _ _ hb => hb, [], 0, by simp [encFold], by simp, rfl⟩
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | g :: gs, d :: ds, hl, hall, acc, h => by
    obtain ⟨e1, hb1, n1, hd1⟩ := hall 0 g d rfl rfl h
    obtain ⟨e2, hacc, vs, n2, hr, hbv, hm⟩ := fold_spec gs ds (by simpa using hl)
      (fun i g' d' hg hd => hall (i + 1) g' d' (by simpa using hg) (by simpa using hd))
      (acc ++ [(g h).1]) (g h).2
    rw [encFold_cons]
    refine ⟨Ext_trans e1 e2, fun v hv hb => ?_, (g h).1 :: vs, max n1 n2, ?_, ?_, ?_⟩
    · exact hacc v (by simp [hv]) (fun q a ea => Nat.lt_of_lt_of_le (hb q a ((follow_Ext e1 q hb a).mp ea)) e1.1)
    · rw [hr]; simp
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hacc _ (by simp) hb1
      · exact hbv v hv
    · simp only [List.mapM_cons]
      rw [dec_ext e2 hb1, dec_mono' hd1 (Nat.le_max_left _ _), mapM_dec_mono hm (Nat.le_max_right _ _)]
      rfl

theorem encDec_node {gs : List (Heap → Value × Heap)} {ds : List DV} (hl : gs.length = ds.length)
    (hall : ∀ (i : Nat) g d, gs[i]? = some g → ds[i]? = some d → EncDec g d) (h0 : Heap)
    (o : List Value → HeapObj) (ho : ∀ vs, okids (some (o vs)) = some vs) (d : List DV → DV)
    (hdo : ∀ (h : Heap) (a n : Nat) vs, h.objs a = some (o vs) → vs.mapM (dec h n) = some ds →
      dec h (n + 1) (.ref a) = some (d ds)) :
    Ext h0 ((encFold gs [] h0).2.alloc (o (encFold gs [] h0).1)).2 ∧
      Below ((encFold gs [] h0).2.alloc (o (encFold gs [] h0).1)).2 (.ref (encFold gs [] h0).2.next) ∧
      ∃ n, dec ((encFold gs [] h0).2.alloc (o (encFold gs [] h0).1)).2 n (.ref (encFold gs [] h0).2.next) =
        some (d ds) := by
  obtain ⟨e1, -, vs, n, hr, hbv, hm⟩ := fold_spec gs ds hl hall [] h0
  simp only [List.nil_append] at hr
  rw [hr]
  obtain ⟨e2, hb2, hm2⟩ := node_spec hbv (o vs) (ho vs)
  refine ⟨Ext_trans e1 e2, hb2, n + 1, hdo _ _ n vs (by simp [Heap.alloc]) ?_⟩
  rw [hm2]; exact hm

theorem encDec_container {ty : Name} {fs : List (Heap → Value × Heap)} {ds : List DV}
    (hl : fs.length = ds.length)
    (hall : ∀ (i : Nat) g d, fs[i]? = some g → ds[i]? = some d → EncDec g d) :
    EncDec (encContainer ty fs) (.cont ty ds) := by
  intro h0
  rw [encContainer_eq]
  exact encDec_node hl hall h0 (.container ty) (fun _ => rfl) (.cont ty)
    (fun h a n vs ho hm => by simp [dec_ref_succ, ho, hm])

theorem encDec_list {α : Type} {k : ListKind} {e : SszTy} {l : Option Nat} {f : Enc α}
    {g : α → DV} (hf : ∀ x, EncDec (f x) (g x)) (xs : List α) :
    EncDec (encList k e l f xs) (.list k e l (xs.map g)) := by
  intro h0
  rw [encList_eq]
  refine encDec_node (by simp) (fun i g' d hg hd => ?_) h0 (.list k e l) (fun _ => rfl) (.list k e l)
    (fun h a n vs ho hm => by simp [dec_ref_succ, ho, hm])
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hg hd
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨x', hx', rfl⟩ := hd
  rw [hx] at hx'; cases hx'
  exact hf x

/-- `hash_tree_root` of a tree in the denotation is the readable `htr` of a value that encodes
to it. -/
theorem htr_den [Spec] {sha : Oracle} (ho : Validation.HtrBridge.OracleHtr sha) {α : Type} (enc : Enc α)
    (x : α) {d : DV} (hE : EncDec (enc x) d) :
    Option.map (Except.mapError SpecError.fail) (dHtr (Scope.env sha) d) =
      some ((fun r => DRes.val (.bytes (Scope.env sha).nm.root r)) <$> htr enc x) := by
  obtain ⟨-, -, n, hn⟩ := hE Heap.empty
  obtain ⟨-, -, n', hn'⟩ := encDV_spec d Heap.empty (dec_leafFlat n _ d hn)
  have heq : sha.hashTreeRoot (encDV d Heap.empty).2 (encDV d Heap.empty).1 =
      sha.hashTreeRoot (enc x Heap.empty).2 (enc x Heap.empty).1 :=
    ho.ext _ _ _ _ (Bis_of_dec 64 hn' hn)
  unfold dHtr htr htrObj
  show Option.map _ (DM.bind (lift (sha.hashTreeRoot _ _)) _) = _
  rw [heq, ho.same]
  have hno := ho.noOof (enc x Heap.empty).2 (enc x Heap.empty).1
  cases hr : sha.hashTreeRoot (enc x Heap.empty).2 (enc x Heap.empty).1 with
  | ok r => simp [hr, lift, DM.bind, DM.ok, erase, Except.mapError]
  | error e =>
    have : e ≠ .outOfFuel := fun he => hno (by rw [hr, he])
    simp [hr, lift, DM.bind, erase, Except.mapError, this]

/-- The oracle gives 32 bytes, so the `Root` of its result needs no check. -/
theorem callK_htr_root [Spec] {sha : Oracle} (ho : Validation.HtrBridge.OracleHtr sha) {α : Type}
    (enc : Enc α) (x : α) {γ : Type} (g : Rd.Gen.Root → Option (Except Fail γ)) :
    Layer4.GenSteps.callK (htr enc x) (fun b => Layer4.GenSteps.callK (bytesOf Rd.Gen.Root b) g) =
      Layer4.GenSteps.callK (htr enc x) (fun b => g ⟨b⟩) := by
  unfold htr htrObj
  rw [ho.same]
  cases hr : sha.hashTreeRoot (enc x Heap.empty).2 (enc x Heap.empty).1 with
  | error e => simp [hr, erase, Except.mapError, Layer4.GenSteps.callK]
  | ok r =>
    have hl := ho.len _ _ r hr
    simp [hr, erase, Except.mapError, Layer4.GenSteps.callK, bytesOf, hl]
    rfl

/-- The oracle gives 32 bytes, so a check of the length of its result holds. -/
theorem callK_htr_len [Spec] {sha : Oracle} (ho : Validation.HtrBridge.OracleHtr sha) {α : Type}
    (enc : Enc α) (x : α) {γ : Type} (g : Bytes → Option (Except Fail γ)) (z : Option (Except Fail γ)) :
    Layer4.GenSteps.callK (htr enc x) (fun b => if b.length = 32 then g b else z) =
      Layer4.GenSteps.callK (htr enc x) g := by
  unfold htr htrObj
  rw [ho.same]
  cases hr : sha.hashTreeRoot (enc x Heap.empty).2 (enc x Heap.empty).1 with
  | error e => simp [hr, erase, Except.mapError, Layer4.GenSteps.callK]
  | ok r =>
    have hl := ho.len _ _ r hr
    simp [hr, erase, Except.mapError, Layer4.GenSteps.callK, hl]

/-- `hash_tree_root` of a tree in the denotation is the readable `htrObj` of an object whose
encoder decodes to it. -/
theorem htr_den_obj [Spec] {sha : Oracle} (ho : Validation.HtrBridge.OracleHtr sha) (o : SszObj)
    {d : DV} (hE : EncDec o.enc d) :
    Option.map (Except.mapError SpecError.fail) (dHtr (Scope.env sha) d) =
      some ((fun r => DRes.val (.bytes (Scope.env sha).nm.root r)) <$> htrObj o) :=
  htr_den ho (fun (_ : Unit) => o.enc) () hE

theorem htr_obj_call [Spec] {sha : Oracle} (ho : Validation.HtrBridge.OracleHtr sha) (o : SszObj)
    {d : DV} (hE : EncDec o.enc d) {γ : Type} (K : DRes → DM γ) :
    Option.map (Except.mapError SpecError.fail) (DM.bind (dHtr (Scope.env sha) d) K) =
      Layer4.GenSteps.callK (htrObj o) fun r =>
        Option.map (Except.mapError SpecError.fail) (K (.val (.bytes (Scope.env sha).nm.root r))) :=
  Layer4.GenSteps.bind_call (htr_den_obj ho o hE) K

/-- `htrObj` gives 32 bytes, as `htr`. -/
theorem callK_htrObj_len [Spec] {sha : Oracle} (ho : Validation.HtrBridge.OracleHtr sha) (o : SszObj)
    {γ : Type} (g : Bytes → Option (Except Fail γ)) (z : Option (Except Fail γ)) :
    Layer4.GenSteps.callK (htrObj o) (fun b => if b.length = 32 then g b else z) =
      Layer4.GenSteps.callK (htrObj o) g :=
  callK_htr_len ho (fun (_ : Unit) => o.enc) () g z

/-! ## Decoded trees back to readable values -/

/-- A leaf decoder on a decoded tree: the readable decoder on the flat value. -/
def undvLeaf {α : Type} (f : Dec α) : DV → Option α
  | .leaf v => f Heap.empty v
  | _ => none

/-- A list decoder on a decoded tree. -/
def undvList {α : Type} (k : ListKind) (e : SszTy) (l : Option Nat) (f : DV → Option α) : DV → Option (List α)
  | .list k' e' l' ds => if k' = k ∧ e' = e ∧ l' = l then ds.mapM f else none
  | _ => none

/-- `u` decodes a tree as `f` decodes every value whose decoded tree it is. -/
def DecOf {α : Type} (f : Dec α) (u : DV → Option α) : Prop :=
  ∀ h n v d x, dec h n v = some d → u d = some x → f h v = some x

theorem decOf_leaf {α : Type} {f : Dec α} (hf : ∀ h v, Flat v = true → f h v = f Heap.empty v) :
    DecOf f (undvLeaf f) := by
  intro h n v d x hd hu
  cases d with
  | leaf u =>
    obtain ⟨rfl, hfl⟩ := dec_leaf hd
    simp only [undvLeaf] at hu
    rw [hf h v hfl]; exact hu
  | _ => simp [undvLeaf] at hu

theorem decOf_uint {α : Type} [UintC α] (t : UintTy) : DecOf (decUintT (α := α) t) (undvLeaf (decUintT t)) :=
  decOf_leaf fun h v _ => by cases v with | lib l => cases l <;> rfl | _ => rfl

theorem decOf_bytes {α : Type} [BytesC α] (c : Name) : DecOf (decBytesT (α := α) c) (undvLeaf (decBytesT c)) :=
  decOf_leaf fun h v _ => by cases v <;> rfl

theorem decOf_boolean : DecOf decBooleanV (undvLeaf decBooleanV) :=
  decOf_leaf fun h v _ => by cases v with | lib l => cases l <;> rfl | _ => rfl

theorem mapM_decOf {α : Type} {f : Dec α} {u : DV → Option α} (hf : DecOf f u) {h : Heap} {m : Nat} :
    ∀ (xs : List Value) (ds : List DV) (ys : List α), xs.mapM (dec h m) = some ds → ds.mapM u = some ys →
      xs.mapM (f h) = some ys
  | [], ds, ys, hx, hy => by simp at hx; subst hx; simpa using hy
  | x :: xs, ds, ys, hx, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx
    obtain ⟨d, hd, ds', hds', rfl⟩ := hx
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hy
    obtain ⟨y, hu, ys', hys', rfl⟩ := hy
    simp [List.mapM_cons, hf h m x d y hd hu, mapM_decOf hf xs ds' ys' hds' hys']

theorem decOf_list {α : Type} {f : Dec α} {u : DV → Option α} (hf : DecOf f u) (k : ListKind) (e : SszTy)
    (l : Option Nat) : DecOf (decListT k e l f) (undvList k e l u) := by
  intro h n v d x hd hu
  cases d with
  | list k' e' l' ds =>
    simp only [undvList] at hu
    split at hu
    · next hc =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨a, m, xs, rfl, rfl, ho, hm⟩ := dec_list hd
      simp only [decListT, ho, and_self, ↓reduceIte]
      exact mapM_decOf hf xs ds x hm hu
    · cases hu
  | _ => simp [undvList] at hu

/-- A `Sequence` decoder on a decoded tree: a list of any kind and limit with element type `e`. -/
def undvListE {α : Type} (e : SszTy) (f : DV → Option α) : DV → Option (List α)
  | .list _ e' _ ds => if e' = e then ds.mapM f else none
  | _ => none

theorem decOf_listE {α : Type} {f : Dec α} {u : DV → Option α} (hf : DecOf f u) (e : SszTy) :
    DecOf (Validation.decListE e f) (undvListE e u) := by
  intro h n v d x hd hu
  cases d with
  | list k' e' l' ds =>
    simp only [undvListE] at hu
    split at hu
    · next hc =>
      subst hc
      obtain ⟨a, m, xs, rfl, rfl, ho, hm⟩ := dec_list hd
      simp only [Validation.decListE, ho, ↓reduceIte]
      exact mapM_decOf hf xs ds x hm hu
    · cases hu
  | _ => simp [undvListE] at hu

theorem undvListE_map {α : Type} {u : DV → Option α} {g : α → DV} (k : ListKind) (e : SszTy) (l : Option Nat)
    (xs : List α) (hx : ∀ x ∈ xs, u (g x) = some x) : undvListE e u (.list k e l (xs.map g)) = some xs := by
  simp only [undvListE, ↓reduceIte]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, hx x (by simp), ih (fun y hy => hx y (by simp [hy]))]
    rfl

/-- The field `i` of a container, decoded as its tree. -/
theorem field_decOf {α : Type} {f : Dec α} {u : DV → Option α} (hf : DecOf f u) {h : Heap} {m : Nat}
    {fs : List Value} {ds : List DV} (hm : fs.mapM (dec h m) = some ds) (i : Nat) {y : α}
    (hy : ds[i]?.bind u = some y) : fs[i]?.bind (f h) = some y := by
  have hl := ((mapM_some_iff fs ds).mp hm)
  cases hd : ds[i]? with
  | none => rw [hd] at hy; cases hy
  | some d =>
    rw [hd] at hy
    have hi : i < fs.length := by have := (List.getElem?_eq_some_iff.mp hd).1; have := hl.1; omega
    have hfx : fs[i]? = some fs[i] := List.getElem?_eq_getElem hi
    rw [hfx]
    have hdec : dec h m fs[i] = some d := by rw [hl.2 i fs[i] hfx, hd]
    exact hf h m fs[i] d y hdec hy

theorem undvList_map {α : Type} {u : DV → Option α} {g : α → DV} (k : ListKind) (e : SszTy) (l : Option Nat)
    (xs : List α) (hx : ∀ x ∈ xs, u (g x) = some x) : undvList k e l u (.list k e l (xs.map g)) = some xs := by
  simp only [undvList, and_self, ↓reduceIte]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, hx x (by simp), ih (fun y hy => hx y (by simp [hy]))]
    rfl

theorem undv_uint {α : Type} [UintC α] (t : UintTy) (x : α) (hx : UintC.val x < 2 ^ UintC.bits α) :
    undvLeaf (decUintT t) (.leaf (.uint t (UintC.val x))) = some x := by
  simp [undvLeaf, decUintT, hx, UintC.ofNat_val]

theorem undv_bytes {α : Type} [BytesC α] (c : Name) (x : α) (hx : (BytesC.data x).length = BytesC.len α) :
    undvLeaf (decBytesT c) (.leaf (.bytes c (BytesC.data x))) = some x := by
  simp [undvLeaf, decBytesT, hx, BytesC.ofBytes_data]

theorem undv_boolean (x : Boolean) : undvLeaf decBooleanV (.leaf (.boolean x.val)) = some x := by
  simp [undvLeaf, decBooleanV]

/-! ## The result of a callee taken from a statement -/

/-- A uint leaf: its class and its number. -/
def leafUint : DV → Option (UintTy × Nat)
  | .leaf (.uint t n) => some (t, n)
  | _ => none

theorem leafUint_spec {d : DV} {t : UintTy} {n : Nat} (h : leafUint d = some (t, n)) :
    d = .leaf (.uint t n) := by
  unfold leafUint at h
  split at h
  · cases h; rfl
  · cases h

/-- The den result of a readable call: its value as a tree, or the error of its class. -/
def extRes {α : Type} (enc : α → DRes) (r : SpecM α) : DM DRes :=
  match r with
  | .ok y => some (.ok (enc y))
  | .error f => some (.error (SpecError.rep f))

theorem rep_fail (f : Fail) : (SpecError.rep f).fail = f := by cases f <;> rfl

theorem extRes_map {α : Type} (enc : α → DRes) (r : SpecM α) :
    Option.map (Except.mapError SpecError.fail) (extRes enc r) = some (enc <$> r) := by
  cases r <;> simp [extRes, rep_fail, Except.mapError] <;> rfl

theorem dbind_assoc {α β γ : Type} (x : DM α) (f : α → DM β) (g : β → DM γ) :
    DM.bind (DM.bind x f) g = DM.bind x (fun a => DM.bind (f a) g) := by
  rcases x with _ | ⟨e | a⟩ <;> rfl

theorem extRes_call {α γ : Type} (enc : α → DRes) (r : SpecM α) (K : DRes → DM γ) :
    Option.map (Except.mapError SpecError.fail) (DM.bind (extRes enc r) K) =
      Layer4.GenSteps.callK r fun y => Option.map (Except.mapError SpecError.fail) (K (enc y)) :=
  Layer4.GenSteps.bind_call (extRes_map enc r) K

end SpecLean.Layer4.GenBridge
