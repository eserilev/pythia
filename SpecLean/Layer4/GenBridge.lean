import SpecLean.Layer4.GenWrap
import SpecLean.Validation.HtrBridge

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

/-- A container from its fields, each decoded. -/
theorem cont_of_fields {h : Heap} {a : Nat} {ty : Name} {fs : List Value} {ds : List DV}
    (ho : h.objs a = some (.container ty fs)) (hl : fs.length = ds.length)
    (hall : ∀ (i : Nat) (w : Value) (d : DV), fs[i]? = some w → ds[i]? = some d → DecTo h w d) :
    DecTo h (.ref a) (.cont ty ds) :=
  cont_dec ho (mapM_of_fields fs ds hl hall)

end SpecLean.Layer4.GenBridge
