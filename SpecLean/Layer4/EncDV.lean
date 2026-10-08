import SpecLean.Layer4.CallRule

/-!
# Layer 4: a decoded tree as a heap value

`encDV d h` puts a new object in `h` for each node of `d`. It decodes back to `d`. The denotation
computes `hash_tree_root` of a tree on this value; the oracle reads only the decoded content.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

mutual
/-- Every leaf of a tree is a flat value, as `dec` gives. -/
def LeafFlat : DV → Prop
  | .leaf v => Flat v = true
  | .cont _ ds => LeafFlats ds
  | .list _ _ _ ds => LeafFlats ds
def LeafFlats : List DV → Prop
  | [] => True
  | d :: ds => LeafFlat d ∧ LeafFlats ds
end

theorem mapM_leafFlat {h : Heap} {m : Nat} (ih : ∀ v d, dec h m v = some d → LeafFlat d) :
    ∀ (xs : List Value) (ds : List DV), xs.mapM (dec h m) = some ds → LeafFlats ds
  | [], ds, hm => by simp at hm; subst hm; trivial
  | x :: xs, ds, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hm
    obtain ⟨d, hd, ds', hds', e⟩ := hm
    simp at e; subst e
    exact ⟨ih x d hd, mapM_leafFlat ih xs ds' hds'⟩

theorem dec_leafFlat {h : Heap} : ∀ (n : Nat) (v : Value) (d : DV), dec h n v = some d → LeafFlat d := by
  intro n
  induction n with
  | zero =>
    intro v d hd
    cases d with
    | leaf u => exact (dec_leaf hd).2
    | cont ty ds => obtain ⟨_, _, _, _, h0, _⟩ := dec_cont hd; omega
    | list k e l ds => obtain ⟨_, _, _, _, h0, _⟩ := dec_list hd; omega
  | succ m ih =>
    intro v d hd
    cases d with
    | leaf u => exact (dec_leaf hd).2
    | cont ty ds =>
      obtain ⟨a, m', fs, rfl, hm', -, hm⟩ := dec_cont hd
      cases hm'
      exact mapM_leafFlat ih fs ds hm
    | list k e l ds =>
      obtain ⟨a, m', xs, rfl, hm', -, hm⟩ := dec_list hd
      cases hm'
      exact mapM_leafFlat ih xs ds hm

theorem mapM_dec_mono {h : Heap} {xs : List Value} {ds : List DV} {n n' : Nat}
    (e : xs.mapM (dec h n) = some ds) (hle : n ≤ n') : xs.mapM (dec h n') = some ds := by
  induction xs generalizing ds with
  | nil => simpa using e
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨d, hd, ds', hds', e⟩ := e
    simp only [List.mapM_cons, dec_mono' hd hle, ih hds', Option.bind_eq_bind, Option.bind_some]
    exact e

/-- A new object over children that are below `next`. -/
theorem node_spec {h1 : Heap} {vs : List Value} (hb : ∀ v ∈ vs, Below h1 v) (o : HeapObj)
    (ho : okids (some o) = some vs) :
    Ext h1 (h1.alloc o).2 ∧ Below (h1.alloc o).2 (.ref h1.next) ∧
      ∀ n, vs.mapM (dec (h1.alloc o).2 n) = vs.mapM (dec h1 n) := by
  have e := Ext_alloc h1 o
  have hobj : (h1.alloc o).2.objs h1.next = some o := by simp [Heap.alloc]
  refine ⟨e, fun q a ea => ?_, fun n => mapM_congr fun i x hx =>
    dec_ext e (hb x (List.mem_of_getElem? hx)) n⟩
  have hnext : (h1.alloc o).2.next = h1.next + 1 := rfl
  cases q with
  | nil => simp [follow] at ea; subst ea; omega
  | cons j q =>
    rw [follow_ref_cons, hobj, ho] at ea
    simp only [Option.bind_some] at ea
    cases hx : vs[j]? with
    | none => simp [hx] at ea
    | some x =>
      simp only [hx, Option.bind_some] at ea
      have hbx := hb x (List.mem_of_getElem? hx)
      have := hbx q a ((follow_Ext e q hbx a).mp ea)
      omega

mutual
/-- `encDV` only adds objects, its value reaches only objects below `next`, and it decodes back. -/
theorem encDV_spec : ∀ (d : DV) (h : Heap), LeafFlat d →
    Ext h (encDV d h).2 ∧ Below (encDV d h).2 (encDV d h).1 ∧
      ∃ n, dec (encDV d h).2 n (encDV d h).1 = some d
  | .leaf v, h, hf => by
    refine ⟨Ext_refl h, fun q a e => ?_, ⟨0, dec_flat hf 0⟩⟩
    exact absurd e (fun e' => follow_nonref_ref (flat_nonref hf) e')
  | .cont ty ds, h, hf => by
    obtain ⟨e1, hb1, n1, hd1⟩ := encDVs_spec ds h hf
    obtain ⟨e2, hb2, hm⟩ := node_spec hb1 (.container ty (encDVs ds h).1) rfl
    have hobj : ((encDVs ds h).2.alloc (.container ty (encDVs ds h).1)).2.objs (encDVs ds h).2.next = some (.container ty (encDVs ds h).1) := by
      simp [Heap.alloc]
    refine ⟨Ext_trans e1 e2, hb2, n1 + 1, ?_⟩
    simp only [encDV, dec_ref_succ, hobj, hm, hd1]; rfl
  | .list k el l ds, h, hf => by
    obtain ⟨e1, hb1, n1, hd1⟩ := encDVs_spec ds h hf
    obtain ⟨e2, hb2, hm⟩ := node_spec hb1 (.list k el l (encDVs ds h).1) rfl
    have hobj : ((encDVs ds h).2.alloc (.list k el l (encDVs ds h).1)).2.objs (encDVs ds h).2.next = some (.list k el l (encDVs ds h).1) := by
      simp [Heap.alloc]
    refine ⟨Ext_trans e1 e2, hb2, n1 + 1, ?_⟩
    simp only [encDV, dec_ref_succ, hobj, hm, hd1]; rfl
theorem encDVs_spec : ∀ (ds : List DV) (h : Heap), LeafFlats ds →
    Ext h (encDVs ds h).2 ∧ (∀ v ∈ (encDVs ds h).1, Below (encDVs ds h).2 v) ∧
      ∃ n, (encDVs ds h).1.mapM (dec (encDVs ds h).2 n) = some ds
  | [], h, _ => ⟨Ext_refl h, by simp [encDVs], 0, by simp [encDVs]⟩
  | d :: ds, h, ⟨hf, hfs⟩ => by
    obtain ⟨e1, hb1, n1, hd1⟩ := encDV_spec d h hf
    obtain ⟨e2, hb2, n2, hd2⟩ := encDVs_spec ds (encDV d h).2 hfs
    refine ⟨Ext_trans e1 e2, fun v hv => ?_, max n1 n2, ?_⟩
    · simp only [encDVs, List.mem_cons] at hv
      rcases hv with rfl | hv
      · intro q a ea
        have := hb1 q a ((follow_Ext e2 q hb1 a).mp ea)
        exact Nat.lt_of_lt_of_le this e2.1
      · exact hb2 v hv
    · simp only [encDVs, List.mapM_cons]
      rw [dec_ext e2 hb1, dec_mono' hd1 (Nat.le_max_left _ _),
        mapM_dec_mono hd2 (Nat.le_max_right _ _)]
      rfl
end

end SpecLean.Layer4
