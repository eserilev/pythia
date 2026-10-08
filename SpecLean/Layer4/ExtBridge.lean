import SpecLean.Layer4.GenBridge
import SpecLean.NoFill
import SpecLean.ContRun
import SpecLean.Validation.FieldKeep

/-!
# Layer 4: a callee taken from a statement

`ExtOK` needs, for each callee taken from a statement, that the interpreter's call agrees with
the den result. A statement of the tactic (`ResultMatches`) gives the result and `Frame`. With
`callFn_noFill` (a call never fills a free address below `next`), `Frame` gives `Ext`.
-/

namespace SpecLean.Layer4.ExtBridge

open SpecLean SpecLean.Encode SpecLean.Layer4

theorem dec_exists {h : Heap} : ∀ (n : Nat) (v : Value) (d : DV), dec h n v = some d →
    ∀ q a, follow h v q = some (.ref a) → h.objs a ≠ none
  | 0, v, d, hd => by
    intro q a e
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr; simp [dec_zero_ref] at hd
    · exact absurd e (fun e' => follow_nonref_ref (fun b e => hr ⟨b, e⟩) e')
  | m + 1, v, d, hd => by
    intro q a e
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      rw [dec_ref_succ] at hd
      have hex : h.objs b ≠ none := by intro hn; rw [hn] at hd; simp at hd
      cases q with
      | nil => simp [follow] at e; subst e; exact hex
      | cons j q =>
        rw [follow_ref_cons] at e
        have kid : ∀ xs, okids (h.objs b) = some xs → ∀ ds, xs.mapM (dec h m) = some ds → h.objs a ≠ none := by
          intro xs hk ds hm
          rw [hk] at e
          simp only [Option.bind_some] at e
          cases hx : xs[j]? with
          | none => simp [hx] at e
          | some x =>
            simp only [hx, Option.bind_some] at e
            obtain ⟨c, -, hc⟩ := mapM_get' hm hx
            exact dec_exists m x c hc q a e
        cases hob : h.objs b with
        | none => exact absurd hob hex
        | some o =>
          rw [hob] at hd
          cases o with
          | container ty fs =>
            cases hm : fs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds => exact kid fs (by simp [okids, hob]) ds hm
          | list k el l xs =>
            cases hm : xs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds => exact kid xs (by simp [okids, hob]) ds hm
          | _ => simp at hd
    · exact absurd e (fun e' => follow_nonref_ref (fun b e => hr ⟨b, e⟩) e')

theorem normE_of_ne {e : SpecError} (h : e ≠ .outOfFuel) : normE e = SpecError.rep e.fail := by
  cases e <;> simp_all [normE]

theorem rep_ne_oof (f : Fail) : SpecError.rep f ≠ .outOfFuel := by cases f <;> simp [SpecError.rep]

theorem ext_of_frame {h h' : Heap} {vs : List Value} (hf : Frame h h' vs []) (hfr : Fresh h h')
    (hnf : ∀ a, a < h.next → h.objs a = none → h'.objs a = none) : Ext h h' := by
  refine ⟨hfr.1, hfr.2, fun a ha => ?_⟩
  by_cases hn : h.objs a = none
  · rw [hn]; exact hnf a ha hn
  · exact hf a hn (by rintro ⟨k, pat, q, hp, -⟩; exact absurd hp (List.not_mem_nil))

/-! ## A callee that writes, taken from a statement -/

/-- An object at a path from a decoded value is a container or a list. -/
theorem dec_kind {h : Heap} : ∀ (n : Nat) (v : Value) (d : DV), dec h n v = some d →
    ∀ q a, follow h v q = some (.ref a) →
      (∃ ty fs, h.objs a = some (.container ty fs)) ∨ (∃ k e l xs, h.objs a = some (.list k e l xs))
  | 0, v, d, hd => by
    intro q a e
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr; simp [dec_zero_ref] at hd
    · exact absurd e (fun e' => follow_nonref_ref (fun b e => hr ⟨b, e⟩) e')
  | m + 1, v, d, hd => by
    intro q a e
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      rw [dec_ref_succ] at hd
      cases q with
      | nil =>
        simp [follow] at e; subst e
        cases hob : h.objs b with
        | none => rw [hob] at hd; simp at hd
        | some o =>
          rw [hob] at hd
          cases o with
          | container ty fs => exact .inl ⟨ty, fs, rfl⟩
          | list k el l xs => exact .inr ⟨k, el, l, xs, rfl⟩
          | _ => simp at hd
      | cons j q =>
        rw [follow_ref_cons] at e
        have kid : ∀ xs, okids (h.objs b) = some xs → ∀ ds, xs.mapM (dec h m) = some ds →
            (∃ ty fs, h.objs a = some (.container ty fs)) ∨ (∃ k e l xs, h.objs a = some (.list k e l xs)) := by
          intro xs hk ds hm
          rw [hk] at e
          simp only [Option.bind_some] at e
          cases hx : xs[j]? with
          | none => simp [hx] at e
          | some x =>
            simp only [hx, Option.bind_some] at e
            obtain ⟨c, -, hc⟩ := mapM_get' hm hx
            exact dec_kind m x c hc q a e
        cases hob : h.objs b with
        | none => rw [hob] at hd; simp at hd
        | some o =>
          rw [hob] at hd
          cases o with
          | container ty fs =>
            cases hm : fs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds => exact kid fs (by simp [okids, hob]) ds hm
          | list k el l xs =>
            cases hm : xs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds => exact kid xs (by simp [okids, hob]) ds hm
          | _ => simp at hd
    · exact absurd e (fun e' => follow_nonref_ref (fun b e => hr ⟨b, e⟩) e')

/-- Each old list keeps its kind, element type, limit and the references at its old indices. It
grows only by items that reach new objects. Obligation of the tactic's `_pk` statements. -/
def ListKeep (h h' : Heap) : Prop :=
  ∀ a k e l xs, h.objs a = some (.list k e l xs) → ∃ xs', h'.objs a = some (.list k e l xs') ∧
    xs.length ≤ xs'.length ∧ (∀ (i : Nat) x y, xs[i]? = some x → xs'[i]? = some y → RefEq x y) ∧
    ∀ (i : Nat) y, xs.length ≤ i → xs'[i]? = some y → ∀ q b, follow h' y q = some (.ref b) →
      h.next ≤ b ∧ b < h'.next

/-- Each new object that the arguments reach has one path from them. Obligation of the tactic. -/
def NewOnce (h h' : Heap) (vs : List Value) : Prop :=
  ∀ kg q b kg' q', at? h' vs kg q = some (.ref b) → h.next ≤ b →
    at? h' vs kg' q' = some (.ref b) → kg' = kg ∧ q' = q

/-- A field that the callee rebinds keeps its reference, or stays flat. -/
def RbRefEq (h h' : Heap) (rb : List (Name × Nat)) : Prop :=
  ∀ a ty fs fs' (i : Nat) x y, h.objs a = some (.container ty fs) → h'.objs a = some (.container ty fs') →
    (ty, i) ∈ rb → fs[i]? = some x → fs'[i]? = some y → RefEq x y

theorem list_eq_of_get? {xs ys : List Value} (h : ∀ i : Nat, ys[i]? = xs[i]?) : ys = xs :=
  List.ext_getElem? h

/-- The old objects of a writer keep their shape. -/
theorem writer_skel {env : Env} {h h' : Heap} {vs : List Value} {roots : List DV} {fp : Footprint}
    {rb : List (Name × Nat)} (hdec : DecArgs h vs roots) (hfr : Frame h h' vs fp) (hfs : Fresh h h')
    (hnf : ∀ a, a < h.next → h.objs a = none → h'.objs a = none) (hfk : FieldKeep h h' rb)
    (hrb : RbRefEq h h' rb) (hlk : ListKeep h h') (hcw : ContRun.CW env h) (hcw' : ContRun.CW env h')
    (hT : ∀ p ∈ rb, ∃ ffs, env.containers.lookup p.1 = some ffs) : Skel h h' := by
  refine ⟨hfs.1, hfs.2, fun a ha => ?_⟩
  cases ho : h.objs a with
  | none => exact .inl (by rw [hnf a ha ho])
  | some o =>
  by_cases hnat : ¬ AtFp h vs fp a
  · exact .inl (by rw [hfr a (by rw [ho]; simp) hnat, ho])
  have hat : AtFp h vs fp a := Classical.not_not.mp hnat
  obtain ⟨k, pat, q, -, -, -, hq⟩ := hat
  obtain ⟨w, hw, hf⟩ := at?_some hq
  have hlen := hdec.1
  obtain ⟨d, hd⟩ : ∃ d, roots[k]? = some d := by
    have : k < vs.length := (List.getElem?_eq_some_iff.mp hw).1
    exact ⟨roots[k], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨n, hn⟩ := hdec.2 k w d hw hd
  rcases dec_kind n w d hn q a hf with ⟨ty, fs, hc⟩ | ⟨kd, el, l, xs, hl⟩
  · rw [hc] at ho; cases ho
    obtain ⟨fs', hc', hkeep⟩ := hfk a ty fs hc
    refine .inr ⟨.container ty fs, .container ty fs', rfl, hc', ?_⟩
    refine ⟨rfl, ?_, fun i x y hx hy => ?_⟩
    · by_cases hin : ∃ i, (ty, i) ∈ rb
      · obtain ⟨i, hi⟩ := hin
        obtain ⟨ffs, hffs⟩ := hT _ hi
        rw [hcw a ty fs ffs hc hffs, hcw' a ty fs' ffs hc' hffs]
      · have : fs' = fs := list_eq_of_get? fun i => hkeep i (fun hi => hin ⟨i, hi⟩)
        rw [this]
    · by_cases hi : (ty, i) ∈ rb
      · exact hrb a ty fs fs' i x y hc hc' hi hx hy
      · rw [hkeep i hi, hx] at hy; cases hy; exact RefEq.refl _
  · rw [hl] at ho; cases ho
    obtain ⟨xs', hl', hle, hre, hnew⟩ := hlk a kd el l xs hl
    refine .inr ⟨.list kd el l xs, .list kd el l xs', rfl, hl', ?_⟩
    exact ⟨rfl, rfl, rfl, hle, hre, fun i y hi hy q b e => hnew i y hi hy q b e⟩

/-- A writer callee from its statement: `FnRel` from the frame facts of the tactic and the new
argument trees. -/
theorem writer_fnRel {env : Env} {h h' : Heap} {vs : List Value} {roots roots' : List DV}
    {fp : Footprint} {rb : List (Name × Nat)} (hfpne : fp ≠ []) (hdec : DecArgs h vs roots)
    (hfr : Frame h h' vs fp) (hfs : Fresh h h')
    (hnf : ∀ a, a < h.next → h.objs a = none → h'.objs a = none) (hfk : FieldKeep h h' rb)
    (hrb : RbRefEq h h' rb) (hlk : ListKeep h h') (hno : NewOnce h h' vs)
    (hcw : ContRun.CW env h) (hcw' : ContRun.CW env h')
    (hT : ∀ p ∈ rb, ∃ ffs, env.containers.lookup p.1 = some ffs) (hda : DecArgs h' vs roots') :
    FnRel fp h vs (.ok (.val .none, roots')) (.ok (.none, h')) :=
  ⟨⟨rfl, rfl⟩, trivial, hda, hfr, writer_skel hdec hfr hfs hnf hfk hrb hlk hcw hcw' hT,
    fun e => absurd e hfpne, hno⟩

/-! ## A callee that returns a new list of flat items -/

theorem mapM_dec_flat {h : Heap} (m : Nat) : ∀ (xs : List Value), (∀ x ∈ xs, Flat x = true) →
    xs.mapM (dec h m) = some (xs.map DV.leaf)
  | [], _ => rfl
  | x :: xs, hf => by
    simp only [List.mapM_cons, List.map_cons, dec_flat (hf x (by simp)) m,
      mapM_dec_flat m xs (fun y hy => hf y (by simp [hy]))]
    rfl

theorem follow_flatList {h : Heap} {a : Nat} {xs : List Value}
    (ho : h.objs a = some (.list .pyList .any none xs)) (hf : ∀ x ∈ xs, Flat x = true) :
    ∀ q b, follow h (.ref a) q = some (.ref b) → q = [] ∧ b = a := by
  intro q b e
  cases q with
  | nil => simp [follow] at e; exact ⟨rfl, e.symm⟩
  | cons j q =>
    rw [follow_ref_cons, ho] at e
    simp only [okids, Option.bind_some] at e
    cases hx : xs[j]? with
    | none => simp [hx] at e
    | some x =>
      simp only [hx, Option.bind_some] at e
      have hfx := hf x (List.mem_of_getElem? hx)
      exact absurd e (fun e' => follow_nonref_ref (fun c ec => by subst ec; simp [Flat] at hfx) e')

/-- The result of a callee that returns a new list of flat items (`ListRes`) is its tree. -/
theorem listRes_rel {α : Type} {h h' : Heap} {vs : List Value} {roots : List DV} {w : Value}
    (r : List α) (f : α → Value) (hf : ∀ y, Flat (f y) = true)
    (hl : Validation.Steps.ListRes h h' w (r.map f)) (hwf : HeapWF h) (hdec : DecArgs h vs roots)
    (hba : BelowArgs h vs) (he : Ext h h') :
    ERel h' vs (.tree (.list .pyList .any none (r.map fun y => DV.leaf (f y)))) w ∧
      TLo h.next h' (.tree (.list .pyList .any none (r.map fun y => DV.leaf (f y)))) w := by
  obtain ⟨a, rfl, hge, ho⟩ := hl
  have hfl : ∀ x ∈ r.map f, Flat x = true := by
    intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact hf y
  have hd : dec h' 1 (.ref a) = some (.list .pyList .any none (r.map fun y => DV.leaf (f y))) := by
    rw [dec_ref_succ, ho]
    simp only [mapM_dec_flat 0 _ hfl, List.map_map]
    rfl
  refine ⟨⟨⟨1, hd⟩, fun q b e k p ep => ?_⟩, fun q b e => ?_⟩
  · obtain ⟨-, rfl⟩ := follow_flatList ho hfl q b e
    have := at?_below0 hwf hdec ((at?_Ext he hba k p b).mp ep)
    omega
  · obtain ⟨-, rfl⟩ := follow_flatList ho hfl q b e
    exact hge

end SpecLean.Layer4.ExtBridge
