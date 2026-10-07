import SpecLean.Layer4.Sound
import SpecLean.Layer4.Skel

/-!
# Layer 4 spike: the theorem for a whole function

`denote_sound` is the contract of SPEC 9.2 for every function whose denotation gives a result:
`DecArgs` and `WTree` over the footprint before; `ResultMatches` after.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

variable [LibModel]

/-- Each argument decodes to its tree. -/
def DecArgs (h : Heap) (vs : List Value) (roots : List DV) : Prop :=
  roots.length = vs.length ∧
    ∀ (k : Nat) (v : Value) (d : DV), vs[k]? = some v → roots[k]? = some d → ∃ n, dec h n v = some d

theorem slot_rel {h : Heap} {vs : List Value} {roots : List DV} (hdec : DecArgs h vs roots)
    {i : Nat} {v : Value} (hv : vs[i]? = some v) : ERel h vs (slot roots i) v := by
  have hi : i < roots.length := hdec.1 ▸ (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨n, hn⟩ := hdec.2 i v roots[i] hv (List.getElem?_eq_getElem hi)
  unfold slot
  rw [List.getElem?_eq_getElem hi]
  by_cases hl : ∃ u, roots[i] = .leaf u
  · obtain ⟨u, hu⟩ := hl
    rw [hu] at hn ⊢
    obtain ⟨rfl, hf⟩ := dec_leaf hn
    exact ⟨rfl, hf⟩
  · obtain ⟨a, -, -, rfl, -, -, -⟩ := dec_node hn (fun u e => hl ⟨u, e⟩)
    revert hl
    cases roots[i] with
    | leaf u => intro hl; exact absurd ⟨u, rfl⟩ hl
    | cont _ _ => intro _; exact ⟨a, rfl, by simp [at?, hv, follow]⟩
    | list _ _ _ _ => intro _; exact ⟨a, rfl, by simp [at?, hv, follow]⟩

/-- `bindArgs.go` binds the parameters as `initLoc` does. -/
theorem go_rel {h : Heap} {vs : List Value} {roots : List DV} (hdec : DecArgs h vs roots)
    : ∀ (ps : List (Name × Nat)) (dl : Name → Option DRes) (L : Locals),
      (∀ x, LRel h vs (dl x) (L x)) → (∀ q ∈ ps, q.2 < vs.length) →
      ∃ L', (∀ dfs fd, bindArgs.go dfs vs [] fd L ps = .ok L') ∧
        ∀ x, LRel h vs (initLoc roots dl ps x) (L' x)
  | [], dl, L, hl, _ => ⟨L, fun _ _ => by simp [bindArgs.go], hl⟩
  | (x, i) :: rest, dl, L, hl, hps => by
    have hi : i < vs.length := hps (x, i) (by simp)
    have hv : vs[i]? = some vs[i] := List.getElem?_eq_getElem hi
    have hl' : ∀ y, LRel h vs (setLoc dl x (slot roots i) y) ((L.set x vs[i]) y) := by
      intro y
      simp only [setLoc, Locals.set_apply]
      split
      · exact slot_rel hdec hv
      · exact hl y
    obtain ⟨L', hgo, hrel⟩ := go_rel hdec rest _ _ hl' (fun q hq => hps q (by simp [hq]))
    refine ⟨L', fun dfs fd => ?_, hrel⟩
    rw [bindArgs.go]
    simp [hv, hgo]

theorem callValue_glob_fn {env : Env} (n : Nat) {g : Name} {d : FunctionDef} (vs : List Value)
    (h : Heap) (hg : env.globals.lookup g = some (.fn d)) :
    callValue env n (.glob g) vs [] h = callFn env n d.params (.stmts d.body) Locals.empty vs [] h := by
  rw [callValue.eq_def]; simp only [hg, frame_eq]

/-- The arguments that decode reach only objects below `next`. -/
theorem at?_below0 {h : Heap} (hwf : HeapWF h) {vs : List Value} {roots : List DV}
    (hdec : DecArgs h vs roots) {k : Nat} {q : List Nat} {b : Nat} (e : at? h vs k q = some (.ref b)) :
    b < h.next := by
  obtain ⟨v, hv, hf⟩ := at?_some e
  have hk : k < roots.length := by
    have := (List.getElem?_eq_some_iff.mp hv).1; rw [hdec.1]; exact this
  obtain ⟨n, hn⟩ := hdec.2 k v _ hv (List.getElem?_eq_getElem hk)
  exact dec_below hwf n v _ hn q b hf

/-- The fragment theorem. For a function `f` whose denotation gives `r`: under `WTree` over the
footprint `fp`, the interpreter with fuel at least `bDep body + 1` matches `r`. -/
theorem denote_sound (env : Env) (hcf : CoerceFlat env) (gfp fp : Footprint) {f : Name}
    {d : FunctionDef} (hg : env.globals.lookup f = some (.fn d)) {h : Heap} {vs : List Value}
    {roots : List DV} (hdec : DecArgs h vs roots) (hw : WTree h vs fp) (hwf : HeapWF h)
    {r : Res (Value × List DV)} (hd : denoteFn env fp d roots = some r) :
    ∀ fuel, bDep d.body + 1 ≤ fuel →
      ResultMatches gfp fp h vs (fun (x : Value × List DV) h' v => v = x.1 ∧ DecArgs h' vs x.2)
        (interp env fuel f vs h) (r.mapError SpecError.fail) := by
  intro fuel hfuel
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  unfold denoteFn at hd
  split at hd
  · next hc =>
    obtain ⟨hdef, hva, hnl⟩ := hc
    have hlen : d.params.names.length = vs.length := hnl.trans hdec.1
    obtain ⟨L0, hgo, hrel⟩ := go_rel hdec d.params.names.zipIdx (fun _ => none) Locals.empty (fun x => by simp [LRel])
      (fun q hq => by
        obtain ⟨x, i⟩ := q
        have := (List.mem_zipIdx hq).2.1
        simp at this ⊢; omega)
    have hI : SInv fp h h vs { roots, loc := initLoc roots (fun _ => none) d.params.names.zipIdx } L0 :=
      ⟨⟨hdec.1, hdec.2, hrel⟩, hw, fun _ _ _ e => e, fun _ _ _ e => .inl e,
        fun k q b _ _ e hb _ => absurd (at?_below0 hwf hdec e) (by omega),
        fun k q b e => at?_below0 hwf hdec e, fun _ _ => Iff.rfl, Frame_refl h vs fp, Fresh_refl h⟩
    have hB := block_sound (stmt_sound env hcf fp h vs hwf m) d.body
      ⟨roots, initLoc roots (fun _ => none) d.params.names.zipIdx⟩ L0 h
    dsimp only at hd
    rw [interp, callName, callValue_glob_fn _ _ _ hg, callFn]
    simp only [hdef, evalList, bindArgs, hlen, gt_iff_lt, Nat.lt_irrefl, false_and, ↓reduceIte,
      List.any_nil, Bool.false_eq_true, hgo, hva, Except.bind_ok', Except.pure_ok', exb_ok]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨⟨o, s1⟩, he, hd2⟩
    · have := hB _ hI he (by omega)
      revert this
      cases execBlock env m L0 h d.body with
      | error e' =>
        rintro ⟨rfl, hne⟩
        simp only [exb_err, Except.bind_error', Except.mapError, ResultMatches]
        exact ⟨hne, trivial⟩
      | ok q => intro h; cases h
    · have := hB _ hI he (by omega)
      revert this
      cases execBlock env m L0 h d.body with
      | error e' => intro h; cases h
      | ok q =>
        obtain ⟨o', L1, h1⟩ := q
        rintro ⟨rfl, hI1⟩
        have post : Frame h h1 vs fp ∧ Fresh h h1 ∧ NoNewPaths h h1 vs gfp :=
          ⟨hI1.frame, hI1.fresh, noNewPaths_of_reach fun k q b e => hI1.refsB k q b e⟩
        have da : DecArgs h1 vs s1.roots := ⟨hI1.r.len, hI1.r.roots⟩
        simp only [Except.bind_ok', exb_ok]
        cases o' with
        | ret v =>
          simp [DM.ok] at hd2; subst hd2
          simp only [Except.mapError, ResultMatches]
          exact ⟨⟨trivial, da⟩, post⟩
        | _ =>
          simp [DM.ok] at hd2; subst hd2
          simp only [Except.mapError, ResultMatches]
          exact ⟨⟨trivial, da⟩, post⟩
  · cases hd

end SpecLean.Layer4
