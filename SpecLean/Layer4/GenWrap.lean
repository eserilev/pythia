import SpecLean.Layer4.GenSteps

/-!
# Layer 4: from a generated `den` theorem to SPEC 9.2

A generated theorem says that `den` of a function, mapped through `SpecError.fail`, is the
readable function. `l4_wrap` turns it into a `ResultMatches` of the interpreter, by
`denote_sound_calls`, for each fuel at least the fuel of the theorem.
-/

namespace SpecLean.Layer4.GenWrap

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd

attribute [local instance high] LibModel.toLibValues

variable [ExtTab]

theorem l4_wrap {sha : Oracle} {fps : Name → Footprint} {gfp fp : Footprint} {fid : Name}
    {d : FunctionDef} (hg : (Scope.env sha).globals.lookup fid = some (.fn d)) {h : Heap}
    (hwf : HeapWF h) (hh : Examples2.HtrDec (Scope.env sha)) {vs : List Value} {roots : List DV} (hdec : DecArgs h vs roots)
    (hw : WTree h vs fp) {n : Nat} {α : Type} {r : SpecM α} {g : α → DRes × List DV}
    (hden : ((den (Scope.env sha) fps n).fn fp d roots).map (Except.mapError SpecError.fail) =
      some (g <$> r))
    {E : α → Heap → Value → Prop}
    (hE : ∀ x h' v, ERel h' vs (g x).1 v ∧ DecArgs h' vs (g x).2 → E x h' v)
    (hX : ExtOK (Scope.env sha) := by first | assumption | exact extOK_none _) :
    ResultMatches gfp fp h vs E (interp (Scope.env sha) n fid vs h) r := by
  cases hd : (den (Scope.env sha) fps n).fn fp d roots with
  | none => rw [hd] at hden; cases hden
  | some r0 =>
    rw [hd] at hden
    have hm := denote_sound_calls (Scope.env sha) fps (Examples2.libFlat_ssz _ (Examples2.nmOK_scope _) hh) hX gfp fp hg hdec hw hwf hd
    simp only [Option.map_some, Option.some.injEq] at hden
    rw [hden] at hm
    exact Examples.resultMatches_map hE hm

/-- More fuel gives the same result. -/
theorem l4_mono {sha : Oracle} {gfp fp : Footprint} {h : Heap} {vs : List Value} {α : Type}
    {E : α → Heap → Value → Prop} {fid : Name} {n fuel : Nat} (hf : n ≤ fuel) {r : SpecM α}
    (hm : ResultMatches gfp fp h vs E (interp (Scope.env sha) n fid vs h) r) :
    ResultMatches gfp fp h vs E (interp (Scope.env sha) fuel fid vs h) r :=
  Examples2.resultMatches_mono hf hm

/-- The decoded arguments: a flat value is a leaf. -/
theorem dec_leaf {h : Heap} {v : Value} (hv : Flat v = true) : ∃ n, dec h n v = some (.leaf v) :=
  ⟨0, dec_flat hv 0⟩

theorem decArgs_cons {h : Heap} {v : Value} {vs : List Value} {d : DV} {ds : List DV}
    (hd : ∃ n, dec h n v = some d) (hds : DecArgs h vs ds) : DecArgs h (v :: vs) (d :: ds) := by
  refine ⟨by simp [hds.1], fun k w e hw he => ?_⟩
  cases k with
  | zero => simp at hw he; subst hw; subst he; exact hd
  | succ k => exact hds.2 k w e (by simpa using hw) (by simpa using he)

theorem decArgs_nil (h : Heap) : DecArgs h [] [] := ⟨rfl, fun k _ _ hw _ => by simp at hw⟩

/-- A tree argument after the call: its decoding. -/
theorem decArgs_get {h : Heap} {vs : List Value} {ds : List DV} (hds : DecArgs h vs ds) (k : Nat)
    {v : Value} {d : DV} (hv : vs[k]? = some v) (hd : ds[k]? = some d) : ∃ n, dec h n v = some d :=
  hds.2 k v d hv hd

end SpecLean.Layer4.GenWrap
