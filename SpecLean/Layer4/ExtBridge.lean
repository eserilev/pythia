import SpecLean.Layer4.GenBridge
import SpecLean.NoFill

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

end SpecLean.Layer4.ExtBridge
