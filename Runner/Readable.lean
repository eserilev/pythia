import Runner.Main
import SpecLean.Gen.Readable

/-!
# The readable Lean on the EF vectors

Runs a case through the generated readable Lean (`SpecLean/Gen/Readable.lean`): decode the
start state and the arguments, run the readable functions, encode the result state and compare
its `hash_tree_root` with `post`. The oracle is the stub of `bls_setting` 0 and 2.
-/

namespace SpecLean.Runner

open SpecLean.Rd SpecLean.Rd.Gen

def rdSpec (B : Build) (c : Case) : Rd.Spec where
  sha256 := Tests.Sha256.hash
  containers := B.containers
  active := B.activeFields
  zero := fun d => zeros[d]?.getD Htr.zeroChunk
  blsVerify := fun _ _ _ => true
  blsFastAggregateVerify := fun _ _ _ => true
  blsAggregateVerify := fun _ _ _ => true
  blsKeyValidate := fun _ => true
  blsAggregatePKs := fun pks => (c.aggregates.lookup pks).getD stubPubkey
  blsG1Add := fun a _ => a
  blsG1Neg := fun a => a
  hashTreeRoot := fun h v => Htr.root (hasher B) h 64 v

def failTag : Fail → String
  | .invalid => "invalid"
  | .bug => "bug"

/-- The state that the interpreter computes, decoded, for a diff. -/
def interpState (B : Build) (c : Case) : Option BeaconState :=
  match runCalls (env B c) c.calls c.heap .none with
  | .ok (h, v) => dec_BeaconState h (if c.resultRoot then v else c.state)
  | .error _ => none

/-- The verdict of the readable Lean on a case. -/
def readableRun (B : Build) (c : Case) : Verdict :=
  let _ : Rd.Spec := rdSpec B c
  let _ : Cfg := Cfg.ofOverrides c.config
  let start : Option (SpecM BeaconState) :=
    if c.resultRoot then upgradeEntry c.heap c.state
    else (dec_BeaconState c.heap c.state).map pure
  match start with
  | none => .fail "readable: the start state does not decode"
  | some st0 =>
    let calls := if c.resultRoot then [] else c.calls
    let step (acc : Option (SpecM BeaconState)) (call : Call) : Option (SpecM BeaconState) := do
      let st ← acc
      match st with
      | .error e => some (.error e)
      | .ok s =>
        let f ← entries.lookup (B.nameOf call.fn)
        f s c.heap (call.args.drop 1)
    match calls.foldl step (some st0), c.post with
    | none, _ => .fail "readable: no entry point, or an argument does not decode"
    | some (.error f), none => .pass s!"readable invalid ({failTag f})"
    | some (.error f), some _ => .fail s!"readable: {failTag f}"
    | some (.ok _), none => .fail "readable: expected an error, got a result"
    | some (.ok s), some root =>
      let (v, h) := enc_BeaconState s Heap.empty
      match Htr.root (hasher B) h 64 v with
      | .ok r =>
        if r = root then .pass "readable"
        else
          let diff := match interpState B c with
            | some s' => s!" differs from the interpreter in {diffBeaconState s s'}"
            | none => ""
          .fail s!"readable root {hex r}{diff}"
      | .error e => .fail s!"readable hash_tree_root: {errTag e}"

end SpecLean.Runner
