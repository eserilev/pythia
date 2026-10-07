import Runner.Readable
import SpecLean.Validation.BlsBridge

/-!
# The runner's BLS oracle meets `OracleBls`

The EF vector runner runs the interpreter with `blsStub` and the readable Lean with `rdSpec`.
When the build names the BLS methods as the scope does, the pair meets `OracleBls`. So the
assumption of the proofs can be met.
-/

namespace SpecLean.Runner

open SpecLean SpecLean.Rd SpecLean.Validation.BlsBridge

/-- The oracle of the interpreter in the runner. -/
def runnerOracle (B : Build) (c : Case) : Oracle where
  sha256 := Tests.Sha256.hash
  hashTreeRoot := fun h v => Htr.root (hasher B) h 64 v
  bls := blsStub B c.aggregates

theorem runner_oracleBls (B : Build) (c : Case)
    (hV : B.nameOf Scope.Id.«Verify» = "Verify")
    (hF : B.nameOf Scope.Id.«FastAggregateVerify» = "FastAggregateVerify") :
    @OracleBls (rdSpec B c) (runnerOracle B c) := by
  letI : Rd.Spec := rdSpec B c
  constructor
  · intro f h args hf
    simp only [runnerOracle, blsStub]
    split <;> try rfl
    rename_i v _
    have hv : FlatArg v = true := hf v (by simp_all)
    cases v <;> simp_all [byteList, FlatArg]
  · intro h c1 c2 c3 pk msg sig
    simp [runnerOracle, blsStub, hV]; rfl
  · intro h pv pks c2 c3 msg sig _
    simp [runnerOracle, blsStub, hF]; rfl

end SpecLean.Runner
