import SpecLean.Interp
import SpecLean.Ssz
import Std.Data.HashMap

/-!
# A build for the runner

The generated tables of one serialized scope. The runner takes one, so that each preset has
its own executable.
-/

namespace SpecLean.Runner

structure Build where
  names : Array String
  containers : List (Name × List (Name × SszTy))
  activeFields : List (Name × List Nat)
  footprint : List (Name × List Name)
  /-- `Footprint f`: a parameter index and the steps from it. -/
  fnFootprint : List (Name × List (Nat × List Name))
  env : Oracle → Env
  /-- The id of each name. `Build.withIds` fills it. -/
  ids : Std.HashMap String Name := {}

def Build.withIds (B : Build) : Build :=
  { B with ids := B.names.foldl (init := {}) fun m s => m.insert s m.size }

def Build.nameOf (B : Build) (n : Name) : String := B.names[n]?.getD s!"#{n}"

end SpecLean.Runner
