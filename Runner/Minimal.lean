import Runner.Main
import Runner.Readable
import SpecLean.Gen.Scope

/-! The EF vector runner on the minimal preset build. -/

open SpecLean in
def main (args : List String) : IO UInt32 :=
  Runner.main { names := Scope.names, containers := Scope.containers,
                activeFields := Scope.activeFields, footprint := Scope.footprint,
                fnFootprint := Scope.fnFootprint,
                env := Scope.env } args (some Runner.readableRun)
