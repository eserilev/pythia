import Runner.Main
import SpecLean.Gen.ScopeMainnet

/-! The EF vector runner on the mainnet preset build. -/

open SpecLean in
def main (args : List String) : IO UInt32 :=
  Runner.main { names := ScopeMainnet.names, containers := ScopeMainnet.containers,
                activeFields := ScopeMainnet.activeFields, footprint := ScopeMainnet.footprint,
                fnFootprint := ScopeMainnet.fnFootprint,
                env := ScopeMainnet.env } args
