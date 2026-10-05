import SpecLean.Heap

/-!
# Environment

The globals of one build: spec functions, constants, types, builtins, modules and `config`,
and the oracle (SPEC 7.1, 8).
-/

namespace SpecLean

inductive Builtin where
  | len | range | enumerate | zip | sorted | min | max | sum | any | all | filter
  | list | tuple | set | dict | bytes | int | bool
  | sszSerialize
  /-- The spec function `sha256`, through the oracle. -/
  | sha256
  /-- The spec function `hash_tree_root`, through the oracle (SPEC 8, step 3 implements it). -/
  | hashTreeRoot
  deriving DecidableEq, Repr

/-- A module name in spec code. -/
inductive ModuleKind where
  /-- `bls`: every member is an oracle function. -/
  | bls
  /-- `fulu`, `electra` and so on: a member is the global of the same name in this build. -/
  | fork
  /-- `config`: a member is a runtime configuration value. -/
  | config
  deriving DecidableEq, Repr

inductive Global where
  | fn (f : FunctionDef)
  | builtin (b : Builtin)
  /-- An SSZ type used as a constructor, for example `Uint64(x)` or `Checkpoint(epoch=e)`. -/
  | type (t : SszTy)
  /-- A Python dataclass of the spec, for example `BlobParameters`. Its fields are in
  `Env.containers`. -/
  | dataclass (ty : Name)
  | const (v : Value)
  /-- A configuration value: `Env.config` holds it, under the same name. -/
  | configVar
  | module (k : ModuleKind)

/-- Interned names that the interpreter needs to know: method names and keyword names. -/
structure KnownNames where
  append : Name
  extend : Name
  index : Name
  count : Name
  copy : Name
  union : Name
  intersection : Name
  add : Name
  fromBytes : Name
  empty : Name
  hashTreeRoot : Name
  data : Name
  key : Name
  reverse : Name
  strict : Name
  get : Name
  bytes32 : Name
  root : Name
  little : String := "little"

/-- The oracle fields (SPEC 8). -/
structure Oracle where
  sha256 : List UInt8 → List UInt8
  hashTreeRoot : Heap → Value → Res (List UInt8)
  bls : Name → Heap → List Value → Res Value

structure Env where
  globals : List (Name × Global)
  /-- Field names and types of each container and dataclass, in order. -/
  containers : List (Name × List (Name × SszTy))
  /-- The interned name of the class `bytes`. -/
  bytesName : Name
  nm : KnownNames
  /-- The runtime configuration (`config.X`). Tests change it. -/
  config : List (Name × Value)
  /-- Oracle for `sha256`. -/
  sha256 : List UInt8 → List UInt8
  /-- Oracle for `hash_tree_root` until step 3 implements it in Lean. -/
  hashTreeRoot : Heap → Value → Res (List UInt8)
  /-- Oracle for `bls.f(args)`. -/
  bls : Name → Heap → List Value → Res Value

end SpecLean
