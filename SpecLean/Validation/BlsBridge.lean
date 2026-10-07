import SpecLean.Gen.Readable

/-!
# BLS as an oracle on both sides

The interpreter calls the oracle field `sha.bls` with a method name, a heap and the argument
values. The readable Lean calls the `Spec.bls*` functions on bytes. The proofs assume one
property of the pair (`OracleBls`):

* On arguments without references, the oracle does not read the heap (`flat`).
* Each method gives the result of its readable function (`verify`, `fastAggregateVerify`).

`Runner.BlsOracle` shows that the stub oracle of the EF vector runner has this property, so
the assumption can be met.
-/

namespace SpecLean.Validation.BlsBridge

open SpecLean SpecLean.Rd SpecLean.Rd.Gen

/-- A value without references: the oracle needs no heap to read it. -/
def FlatArg : Value → Bool
  | .int _ | .bool _ | .lib _ | .str _ | .none | .bytes _ _ => true
  | _ => false

/-- The byte strings of a heap list of byte values. -/
def byteItems (h : Heap) : Value → Option (List Bytes)
  | .ref a => match h.objs a with
    | some (.list _ _ _ xs) => xs.mapM fun | .bytes _ b => some b | _ => none
    | _ => none
  | _ => none

structure OracleBls [Spec] (sha : Oracle) : Prop where
  /-- On arguments without references, the oracle does not read the heap. -/
  flat : ∀ f h args, (∀ v ∈ args, FlatArg v = true) → sha.bls f h args = sha.bls f Heap.empty args
  /-- `bls.Verify(pubkey, message, signature)`. -/
  verify : ∀ h (c1 c2 c3 : Name) (pk msg sig : Bytes),
    sha.bls Scope.Id.«Verify» h [.bytes c1 pk, .bytes c2 msg, .bytes c3 sig] =
      .ok (.bool (Spec.blsVerify pk msg sig))
  /-- `bls.FastAggregateVerify(pubkeys, message, signature)`, with the pubkeys in a heap list. -/
  fastAggregateVerify : ∀ h (pv : Value) (pks : List Bytes) (c2 c3 : Name) (msg sig : Bytes),
    byteItems h pv = some pks →
    sha.bls Scope.Id.«FastAggregateVerify» h [pv, .bytes c2 msg, .bytes c3 sig] =
      .ok (.bool (Spec.blsFastAggregateVerify pks msg sig))

end SpecLean.Validation.BlsBridge
