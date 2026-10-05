"""Convert EF test vectors into case files for the Lean runner (SPEC 11, item 1).

Run from the consensus-specs checkout, in its uv environment:

    cd ../consensus-specs-safe
    uv run python ../consensus-specs-lean/tools/ef_cases.py VECTORS_DIR OUT_DIR

`VECTORS_DIR` is `<preset>/gloas` of a vector tree. The script writes one `.case` file per case
under `OUT_DIR/<runner>/<handler>/`, and `OUT_DIR/skipped.txt` with each skipped case and why.

A case file is a list of calls on one state. The runner applies them in order. It then compares
`hash_tree_root` of the state (or of the last result) with `post`. A case with no `post` passes
when a call raises a Python exception.

Encoding, all integers little-endian:
- `str`: u16 length, UTF-8 bytes.
- case: b"SLC1", str id, u8 bls_setting, value of the start state, u16 call count, calls,
  u8 result (0: the state, 1: the return value of the last call), u8 has_post, 32-byte root,
  u16 config count, (str name, value) each, u16 table count, (u16 n, n * 48 bytes, 48 bytes)
  each: inputs and results of `bls.AggregatePKs`.
- call: str function, u8 argument count, values.
- value: `S` the state; `u` str class ("" for a width class), u16 bits, bytes; `o` u8 SSZ
  Boolean; `b` u8 Python bool; `y` str class, u32 length, bytes; `c` str class, u16 count,
  values; `l` u8 kind, type, u8 has_limit, u64 limit, u32 count, values.
- type: `U` str class, u16 bits; `O`; `Y` str class, u32 length; `C` str class; `L` u8 kind,
  type, u8 has_limit, u64 limit.
- list kinds: 0 list, 1 vector, 2 progressiveList, 3 bitlist, 4 bitvector, 5 progressiveBitlist.
"""

import struct
import sys
from pathlib import Path

import snappy
import ssz.bitfields
import ssz.boolean
import ssz.byte_arrays
import ssz.collections
import ssz.container
import ssz.uint
import yaml
from eth_consensus_specs.fulu import mainnet as fulu_mainnet
from eth_consensus_specs.fulu import minimal as fulu_minimal
from eth_consensus_specs.gloas import mainnet as spec_mainnet
from eth_consensus_specs.gloas import minimal as spec_minimal
from eth_consensus_specs.utils import bls

BaseUint = ssz.uint.BaseUint
PREV_FORK = "fulu"


def prev_spec(spec):
    return fulu_mainnet if spec is spec_mainnet else fulu_minimal

KINDS = {"list": 0, "vector": 1, "progressiveList": 2, "bitlist": 3, "bitvector": 4,
         "progressiveBitlist": 5}


class Skip(Exception):
    pass


# The state argument of a call.
STATE = object()


class Writer:
    def __init__(self, spec, prev=""):
        self.spec = spec
        # A class of an older fork that the build does not have gets the fork's prefix.
        self.prev = prev
        self.out = bytearray()

    def cname(self, cls):
        name = cls.__name__
        if getattr(self.spec, name, None) is cls:
            return name
        return f"{self.prev}.{name}"

    def u8(self, n):
        self.out += struct.pack("<B", n)

    def u16(self, n):
        self.out += struct.pack("<H", n)

    def u32(self, n):
        self.out += struct.pack("<I", n)

    def u64(self, n):
        self.out += struct.pack("<Q", n)

    def str(self, s):
        b = s.encode()
        self.u16(len(b))
        self.out += b

    def uint_class(self, cls):
        parents = [b for b in cls.__bases__ if issubclass(b, BaseUint)]
        if parents == [BaseUint]:
            return ""
        if len(parents) == 1 and parents[0].__bases__ == (BaseUint,):
            return self.cname(cls)
        raise Skip(f"uint class depth: {cls.__name__}")

    def list_kind(self, t):
        for kind, base in [("progressiveBitlist", ssz.bitfields.ProgressiveBitList),
                           ("bitlist", ssz.bitfields.BitList),
                           ("bitvector", ssz.bitfields.BitVector)]:
            if issubclass(t, base):
                limit = t.LENGTH if kind == "bitvector" else getattr(t, "LIMIT", None)
                return kind, None, limit
        if issubclass(t, ssz.byte_arrays.ByteList):
            return "list", ssz.uint.Uint8, t.LIMIT
        for kind, base in [("progressiveList", ssz.collections.ProgressiveList),
                           ("list", ssz.collections.List), ("vector", ssz.collections.Vector)]:
            if issubclass(t, base):
                limit = None if kind == "progressiveList" else (
                    t.LIMIT if kind == "list" else t.LENGTH)
                return kind, t.ELEMENT_TYPE, limit
        return None

    def limit(self, limit):
        self.u8(0 if limit is None else 1)
        self.u64(0 if limit is None else limit)

    def ty(self, t):
        if issubclass(t, BaseUint):
            self.out += b"U"
            self.str(self.uint_class(t))
            self.u16(t.BITS)
        elif issubclass(t, ssz.boolean.Boolean):
            self.out += b"O"
        elif issubclass(t, ssz.byte_arrays.ByteVector):
            self.out += b"Y"
            self.str(self.cname(t))
            self.u32(t.LENGTH)
        elif issubclass(t, (ssz.container.Container, ssz.container.ProgressiveContainer)):
            self.out += b"C"
            self.str(self.cname(t))
        else:
            lk = self.list_kind(t)
            if lk is None:
                raise Skip(f"SSZ type {t}")
            kind, elem, limit = lk
            self.out += b"L"
            self.u8(KINDS[kind])
            if elem is None:
                self.out += b"O"
            else:
                self.ty(elem)
            self.limit(limit)

    def value(self, v, t=None):
        t = t or type(v)
        if issubclass(t, BaseUint):
            self.out += b"u"
            self.str(self.uint_class(t))
            self.u16(t.BITS)
            self.out += int(v).to_bytes(t.BITS // 8, "little")
        elif issubclass(t, ssz.boolean.Boolean):
            self.out += b"o"
            self.u8(1 if v else 0)
        elif issubclass(t, ssz.byte_arrays.ByteVector):
            self.out += b"y"
            self.str(self.cname(t))
            self.u32(len(v))
            self.out += bytes(v)
        elif issubclass(t, (ssz.container.Container, ssz.container.ProgressiveContainer)):
            self.out += b"c"
            self.str(self.cname(t))
            self.u16(len(t._FIELD_TYPES))
            for f, ft in t._FIELD_TYPES:
                self.value(getattr(v, f), ft)
        else:
            lk = self.list_kind(t)
            if lk is None:
                raise Skip(f"SSZ value of {t}")
            kind, elem, limit = lk
            self.out += b"l"
            self.u8(KINDS[kind])
            if elem is None:
                self.out += b"O"
            else:
                self.ty(elem)
            self.limit(limit)
            xs = list(v)
            self.u32(len(xs))
            for x in xs:
                if elem is None:
                    self.out += b"o"
                    self.u8(1 if x else 0)
                elif elem is ssz.uint.Uint8 and isinstance(x, int) and not isinstance(x, BaseUint):
                    self.value(ssz.uint.Uint8(x), elem)
                else:
                    self.value(x, elem)

    def py_value(self, v):
        if v is STATE:
            self.out += b"S"
        elif type(v) is bool:
            self.out += b"b"
            self.u8(1 if v else 0)
        else:
            self.value(v)


def load(path: Path, cls):
    return cls.decode_bytes(snappy.decompress(path.read_bytes()))


def read_yaml(path: Path):
    return yaml.safe_load(path.read_text()) if path.exists() else {}


OPERATIONS = {
    "attestation": ("process_attestation", "attestation", "Attestation"),
    "attester_slashing": ("process_attester_slashing", "attester_slashing", "AttesterSlashing"),
    "block_header": ("process_block_header", "block", "BeaconBlock"),
    "bls_to_execution_change": ("process_bls_to_execution_change", "address_change",
                                "SignedBLSToExecutionChange"),
    "builder_deposit_request": ("process_builder_deposit_request", "builder_deposit_request",
                                "BuilderDepositRequest"),
    "builder_exit_request": ("process_builder_exit_request", "builder_exit_request",
                             "BuilderExitRequest"),
    "consolidation_request": ("process_consolidation_request", "consolidation_request",
                              "ConsolidationRequest"),
    "deposit_request": ("process_deposit_request", "deposit_request", "DepositRequest"),
    "execution_payload_bid": ("process_execution_payload_bid", "execution_payload_bid",
                              "SignedExecutionPayloadBid"),
    "parent_execution_payload": ("process_parent_execution_payload", "block", "BeaconBlock"),
    "payload_attestation": ("process_payload_attestation", "payload_attestation",
                            "PayloadAttestation"),
    "proposer_slashing": ("process_proposer_slashing", "proposer_slashing", "ProposerSlashing"),
    "sync_aggregate": ("process_sync_aggregate", "sync_aggregate", "SyncAggregate"),
    "voluntary_exit": ("process_voluntary_exit", "voluntary_exit", "SignedVoluntaryExit"),
    "voluntary_exit_churn": ("process_voluntary_exit", "voluntary_exit", "SignedVoluntaryExit"),
    "withdrawal_request": ("process_withdrawal_request", "withdrawal_request",
                           "WithdrawalRequest"),
    "withdrawals": ("process_withdrawals", None, None),
}

# Cases that need real BLS, but whose meta.yaml has no `bls_setting: 1`: the test checks an
# invalid signature and lacks `@always_bls` upstream.
NEEDS_BLS = {
    "operations/payload_attestation/process_payload_attestation_invalid_signature",
    "fork/fork/fork_invalid_builder_deposit_followed_by_valid_builder_deposit",
    "fork/fork/fork_invalid_validator_deposit_followed_by_builder_credentials",
}

# Epoch processing handlers whose function name is not `process_<handler>`.
EPOCH_FUNCTIONS = {"pending_deposits_churn": "process_pending_deposits"}


def calls_for(spec, runner, handler, case: Path, meta, pre):
    """The calls of one case, and whether the result is the state (0) or the last value (1)."""
    if runner == "operations":
        fn, name, cls = OPERATIONS[handler]
        args = [STATE]
        if name is not None:
            args.append(load(case / f"{name}.ssz_snappy", getattr(spec, cls)))
        if handler == "attestation":
            args.append(spec.Slot(meta.get("parent_slot", 0)))
        return [(fn, args)], 0
    if runner == "epoch_processing":
        return [(EPOCH_FUNCTIONS.get(handler, f"process_{handler}"), [STATE])], 0
    if runner == "sanity" and handler == "slots":
        n = int(yaml.safe_load((case / "slots.yaml").read_text()))
        return [("process_slots", [STATE, spec.Slot(pre.slot + n)])], 0
    if runner == "fork":
        return [("upgrade_to_gloas", [STATE])], 1
    if (runner == "sanity" and handler == "blocks") or runner == "finality":
        n = meta.get("blocks_count", 0)
        blocks = [load(case / f"blocks_{i}.ssz_snappy", spec.SignedBeaconBlock) for i in range(n)]
        return [("state_transition", [STATE, b]) for b in blocks], 0
    raise Skip(f"runner {runner}/{handler}")


def config_overrides(spec, case: Path):
    path = case / "config.yaml"
    if not path.exists():
        return []
    out = []
    for name, raw in read_yaml(path).items():
        default = getattr(spec.config, name, None)
        if default is None or isinstance(default, str):
            continue
        if isinstance(default, bytes):
            # YAML reads an unquoted 0x... value as an int.
            data = (raw.to_bytes(len(default), "big") if isinstance(raw, int)
                    else bytes.fromhex(str(raw)[2:]))
            value = type(default)(data)
        elif isinstance(default, int):
            value = type(default)(int(raw))
        else:
            if raw in ([], None) and not default:
                continue
            raise Skip(f"config value {name}")
        if value != default:
            out.append((name, value))
    return out


def aggregate_table(spec, states):
    table = {}
    for st in states:
        for committee in (st.current_sync_committee, st.next_sync_committee):
            key = b"".join(bytes(p) for p in committee.pubkeys)
            table[key] = (len(committee.pubkeys), bytes(committee.aggregate_pubkey))
    return table


def encode_case(spec, runner, handler, case: Path) -> bytes:
    meta = read_yaml(case / "meta.yaml")
    w = Writer(spec, PREV_FORK)
    w.out += b"SLC1"
    w.str(f"{runner}/{handler}/{case.name}")
    w.u8(meta.get("bls_setting", 0))
    pre_spec = prev_spec(spec) if runner == "fork" else spec
    pre = load(case / "pre.ssz_snappy", pre_spec.BeaconState)
    calls, result = calls_for(spec, runner, handler, case, meta, pre)
    w.value(pre)
    w.u16(len(calls))
    for fn, args in calls:
        w.str(fn)
        w.u8(len(args))
        for a in args:
            w.py_value(a)
    w.u8(result)
    post_path = case / "post.ssz_snappy"
    states = [pre] if runner != "fork" else []
    if post_path.exists():
        post = load(post_path, spec.BeaconState)
        states.append(post)
        w.u8(1)
        w.out += bytes(post.hash_tree_root())
    else:
        w.u8(0)
        w.out += bytes(32)
    overrides = config_overrides(spec, case)
    w.u16(len(overrides))
    for name, value in overrides:
        w.str(name)
        w.value(value)
    table = aggregate_table(spec, states)
    w.u16(len(table))
    for key, (n, agg) in table.items():
        w.u16(n)
        w.out += key
        w.out += agg
    return bytes(w.out)


def main():
    vectors, out = Path(sys.argv[1]), Path(sys.argv[2])
    spec = spec_mainnet if "mainnet" in vectors.parts else spec_minimal
    bls.bls_active = False
    skipped, written = [], 0
    for case in sorted(vectors.glob("*/*/*/*")):
        if not case.is_dir():
            continue
        runner, handler = case.parts[-4], case.parts[-3]
        cid = f"{runner}/{handler}/{case.name}"
        meta = read_yaml(case / "meta.yaml")
        if meta.get("bls_setting", 0) == 1:
            skipped.append(f"{cid}: bls_setting 1")
            continue
        if cid in NEEDS_BLS:
            skipped.append(f"{cid}: needs BLS, no @always_bls upstream")
            continue
        try:
            data = encode_case(spec, runner, handler, case)
        except Skip as e:
            skipped.append(f"{cid}: {e}")
            continue
        dest = out / runner / handler / f"{case.name}.case"
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        written += 1
    out.mkdir(parents=True, exist_ok=True)
    (out / "skipped.txt").write_text("".join(s + "\n" for s in skipped))
    print(f"{written} cases written, {len(skipped)} skipped")


if __name__ == "__main__":
    main()
