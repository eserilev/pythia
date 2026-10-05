"""Probe the eth-ssz-specs value rules and emit them as Lean checks.

Run from the consensus-specs checkout, in its uv environment:

    cd ../consensus-specs-safe
    uv run python ../consensus-specs-lean/tools/probes/value_rules.py

Each probe runs in pyspec. The script prints the table and writes `Tests/ValueRules.lean`, one
`example ... := rfl` per row, so `lake build Tests` fails when the interpreter and the library
disagree. The interpreter does not hold this table: it holds the rule that the table tests
(`resolveUint`: the more derived class wins, unrelated classes raise `TypeError`).
"""

import operator
from pathlib import Path

import pydantic
from ssz.boolean import Boolean
from eth_consensus_specs.gloas import minimal as spec
from ssz.exceptions import SSZTypeError, SSZValueError

OUT = Path(__file__).resolve().parents[2] / "Tests" / "ValueRules.lean"

# Classes the targets use, plus one 8-bit width class and one unrelated 64-bit sibling.
CLASSES = {
    "Gwei": (spec.Gwei, "(.nominal Id.Gwei 64)"),
    "ValidatorIndex": (spec.ValidatorIndex, "(.nominal Id.ValidatorIndex 64)"),
    "Uint64": (spec.Uint64, "(.width 64)"),
    "Uint8": (spec.Uint8, "(.width 8)"),
}
BINOPS = {"add": operator.add, "sub": operator.sub, "mul": operator.mul,
          "floorDiv": operator.floordiv, "mod": operator.mod, "pow": operator.pow,
          "bitAnd": operator.and_, "bitOr": operator.or_, "bitXor": operator.xor,
          "lShift": operator.lshift, "rShift": operator.rshift}
CMPOPS = {"lt": operator.lt, "eq": operator.eq, "gt": operator.gt}


def err(e):
    if isinstance(e, SSZValueError):
        return "sszValue"
    if isinstance(e, pydantic.ValidationError):
        return "validation"
    if isinstance(e, IndexError):
        return "indexError"
    if isinstance(e, ZeroDivisionError):
        return "divisionByZero"
    if isinstance(e, ValueError) and not isinstance(e, (SSZValueError, pydantic.ValidationError)):
        return "valueError"
    if isinstance(e, (SSZTypeError, TypeError)):
        return "typeError"
    raise e


def operand(kind, n):
    """A Python value and its Lean `Value` term."""
    if kind == "int":
        return n, f"(.int ({n}))"
    cls, ty = CLASSES[kind]
    return cls(n), f"(.uint {ty} {n})"


def result_term(r):
    if isinstance(r, Boolean):
        return f".ok (.boolean {'true' if r else 'false'})"
    if type(r) is bool:
        return f".ok {'true' if r else 'false'}"
    if type(r) is int:
        return f".ok (.int ({r}))"
    for cls, ty in CLASSES.values():
        if type(r) is cls:
            return f".ok (.uint {ty} {int(r)})"
    raise TypeError(f"unexpected result {r!r}")


def probe(fn, *args):
    try:
        return result_term(fn(*args))
    except Exception as e:  # noqa: BLE001
        return f".error .{err(e)}"


def main():
    rows, checks = [], []
    kinds = list(CLASSES) + ["int"]
    pairs = [(a, b) for a in kinds for b in kinds if not (a == "int" and b == "int")]
    values = [(7, 2), (2, 7), (7, 0), (2**64 - 1, 1), (2**63, 2)]
    for op, fn in BINOPS.items():
        for a, b in pairs:
            for x, y in values:
                if "Uint8" in (a, b) and max(x, y) > 255:
                    continue
                (pa, la), (pb, lb) = operand(a, x), operand(b, y)
                res = probe(fn, pa, pb)
                rows.append(f"{a}({x}) {op} {b}({y}) = {res}")
                checks.append(f"example : binopVal .{op} {la} {lb} = {res} := rfl")
    for op, fn in CMPOPS.items():
        for a, b in pairs:
            (pa, la), (pb, lb) = operand(a, 3), operand(b, 5)
            res = probe(fn, pa, pb)
            rows.append(f"{a}(3) {op} {b}(5) = {res}")
            checks.append(f"example : cmpVal .{op} {la} {lb} = {res} := rfl")
    # Writes: a list element of class Gwei, and a container field of class Gwei.
    state = spec.BeaconState()
    state.balances.append(spec.Gwei(0))
    state.validators.append(spec.Validator())
    gwei_ty = "(.uint (.nominal Id.Gwei 64))"

    def list_write(v):
        state.balances[0] = v
        return state.balances[0]

    def field_write(v):
        state.validators[0].effective_balance = v
        return state.validators[0].effective_balance

    for kind in kinds:
        for n in [5, -5, 2**64]:
            if kind != "int" and not (0 <= n < 2 ** (8 if kind == "Uint8" else 64)):
                continue
            pv, lv = operand(kind, n)
            res_list = probe(list_write, pv)
            res_field = probe(field_write, pv)
            rows.append(f"Gwei list element := {kind}({n}) -> {res_list}")
            rows.append(f"Gwei container field := {kind}({n}) -> {res_field}")
            checks.append(f"example : coerceElem {gwei_ty} {lv} = {res_list} := rfl")
            checks.append(f"example : coerceField {gwei_ty} {lv} = {res_field} := rfl")

    # SSZ Boolean is nominal.
    from ssz.boolean import Boolean
    others = [("Boolean", Boolean(True), "(.boolean true)"), ("bool", True, "(.bool true)"),
              ("int", 1, "(.int (1))"), ("Uint64", spec.Uint64(1), "(.uint (.width 64) 1)")]
    for name, pv, lv in others:
        for op, fn in [("eq", operator.eq), ("notEq", operator.ne)]:
            res = probe(fn, Boolean(True), pv)
            rows.append(f"Boolean(True) {op} {name} = {res}")
            checks.append(f"example : cmpVal .{op} (.boolean true) {lv} = {res} := rfl")
        res = probe(operator.add, Boolean(True), pv)
        rows.append(f"Boolean(True) add {name} = {res}")
        checks.append(f"example : binopVal .add (.boolean true) {lv} = {res} := rfl")

    # Unary operators: `-x` and `~x` of a uint give a plain `int`.
    for kind in kinds:
        pv, lv = operand(kind, 5)
        for op, fn in [("neg", operator.neg), ("invert", operator.invert)]:
            res = probe(fn, pv)
            rows.append(f"{op} {kind}(5) = {res}")
            checks.append(f"example : unopVal .{op} {lv} = {res} := rfl")
    # Equality against None, bool and str.
    misc = [("None", None, ".none"), ("bool", True, "(.bool true)"), ("str", "a", "(.str \"a\")")]
    for kind in kinds:
        pv, lv = operand(kind, 1)
        for name, mv, ml in misc:
            for op, fn in [("eq", operator.eq), ("notEq", operator.ne)]:
                res = probe(fn, pv, mv)
                rows.append(f"{kind}(1) {op} {name} = {res}")
                checks.append(f"example : cmpVal .{op} {lv} {ml} = {res} := rfl")
    # Boolean field writes: a Python bool passes, an int does not.
    v = spec.Validator()

    def slashed_write(x):
        v.slashed = x
        return v.slashed

    for name, pv, lv in [("True", True, "(.bool true)"), ("False", False, "(.bool false)"),
                         ("int 1", 1, "(.int 1)"), ("int 0", 0, "(.int 0)")]:
        res = probe(slashed_write, pv)
        rows.append(f"Boolean field := {name} -> {res}")
        checks.append(f"example : coerceField .boolean {lv} = {res} := rfl")

    print("\n".join(rows))
    OUT.write_text(
        "-- Generated by tools/probes/value_rules.py. Do not edit.\n"
        "-- Each row is a probe against eth-ssz-specs in pyspec.\n"
        "import SpecLean.Gen.Ast\n\n"
        "namespace SpecLean.Tests.ValueRules\n\nopen SpecLean SpecLean.Gen\n\n"
        + "\n".join(checks)
        + "\n\nend SpecLean.Tests.ValueRules\n"
    )
    print(f"{len(checks)} rows -> {OUT}")


if __name__ == "__main__":
    main()
