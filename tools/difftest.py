"""Differential test: the Lean interpreter and the readable Lean against pyspec.

Run from the consensus-specs checkout, in its uv environment:

    cd ../consensus-specs-safe
    uv run python ../consensus-specs-lean/tools/difftest.py

The script runs each case in pyspec, writes `Tests/Diff.lean` with the same cases, runs it with
`lake env lean --run`, and compares the lines. It exits with status 1 on a difference.
"""

import subprocess
import sys
from pathlib import Path

import pydantic
from eth_consensus_specs.gloas import minimal as spec
from ssz.exceptions import SSZTypeError, SSZValueError

LEAN_DIR = Path(__file__).resolve().parent.parent
U64 = 2**64 - 1
ETH = 10**9

# Validators are (effective_balance, first byte of withdrawal_credentials).
CASES = [
    ("db_basic", "decrease_balance", dict(bals=[10, 20, 30], index=1, delta=5)),
    ("db_saturate", "decrease_balance", dict(bals=[10, 20, 30], index=2, delta=50)),
    ("db_last", "decrease_balance", dict(bals=[10, 20, U64], index=2, delta=U64)),
    ("db_index_error", "decrease_balance", dict(bals=[10, 20, 30], index=3, delta=1)),
    ("db_type_error", "decrease_balance", dict(bals=[10, 20, 30], index=1, delta=5, delta_vidx=True)),
    ("peb_empty", "peb", dict(vals=[], bals=[])),
    (
        "peb_mixed",
        "peb",
        dict(
            vals=[(32 * ETH, 1), (32 * ETH, 1), (32 * ETH, 2), (40 * ETH, 2), (32 * ETH, 1)],
            bals=[31 * ETH, 3 * 10**10 + 7, 100 * ETH + 5, 39_700_000_000, 33_300_000_000],
        ),
    ),
    ("peb_cap_compounding", "peb", dict(vals=[(0, 2)], bals=[5000 * ETH])),
    ("peb_overflow", "peb", dict(vals=[(32 * ETH, 1)], bals=[U64])),
    ("peb_index_error", "peb", dict(vals=[(32 * ETH, 1), (32 * ETH, 1)], bals=[1])),
    ("isqrt_0", "isqrt", dict(n=0)),
    ("isqrt_1", "isqrt", dict(n=1)),
    ("isqrt_15", "isqrt", dict(n=15)),
    ("isqrt_16", "isqrt", dict(n=16)),
    ("isqrt_big", "isqrt", dict(n=10**18 + 12345)),
    ("isqrt_max_minus_1", "isqrt", dict(n=U64 - 1)),
    ("isqrt_max", "isqrt", dict(n=U64)),
    ("isqrt_int_arg", "isqrt", dict(n=17, plain_int=True)),
    # Pending partials are (validator_index, amount, withdrawable_epoch). Prior withdrawals are
    # (index, validator_index, amount). Validator 0 is out of range, and the balance after the
    # prior withdrawal underflows. Python reads the validator first, so the error is an
    # IndexError. A lazy alias read would report the underflow instead.
    ("ppw_alias_order", "ppw", dict(vals=[], bals=[5], ppws=[(0, 1, 0)], prior=[(0, 0, 10)])),
    ("ppw_underflow", "ppw", dict(vals=[(32 * ETH, 1)], bals=[5], ppws=[(0, 1, 0)], prior=[(0, 0, 10)])),
    ("ppw_ok", "ppw", dict(vals=[(32 * ETH, 1)], bals=[40 * ETH], ppws=[(0, ETH, 0)], prior=[])),
]


def tag(e: Exception) -> str:
    if isinstance(e, SSZValueError):
        return "sszValue"
    if isinstance(e, pydantic.ValidationError):
        return "validation"
    if isinstance(e, IndexError):
        return "indexError"
    if isinstance(e, ZeroDivisionError):
        return "divisionByZero"
    if isinstance(e, (SSZTypeError, TypeError)):
        return "typeError"
    if isinstance(e, AssertionError):
        return "assertionFailed"
    raise e


def make_state(vals, bals):
    state = spec.BeaconState()
    for eff, prefix in vals:
        wc = spec.Bytes32(bytes([prefix]) + b"\x00" * 31)
        state.validators.append(spec.Validator(withdrawal_credentials=wc, effective_balance=eff))
    for b in bals:
        state.balances.append(spec.Gwei(b))
    return state


def run_python(kind, a):
    try:
        if kind == "decrease_balance":
            state = make_state([], a["bals"])
            delta = (spec.ValidatorIndex if a.get("delta_vidx") else spec.Gwei)(a["delta"])
            spec.decrease_balance(state, spec.ValidatorIndex(a["index"]), delta)
            return "ok balances=" + str([int(b) for b in state.balances]).replace(" ", "")
        if kind == "peb":
            state = make_state(a["vals"], a["bals"])
            spec.process_effective_balance_updates(state)
            effs = [int(v.effective_balance) for v in state.validators]
            return "ok eff=" + str(effs).replace(" ", "")
        if kind == "isqrt":
            n = a["n"] if a.get("plain_int") else spec.Uint64(a["n"])
            r = spec.integer_squareroot(n)
            return f"ok {type(r).__name__ if type(r) is not int else 'int'} {int(r)}"
        if kind == "ppw":
            state = make_state(a["vals"], a["bals"])
            for i, amount, epoch in a["ppws"]:
                state.pending_partial_withdrawals.append(
                    spec.PendingPartialWithdrawal(
                        validator_index=i, amount=amount, withdrawable_epoch=epoch
                    )
                )
            prior = [
                spec.Withdrawal(index=k, validator_index=i, amount=amount)
                for k, i, amount in a["prior"]
            ]
            ws, k, c = spec.get_pending_partial_withdrawals(state, spec.WithdrawalIndex(0), prior)
            return f"ok n={len(ws)} index={int(k)} count={int(c)}"
    except Exception as e:
        return "err " + tag(e)


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_case(name, kind, a):
    if kind == "decrease_balance":
        vidx = "true" if a.get("delta_vidx") else "false"
        return f'  runDB "{name}" {lean_list(a["bals"])} {a["index"]} {a["delta"]} {vidx}'
    if kind == "peb":
        vals = lean_list(f"({e}, {p})" for e, p in a["vals"])
        return f'  runPEB "{name}" {vals} {lean_list(a["bals"])}'
    if kind == "isqrt":
        return f'  runIsqrt "{name}" {a["n"]} {"true" if a.get("plain_int") else "false"}'
    if kind == "ppw":
        vals = lean_list(f"({e}, {p})" for e, p in a["vals"])
        ppws = lean_list(f"({i}, {x}, {e})" for i, x, e in a["ppws"])
        prior = lean_list(f"({k}, {i}, {x})" for k, i, x in a["prior"])
        return f'  runPPW "{name}" {vals} {lean_list(a["bals"])} {ppws} {prior}'


def main():
    expected = [f"{name}: {run_python(kind, a)}" for name, kind, a in CASES]
    body = "\n".join(lean_case(name, kind, a) for name, kind, a in CASES)
    out = LEAN_DIR / "Tests" / "Diff.lean"
    out.parent.mkdir(exist_ok=True)
    out.write_text(
        "-- Generated by tools/difftest.py. Do not edit.\n"
        "import Tests.Harness\n\nopen SpecLean.Tests\n\n"
        f"def main : IO Unit := do\n{body}\n"
    )
    subprocess.run(["lake", "build", "Tests"], cwd=LEAN_DIR, check=True, capture_output=True)
    res = subprocess.run(
        ["lake", "env", "lean", "--run", str(out)], cwd=LEAN_DIR, capture_output=True, text=True
    )
    if res.returncode != 0:
        sys.exit(res.stdout + res.stderr)
    got = res.stdout.splitlines()
    interp = [l.removeprefix("interp ") for l in got if l.startswith("interp ")]
    readable = [l.removeprefix("readable ") for l in got if l.startswith("readable ")]
    bad = 0
    for i, exp in enumerate(expected):
        for label, lines in [("interp", interp), ("readable", readable)]:
            line = lines[i] if i < len(lines) else "<missing>"
            if line.endswith(": skip"):
                print(f"skip {label:8} {line}")
                continue
            # The readable Lean keeps only the error class (SPEC 9.2).
            want = exp
            if label == "readable" and ": err " in exp:
                head, kind = exp.split(": err ")
                cls = "invalid" if kind in ("assertionFailed", "indexError") else "bug"
                want = f"{head}: err {cls}"
            mark = "same" if line == want else "DIFF"
            bad += mark == "DIFF"
            print(f"{mark} {label:8} {line}" + ("" if mark == "same" else f"   pyspec: {exp}"))
    print(f"{len(expected)} cases, {bad} differences")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
