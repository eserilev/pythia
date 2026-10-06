"""Translate the spec functions of a build into readable Lean (SPEC 9.1).

Run from the consensus-specs checkout, in its uv environment:

    cd ../consensus-specs-safe
    uv run python ../consensus-specs-lean/tools/translate.py \
        --out ../consensus-specs-lean/SpecLean/Gen/Readable.lean

It reads the same scope as `gen_scope.sh` and writes one Lean file: a structure per SSZ
container and dataclass, a type per uint and byte vector class, the encoders and decoders
between these types and interpreter values, the constants, the configuration, and one Lean
function per spec function. `tools/rd_types.py` holds the types, `tools/rd_emit.py` the
functions.
"""

import argparse
import ast
import dataclasses
import re
import sys
import typing
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rd_emit  # noqa: E402
import rd_types as T  # noqa: E402
import serialize as S  # noqa: E402

HERE = Path(__file__).resolve().parent


def scope_roots() -> list[str]:
    text = (HERE / "gen_scope.sh").read_text()
    return ",".join(re.findall(r"ROOTS=(?:\$ROOTS,)?([\w,]+)", text)).split(",")


class Build:
    """The classes, constants and configuration values that the scope uses."""

    def __init__(self, spec, fns, names: T.Names):
        self.spec, self.fns, self.names = spec, fns, names
        self.classes: dict[str, type] = {}
        self.order: list[type] = []
        self.dataclass_fields: dict[type, list] = {}
        self.consts: dict[str, object] = {}
        self.config: dict[str, object] = {}

    def add(self, c):
        """Add a class and every class that it holds."""
        if not isinstance(c, type) or c in self.order:
            return
        if T.is_uint_cls(c) or T.is_bytesn_cls(c):
            # An abstract base class (`Uint`, `BytesN`) has no width.
            if hasattr(c, "BITS") if T.is_uint_cls(c) else isinstance(
                    getattr(c, "LENGTH", None), int):
                self.order.append(c)
            return
        li = T.list_info(c)
        if li is not None:
            self.add(li[1])
            return
        if T.is_container_cls(c):
            self.order.append(c)  # placeholder against cycles
            self.order.remove(c)
            for _, ft in c._FIELD_TYPES:
                self.add(ft)
            self.order.append(c)
            return
        if dataclasses.is_dataclass(c):
            hints = typing.get_type_hints(c, vars(self.spec))
            fs = [(f.name, hints[f.name]) for f in dataclasses.fields(c)]
            self.dataclass_fields[c] = fs
            for _, ft in fs:
                self.add_hint(ft)
            self.order.append(c)

    def add_hint(self, h):
        if isinstance(h, type):
            self.add(h)
        for a in typing.get_args(h):
            self.add_hint(a)


def uint_ty_term(names: T.Names, c) -> str:
    if c.BITS in T.WIDTHS and c is T.uint_width(c):
        return f"(.width {c.BITS})"
    return f"(.nominal Scope.Id.«{names.scope(c)}» {c.BITS})"


def ssz_ty_term(b: Build, c) -> str:
    """The `SszTy` of a class, as the interpreter heap holds it."""
    n = b.names
    if T.is_uint_cls(c):
        return f"(.uint {uint_ty_term(n, c)})"
    if T.of_class(c) == T.BOOLEAN:
        return ".boolean"
    if T.is_bytesn_cls(c):
        return f"(.bytes Scope.Id.«{n.scope(c)}» {c.LENGTH})"
    if T.is_container_cls(c) or dataclasses.is_dataclass(c):
        return f"(.container Scope.Id.«{n.scope(c)}»)"
    li = T.list_info(c)
    if li is not None:
        kind, e, limit = li
        lim = "none" if limit is None else f"(some {limit})"
        return f"(.list .{kind} {ssz_ty_term(b, e)} {lim})"
    return ".any"


def enc_term(b: Build, c) -> str:
    """An encoder for values of class `c`."""
    n = b.names
    if T.is_uint_cls(c) or T.is_bytesn_cls(c) or T.is_container_cls(c) or \
            dataclasses.is_dataclass(c):
        return f"enc_{n.cls(c)}"
    if T.of_class(c) == T.BOOLEAN:
        return "encBoolean"
    li = T.list_info(c)
    if li is not None:
        kind, e, limit = li
        lim = "none" if limit is None else f"(some {limit})"
        return f"(encList .{kind} {ssz_ty_term(b, e)} {lim} {enc_term(b, e)})"
    raise ValueError(f"no encoder for {c}")


def dec_term(b: Build, c) -> str:
    n = b.names
    if T.is_uint_cls(c) or T.is_bytesn_cls(c) or T.is_container_cls(c) or \
            dataclasses.is_dataclass(c):
        return f"dec_{n.cls(c)}"
    if T.of_class(c) == T.BOOLEAN:
        return "decBooleanV"
    li = T.list_info(c)
    if li is not None:
        kind, e, limit = li
        lim = "none" if limit is None else f"(some {limit})"
        return f"(decListT .{kind} {ssz_ty_term(b, e)} {lim} {dec_term(b, e)})"
    raise ValueError(f"no decoder for {c}")


def default_term(b: Build, c) -> str:
    """The SSZ default value of class `c`: zeros, and a vector of defaults."""
    li = T.list_info(c)
    if li is not None:
        kind, e, limit = li
        if kind in ("vector", "bitvector"):
            return f"(List.replicate {limit} {default_term(b, e)})"
        return "[]"
    return "default"


def lean_of_hint(b: Build, h) -> str:
    t = rd_emit.type_of_hint(b, h)
    return b.names.lean(t)


def emit_types(b: Build) -> str:
    n = b.names
    out = []
    for c in b.order:
        name = n.cls(c)
        if T.is_uint_cls(c):
            out.append(f"structure {name} where\n  val : Nat\n"
                       f"  deriving DecidableEq, Repr, Inhabited, Hashable\n\n"
                       f"instance : UintC {name} := ⟨{c.BITS}, {name}.val, {name}.mk, fun _ => rfl, fun _ => rfl⟩\n"
                       f"instance : PyOrd {name} := ⟨fun a b => decide (a.val < b.val)⟩\n"
                       f"def enc_{name} : Enc {name} := encUint {uint_ty_term(n, c)}\n"
                       f"abbrev dec_{name} : Dec {name} := decUintT {uint_ty_term(n, c)}\n")
        elif T.is_bytesn_cls(c):
            out.append(f"structure {name} where\n  data : Bytes\n"
                       f"  deriving DecidableEq, Repr, Hashable\n\n"
                       f"instance : Inhabited {name} := ⟨⟨List.replicate {c.LENGTH} 0⟩⟩\n"
                       f"instance : BytesC {name} := ⟨{c.LENGTH}, {name}.data, {name}.mk, fun _ => rfl, fun _ => rfl⟩\n"
                       f"instance : PyOrd {name} := ⟨fun a b => PyOrd.lt a.data b.data⟩\n"
                       f"def enc_{name} : Enc {name} := encBytesN Scope.Id.«{n.scope(c)}»\n"
                       f"abbrev dec_{name} : Dec {name} := decBytesT Scope.Id.«{n.scope(c)}»\n")
        else:
            if T.is_container_cls(c):
                fields = list(c._FIELD_TYPES)
                lean_fields = [(f, n.lean(T.of_class(ft))) for f, ft in fields]
            else:
                fields = b.dataclass_fields[c]
                lean_fields = [(f, lean_of_hint(b, ft)) for f, ft in fields]
            body = "".join(f"  {T.ident(f)} : {lt}\n" for f, lt in lean_fields)
            if T.is_container_cls(c):
                dflt = ", ".join(f"{T.ident(f)} := {default_term(b, ft)}" for f, ft in fields)
                out.append(f"structure {name} where\n{body}"
                           f"  deriving DecidableEq, Repr\n\n"
                           f"instance : Inhabited {name} := ⟨{{ {dflt} }}⟩\n")
            else:
                out.append(f"structure {name} where\n{body}"
                           f"  deriving DecidableEq, Repr, Inhabited\n")
            if T.is_container_cls(c):
                encs = ", ".join(f"{enc_term(b, ft)} x.{T.ident(f)}" for f, ft in fields)
                out.append(f"def enc_{name} : Enc {name} := fun x =>\n"
                           f"  encContainer Scope.Id.«{n.scope(c)}» [{encs}]\n")
                decs = "\n".join(
                    f"  let {T.ident(f)} ← fs[{i}]? >>= {dec_term(b, ft)} h"
                    for i, (f, ft) in enumerate(fields))
                assign = ", ".join(f"{T.ident(f)}" for f, _ in fields)
                out.append(f"def dec_{name} : Dec {name} := fun h v => do\n"
                           f"  let fs ← containerFieldsT Scope.Id.«{n.scope(c)}» h v\n{decs}\n"
                           f"  pure {{ {assign} }}\n")
        out.append("")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default="889a389f9")
    ap.add_argument("--preset", default="minimal")
    ap.add_argument("--only", default=None, help="translate only these functions (debug)")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    out = Path(args.out).resolve()
    commit, spec_object, sources, spec, fns, sources_text, _ = S.load_scope(
        args.rev, "gloas", args.preset, scope_roots())
    names = T.Names(spec)
    b = Build(spec, fns, names)
    b.sources = sources
    b.sources_text = sources_text
    b.config_vars = spec_object.config_vars
    em = rd_emit.Emitter(b)
    em.collect()
    types = emit_types(b)
    consts = em.emit_constants()
    config = em.emit_config()
    only = set(args.only.split(",")) if args.only else None
    funcs = em.emit_functions(only)
    entries = em.emit_entries()
    out.write_text(f"""-- Generated by tools/translate.py. Do not edit.
-- Spec: consensus-specs {commit} (gloas, {args.preset}).
import SpecLean.Rd.Prelude
import SpecLean.Gen.Scope

/-!
# Readable Lean of the version 1 scope (SPEC 9.1)

One Lean function per spec function, in the state-passing style: a function returns every
argument that it changes. Each uint class and byte vector class is its own type.
-/

namespace SpecLean.Rd.Gen

open SpecLean SpecLean.Rd

/-! ## Types -/

{types}
/-! ## Constants -/

{consts}
/-! ## Configuration -/

{config}
/-! ## Functions -/

variable [Spec] [Cfg]

{funcs}
/-! ## Entry points -/

{entries}
end SpecLean.Rd.Gen
""")
    print(f"wrote {out}: {len(b.order)} types, {em.count} functions")


if __name__ == "__main__":
    main()
