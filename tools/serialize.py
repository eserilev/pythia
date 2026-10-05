"""Serialize spec functions from the pyspec SpecObject into Lean syntax trees.

Run from the consensus-specs checkout, in its uv environment:

    cd ../consensus-specs-safe
    uv run python ../consensus-specs-lean/tools/serialize.py --rev 889a389f9 \
        --roots decrease_balance,process_effective_balance_updates,integer_squareroot \
        --namespace Gen --out ../consensus-specs-lean/SpecLean/Gen/Ast.lean

`--rev` extracts that commit with `git archive`, so uncommitted edits do not leak in.
The SpecObject comes from `combine_spec_objects` over the fork's markdown files, as
`pysetup/generate_specs.py` builds it. The SpecObject has no source positions, so the
serializer finds each function's `def` line in the markdown by text search.

The output holds the syntax trees of the roots and their callees, and the environment: types,
dataclasses, constants, the referenced `config` values, modules, builtins and the known names.
`--extra FILE` adds the functions of a Python file (the construct tests), with the spec module
as their namespace.
"""

import argparse
import ast
import dataclasses
import importlib
import inspect
import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from footprint import footprint  # noqa: E402
from pyast import (Emitter, Interner, Unsupported, config_names, free_names,  # noqa: E402
                   lean_str, strip_docstring)

TOOL_VERSION = "0.2.0"

BUILTINS = {
    "len": "len", "range": "range", "enumerate": "enumerate", "zip": "zip", "sorted": "sorted",
    "min": "min", "max": "max", "sum": "sum", "any": "any", "all": "all", "filter": "filter",
    "list": "list", "tuple": "tuple", "set": "set", "dict": "dict", "bytes": "bytes",
    "int": "int", "bool": "bool", "ssz_serialize": "sszSerialize",
}
# Spec functions whose bodies use library internals. The oracle gives them (SPEC 8).
ORACLE_FUNCTIONS = {"sha256": "sha256", "hash_tree_root": "hashTreeRoot"}
# Spec functions that pyspec replaces with a BLS call (`implement_optimizations`). The
# markdown text is for show only. They become `bls.<name>` (SPEC 8).
BLS_FUNCTIONS = {"eth_aggregate_pubkeys": "AggregatePKs"}
# Data members of the `bls` module. `bls.X` becomes the constant `bls.X`.
BLS_CONSTANTS = {"G2_POINT_AT_INFINITY"}
FORK_MODULES = {"phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas"}
KNOWN = ["append", "extend", "index", "count", "copy", "union", "intersection", "add",
         "from_bytes", "empty", "hash_tree_root", "data", "key", "reverse", "strict", "get",
         "Bytes32", "Root", "bit_length", "difference", "items", "values", "keys"]
ANNOTATION_ONLY = {"Any", "Callable", "Sequence", "SSZObject", "Uint", "List", "BitVector",
                   "ProgressiveList", "Optional", "Tuple", "Set", "Dict"}


def load_scope(rev: str, fork: str, preset: str, roots: list[str], extra=None):
    """The scope of a build: the SpecObject, its source files, the pyspec module, and the
    syntax trees of the roots and their callees, with the source text of each."""
    commit = subprocess.check_output(["git", "rev-parse", rev], text=True).strip()
    tmp = Path(tempfile.mkdtemp(prefix="spec-"))
    archive = subprocess.run(["git", "archive", commit], check=True, capture_output=True).stdout
    subprocess.run(["tar", "-x", "-C", str(tmp)], input=archive, check=True)
    repo = Path.cwd()
    spec_object, sources = build_spec_object(tmp, fork, preset)
    os.chdir(repo)
    spec = importlib.import_module(f"eth_consensus_specs.{fork}.{preset}")
    sources_text = dict(spec_object.functions)
    extra_names = []
    if extra is not None:
        extra_src = extra.read_text()
        for node in ast.parse(extra_src).body:
            if isinstance(node, ast.FunctionDef):
                sources_text[node.name] = ast.get_source_segment(extra_src, node)
                extra_names.append(node.name)
    todo, fns = list(roots) + extra_names, {}
    while todo:
        name = todo.pop()
        if (name in fns or name in ORACLE_FUNCTIONS or name in BLS_FUNCTIONS
                or name not in sources_text):
            continue
        tree = ast.parse(sources_text[name]).body[0]
        fns[name] = tree
        todo += [c for c in free_names(tree) if c in sources_text]
    return commit, spec_object, sources, spec, fns, sources_text, extra_names


def build_spec_object(spec_dir: Path, fork: str, preset_name: str):
    sys.path.insert(0, str(spec_dir))
    os.chdir(spec_dir)
    from pysetup.generate_specs import get_spec, load_config, load_preset
    from pysetup.helpers import combine_spec_objects, finalized_spec_object
    from pysetup.md_doc_paths import get_md_doc_paths

    sources = [Path(p) for p in get_md_doc_paths(fork).split()]
    preset = load_preset(tuple(sorted(Path(f"presets/{preset_name}").glob("*.yaml"))))
    config = load_config(Path(f"configs/{preset_name}.yaml"))
    specs = [get_spec(s, preset, config, preset_name) for s in sources]
    spec_object = specs[0]
    for other in specs[1:]:
        spec_object = combine_spec_objects(spec_object, other)
    return finalized_spec_object(spec_object), sources


def find_source_line(sources, name: str, text: str):
    """The markdown file and line of the `def` that produced `text`. The last match wins."""
    body = text.splitlines()
    found = None
    for src in sources:
        lines = src.read_text().splitlines()
        for i, line in enumerate(lines):
            if line == body[0] and lines[i : i + len(body)] == body:
                found = (str(src), i + 1)
    if found is None:
        raise Unsupported(f"no markdown source for {name}")
    return found


class Types:
    """SSZ types and dataclasses that the code references, emitted as Lean data."""

    def __init__(self, intern, m, spec=None, prev=""):
        self.intern, self.m = intern, m
        # A class of an older fork that the build does not have gets the fork's prefix, as in
        # `fulu.BeaconState`.
        self.spec, self.prev = spec, prev
        self.containers: dict[str, str] = {}
        self.active: dict[str, str] = {}

    def cname(self, cls) -> str:
        name = cls.__name__
        if self.spec is None or getattr(self.spec, name, None) is cls:
            return name
        return f"{self.prev}.{name}"

    def uint_ty(self, cls) -> str:
        BaseUint = self.m["BaseUint"]
        parents = [b for b in cls.__bases__ if issubclass(b, BaseUint)]
        if parents == [BaseUint]:
            return f"(.width {cls.BITS})"
        if len(parents) == 1 and parents[0].__bases__ == (BaseUint,):
            return f"(.nominal {self.intern(self.cname(cls))} {cls.BITS})"
        raise Unsupported(f"uint class depth: {cls.__name__}")

    def ssz(self, t) -> str:
        m = self.m
        if issubclass(t, m["BaseUint"]):
            return f"(.uint {self.uint_ty(t)})"
        if issubclass(t, m["Boolean"]):
            return ".boolean"
        if issubclass(t, m["ByteVector"]):
            return f"(.bytes {self.intern(self.cname(t))} {t.LENGTH})"
        if issubclass(t, m["Container"]) or issubclass(t, m["ProgressiveContainer"]):
            self.container(t)
            return f"(.container {self.intern(self.cname(t))})"
        for kind, base in [("progressiveBitlist", "ProgressiveBitList"), ("bitlist", "BitList"),
                           ("bitvector", "BitVector")]:
            if issubclass(t, m[base]):
                limit = getattr(t, "LIMIT", None) if kind == "bitlist" else getattr(t, "LENGTH", None)
                lim = "none" if limit is None else f"(some {limit})"
                return f"(.list .{kind} .boolean {lim})"
        if issubclass(t, m["ByteList"]):
            return f"(.list .list (.uint (.width 8)) (some {t.LIMIT}))"
        for kind, base in [("progressiveList", "ProgressiveList"), ("list", "List"),
                           ("vector", "Vector")]:
            if issubclass(t, m[base]):
                limit = None if kind == "progressiveList" else (t.LIMIT if kind == "list" else t.LENGTH)
                lim = "none" if limit is None else f"(some {limit})"
                elem = self.ssz(t.ELEMENT_TYPE)
                if elem == "(.uint (.width 8))":
                    # The interpreter reads a list of `Uint8` as a `ByteList`.
                    raise Unsupported(f"SSZ list of uint8: {t}")
                return f"(.list .{kind} {elem} {lim})"
        raise Unsupported(f"SSZ type {t}")

    def container(self, t):
        name = self.cname(t)
        if name in self.containers:
            return
        self.containers[name] = ""
        fields = [f"({self.intern(f)}, {self.ssz(ft)})" for f, ft in t._FIELD_TYPES]
        self.containers[name] = f"({self.intern(name)}, [{', '.join(fields)}])"
        if issubclass(t, self.m["ProgressiveContainer"]):
            bits = ", ".join(str(int(b)) for b in t.ACTIVE_FIELDS)
            self.active[name] = f"({self.intern(name)}, [{bits}])"

    def dataclass(self, t):
        name = t.__name__
        fields = [f"({self.intern(f.name)}, .any)" for f in dataclasses.fields(t)]
        self.containers[name] = f"({self.intern(name)}, [{', '.join(fields)}])"

    def is_ssz_class(self, obj) -> bool:
        return inspect.isclass(obj) and issubclass(obj, self.m["SSZType"])


def value_term(v, types: Types) -> str:
    m, intern = types.m, types.intern
    if isinstance(v, m["BaseUint"]):
        return f"(.uint {types.uint_ty(type(v))} {int(v)})"
    if isinstance(v, m["Boolean"]):
        return f"(.boolean {'true' if v else 'false'})"
    if isinstance(v, bytes):
        return f"(.bytes {intern(type(v).__name__)} [{', '.join(str(b) for b in v)}])"
    if type(v) is bool:
        return f"(.bool {'true' if v else 'false'})"
    if type(v) is int:
        return f"(.int ({v}))"
    if type(v) is str:
        return f"(.str {lean_str(v)})"
    if v is None:
        return ".none"
    if isinstance(v, (list, tuple)):
        return f"(.tuple [{', '.join(value_term(x, types) for x in v)}])"
    if isinstance(v, dict) or type(v).__name__ == "frozendict":
        kvs = [f"({value_term(k, types)}, {value_term(x, types)})" for k, x in v.items()]
        return f"(.frozenDict [{', '.join(kvs)}])"
    raise Unsupported(f"constant value {v!r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default="889a389f9")
    ap.add_argument("--fork", default="gloas")
    ap.add_argument("--preset", default="minimal")
    ap.add_argument("--roots",
                    default="decrease_balance,process_effective_balance_updates,integer_squareroot")
    ap.add_argument("--namespace", default="Gen")
    ap.add_argument("--extra", default=None)
    ap.add_argument("--containers", default="BeaconState",
                    help="container types to emit even if the code does not name them")
    ap.add_argument("--out", required=True)
    ap.add_argument("--fp-out", default=None, help="write FP and the write sites as text")
    ap.add_argument("--prev-fork", default=None,
                    help="also emit the BeaconState of this fork, for the upgrade function")
    args = ap.parse_args()

    out = Path(args.out).resolve()
    extra = Path(args.extra).resolve() if args.extra else None
    roots = [r for r in args.roots.split(",") if r]
    commit, spec_object, sources, spec, fns, sources_text, extra_names = load_scope(
        args.rev, args.fork, args.preset, roots, extra)
    import ssz.bitfields, ssz.boolean, ssz.byte_arrays, ssz.collections, ssz.container
    import ssz.ssz_base, ssz.uint

    m = {
        "BaseUint": ssz.uint.BaseUint, "Boolean": ssz.boolean.Boolean,
        "ByteVector": ssz.byte_arrays.ByteVector, "ByteList": ssz.byte_arrays.ByteList,
        "Container": ssz.container.Container,
        "ProgressiveContainer": ssz.container.ProgressiveContainer,
        "BitList": ssz.bitfields.BitList, "BitVector": ssz.bitfields.BitVector,
        "ProgressiveBitList": ssz.bitfields.ProgressiveBitList, "List": ssz.collections.List,
        "ProgressiveList": ssz.collections.ProgressiveList, "Vector": ssz.collections.Vector,
        "SSZType": ssz.ssz_base.SSZType,
    }

    intern = Interner()
    intern("bytes")
    types = Types(intern, m)

    defs, globals_, configs, base_lines = [], {}, set(), {}
    for name in sorted(fns):
        tree = fns[name]
        text = sources_text[name]
        if name in extra_names:
            src = extra.name
            line = next(n.lineno for n in ast.parse(extra.read_text()).body
                        if isinstance(n, ast.FunctionDef) and n.name == name)
        else:
            src, line = find_source_line(sources, name, text)
        base_lines[name] = (src, line)
        em = Emitter(intern, line, frozenset(("bls", c) for c in BLS_CONSTANTS))
        params = em.params(tree.args)
        body = em.block(strip_docstring(tree.body), 2)
        quoted = text.rstrip().replace("-/", "- /").replace("/-", "/ -")
        defs.append(
            f"/-- `{src}:{line}`\n```python\n{quoted}\n``` -/\n"
            f"def fn_{name} : FunctionDef where\n"
            f"  name := {intern(name)}\n  params := {params}\n"
            f"  line := {line}\n  body := {body}\n"
        )
        globals_[name] = f"(.fn fn_{name})"
        configs |= config_names(tree)
    for name in sorted(fns):
        for free in sorted(free_names(fns[name])):
            if free in globals_:
                continue
            if free in ORACLE_FUNCTIONS:
                globals_[free] = f"(.builtin .{ORACLE_FUNCTIONS[free]})"
            elif free in BLS_FUNCTIONS:
                globals_[free] = (f"(.const (.member (.glob {intern('bls')}) "
                                  f"{intern(BLS_FUNCTIONS[free])}))")
                globals_.setdefault("bls", "(.module .bls)")
            elif free in BUILTINS:
                globals_[free] = f"(.builtin .{BUILTINS[free]})"
            elif free == "bls":
                globals_[free] = "(.module .bls)"
            elif free in FORK_MODULES:
                globals_[free] = "(.module .fork)"
            elif free == "config":
                globals_[free] = "(.module .config)"
            elif free in ANNOTATION_ONLY:
                continue
            elif free in spec_object.config_vars:
                # A runtime configuration value: looked up in `Env.config` at each read.
                globals_[free] = "(.configVar)"
                configs.add(free)
            else:
                obj = getattr(spec, free, None)
                if obj is None:
                    raise Unsupported(f"{name}: free name {free}")
                if types.is_ssz_class(obj):
                    globals_[free] = f"(.type {types.ssz(obj)})"
                elif inspect.isclass(obj) and dataclasses.is_dataclass(obj):
                    types.dataclass(obj)
                    globals_[free] = f"(.dataclass {intern(obj.__name__)})"
                elif not callable(obj) or isinstance(obj, (bytes, int)):
                    globals_[free] = f"(.const {value_term(obj, types)})"
                else:
                    raise Unsupported(f"{name}: free name {free}")

    for c in sorted(BLS_CONSTANTS):
        if f"bls.{c}" in intern.ids:
            globals_[f"bls.{c}"] = f"(.const {value_term(getattr(spec.bls, c), types)})"
    for c in [c for c in args.containers.split(",") if c]:
        types.ssz(getattr(spec, c))
    if args.prev_fork:
        prev = importlib.import_module(f"eth_consensus_specs.{args.prev_fork}.{args.preset}")
        types.spec, types.prev = spec, args.prev_fork
        types.ssz(prev.BeaconState)
    ssz_names = {n for n in dir(spec) if types.is_ssz_class(getattr(spec, n))}
    def is_heap(t, steps):
        cls = getattr(spec, t)
        for x in steps:
            if x == "*":
                cls = getattr(cls, "ELEMENT_TYPE", None)
            else:
                cls = dict(getattr(cls, "_FIELD_TYPES", [])).get(x)
            if cls is None:
                return False
        return not issubclass(cls, (m["BaseUint"], m["Boolean"], m["ByteVector"]))

    fp, sites, per_fn = footprint(fns, ssz_names, is_heap)
    fn_fp_terms = [
        f"({intern(n)}, [{', '.join(f'({j}, [{chr(44).join(str(intern(x)) for x in st)}])' for j, st in ps)}])"
        for n, ps in sorted(per_fn.items()) if ps]
    fp_terms = [f"({intern(t)}, [{', '.join(str(intern(x)) for x in steps)}])" for t, steps in fp]
    if args.fp_out:
        Path(args.fp_out).write_text(
            "".join(f"FP {t}{''.join('.' + x for x in steps)}\n" for t, steps in fp)
            + "".join(f"WRITE {n}:{base_lines[n][0]}:{base_lines[n][1] + line - 1} {t}{''.join('.' + x for x in steps)}\n"
                      for n, line, t, steps in sites))
    config_terms = [f"({intern(c)}, {value_term(getattr(spec.config, c), types)})"
                    for c in sorted(configs)]
    known = {k: intern(k) for k in KNOWN}
    ns = args.namespace
    gl = ",\n".join(f"  ({intern(k)}, {v})" for k, v in globals_.items())
    ids = "\n".join(f"abbrev «{s}» : Name := {i}" for i, s in enumerate(intern.names))
    name_table = ",\n  ".join(lean_str(s) for s in intern.names)
    containers = ",\n  ".join(v for v in types.containers.values() if v)
    known_fields = "\n".join(
        f"  {lean}  := {known[py]}" for lean, py in [
            ("append", "append"), ("extend", "extend"), ("index", "index"), ("count", "count"),
            ("copy", "copy"), ("union", "union"), ("intersection", "intersection"),
            ("add", "add"), ("fromBytes", "from_bytes"), ("empty", "empty"),
            ("hashTreeRoot", "hash_tree_root"), ("data", "data"), ("key", "key"),
            ("reverse", "reverse"), ("strict", "strict"), ("get", "get"),
            ("bytes32", "Bytes32"), ("root", "Root"), ("bitLength", "bit_length"),
            ("difference", "difference"), ("items", "items"), ("values", "values"),
            ("keys", "keys")])
    nl = "\n"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        f"""-- Generated by tools/serialize.py {TOOL_VERSION}. Do not edit.
-- Spec: consensus-specs {commit} ({args.fork}, {args.preset}).
import SpecLean.Interp
import SpecLean.Ssz

namespace SpecLean.{ns}

/-- Interned names. Index `i` is the name with id `i`. -/
def names : Array String := #[
  {name_table}]

namespace Id
{ids}
end Id

open SpecLean

{nl.join(defs)}
def containers : List (Name × List (Name × SszTy)) := [
  {containers}]

/-- The layout of each progressive container: one bit per position (EIP-7495). -/
def activeFields : List (Name × List Nat) := [
  {(','+nl+'  ').join(types.active.values())}]

/-- FP: the pattern of each object that a function of this build changes in place (SPEC 9.2).
A pattern is a root type and a list of steps. A step is a field name or `*`, any element. -/
def footprint : List (Name × List Name) := [
  {(','+nl+'  ').join(fp_terms)}]

/-- `Footprint f` of each function that writes in place: a parameter index and the steps from
it. A step is a field name or `*`. -/
def fnFootprint : List (Name × List (Nat × List Name)) := [
  {(','+nl+'  ').join(fn_fp_terms)}]

def globals : List (Name × Global) := [
{gl}]

def config : List (Name × Value) := [
  {(','+nl+'  ').join(config_terms)}]

def knownNames : KnownNames where
{known_fields}

/-- The environment of this build. The oracle gives `sha256`, `hash_tree_root` and BLS. -/
def env (o : Oracle) : Env :=
  {{ globals, containers, bytesName := 0, nm := knownNames, config,
     sha256 := o.sha256, hashTreeRoot := o.hashTreeRoot, bls := o.bls }}

end SpecLean.{ns}
"""
    )
    print(f"wrote {out}: {len(defs)} functions, {len(intern.names)} names, "
          f"{len([c for c in types.containers.values() if c])} containers")


if __name__ == "__main__":
    try:
        main()
    except Unsupported as e:
        sys.exit(f"serialize: unsupported: {e}")
