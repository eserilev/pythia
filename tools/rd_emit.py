"""The function part of the readable Lean translator (SPEC 9.1, 4.2)."""

import ast
import dataclasses
import inspect
import typing
from pathlib import Path

import rd_types as T
import serialize as S


def type_of_hint(b, h):
    """The type of a Python type hint."""
    if h is typing.Any:
        return T.ANY
    if isinstance(h, str):
        return type_of_annotation(b, ast.parse(h, mode="eval").body)
    origin = typing.get_origin(h)
    args = typing.get_args(h)
    if origin in (list, typing.Sequence) or (origin is not None and getattr(origin, "__name__", "") == "Sequence"):
        return ("list", type_of_hint(b, args[0]), None)
    if origin is set:
        return ("set", type_of_hint(b, args[0]))
    if origin is dict:
        return ("dict", type_of_hint(b, args[0]), type_of_hint(b, args[1]))
    if origin is tuple:
        return ("tuple", tuple(type_of_hint(b, a) for a in args))
    if origin is typing.Union or str(origin) == "<class 'types.UnionType'>":
        rest = [a for a in args if a is not type(None)]
        if len(rest) == 1:
            return ("option", type_of_hint(b, rest[0]))
    t = T.of_class(h)
    if t is not None:
        return t
    raise S.Unsupported(f"type hint {h}")


def type_of_annotation(b, a):
    """The type of an annotation in the source."""
    spec = b.spec
    match a:
        case None:
            return T.NONE
        case ast.Constant(value=None):
            return T.NONE
        case ast.Name(id="int"):
            return T.INT
        case ast.Name(id="bool"):
            return T.BOOL
        case ast.Name(id="bytes"):
            return T.BYTES
        case ast.Name(id="Any") | ast.Name(id="SSZObject"):
            return T.ANY
        case ast.Name(id="Uint"):
            return ("utvar", "β")
        case ast.Name(id=n):
            c = getattr(spec, n, None)
            t = T.of_class(c) if c is not None else None
            if t is None:
                raise S.Unsupported(f"annotation {n}")
            return t
        case ast.Attribute(value=ast.Name(id=mod), attr=n):
            import importlib
            m = importlib.import_module(f"eth_consensus_specs.{mod}.{b.preset}")
            return T.of_class(getattr(m, n))
        case ast.Subscript(value=ast.Name(id=g), slice=s):
            args = s.elts if isinstance(s, ast.Tuple) else [s]
            ts = [type_of_annotation(b, x) for x in args]
            if g in ("Sequence", "list", "List"):
                return ("list", ts[0], None)
            if g in ("set", "Set"):
                return ("set", ts[0])
            if g in ("dict", "Dict"):
                return ("dict", ts[0], ts[1])
            if g in ("tuple", "Tuple"):
                return ("tuple", tuple(ts))
            if g == "Optional":
                return ("option", ts[0])
        case ast.BinOp(op=ast.BitOr(), left=l, right=r):
            if isinstance(r, ast.Constant) and r.value is None:
                return ("option", type_of_annotation(b, l))
            return T.ANY
    raise S.Unsupported(f"annotation {ast.unparse(a)}")


class Emitter:
    def __init__(self, b):
        self.b = b
        self.count = 0
        b.preset = getattr(b, "preset", "minimal")

    # --- collection ---------------------------------------------------------------------

    def collect(self):
        b, spec = self.b, self.b.spec
        for name, tree in b.fns.items():
            for a in tree.args.args:
                self.add_annotation(a.annotation)
            self.add_annotation(tree.returns)
            for free in S.free_names(tree):
                obj = getattr(spec, free, None)
                if free in b.config_vars:
                    b.config[free] = getattr(spec.config, free)
                elif isinstance(obj, type):
                    t = T.of_class(obj)
                    if t is not None:
                        b.add(obj)
                        li = T.list_info(obj)
                        if li:
                            b.add(li[1])
                elif free in b.fns or free in S.BUILTINS or free in S.ORACLE_FUNCTIONS \
                        or free in S.BLS_FUNCTIONS or free in S.FORK_MODULES or free in (
                            "bls", "config") or free in S.ANNOTATION_ONLY:
                    continue
                elif obj is not None and not callable(obj) or isinstance(obj, (int, bytes)):
                    b.consts[free] = obj
            for n in ast.walk(tree):
                if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and \
                        n.value.id == "config":
                    b.config[n.attr] = getattr(spec.config, n.attr)
        for v in list(b.consts.values()) + list(b.config.values()):
            self.add_value_classes(v)
        b.add(spec.BeaconState)

    def add_annotation(self, a):
        if a is None:
            return
        for n in ast.walk(a):
            if isinstance(n, ast.Name):
                c = getattr(self.b.spec, n.id, None)
                if isinstance(c, type):
                    self.b.add(c)
                    li = T.list_info(c)
                    if li:
                        self.b.add(li[1])
            if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name):
                import importlib
                m = importlib.import_module(f"eth_consensus_specs.{n.value.id}.{self.b.preset}")
                c = getattr(m, n.attr, None)
                if isinstance(c, type):
                    self.b.add(c)

    def add_value_classes(self, v):
        if isinstance(v, (list, tuple)):
            for x in v:
                self.add_value_classes(x)
        elif isinstance(v, dict) or type(v).__name__ == "frozendict":
            for k, x in v.items():
                self.add_value_classes(k)
                self.add_value_classes(x)
        elif type(v) not in (int, bool, bytes, str) and isinstance(type(v), type):
            self.b.add(type(v))

    # --- values ---------------------------------------------------------------------------

    def value_type(self, v):
        if type(v) is bool:
            return T.BOOL
        if type(v) is int:
            return T.INT
        if type(v) is bytes:
            return T.BYTES
        if type(v) is str:
            return T.STR
        if isinstance(v, (list, tuple)):
            if isinstance(v, tuple) and len({self.value_type(x) for x in v}) > 1:
                return ("tuple", tuple(self.value_type(x) for x in v))
            elem = self.value_type(v[0]) if v else T.INT
            return ("list", elem, None)
        if isinstance(v, dict) or type(v).__name__ == "frozendict":
            items = list(v.items())
            kt = self.value_type(items[0][0]) if items else T.STR
            vt = self.value_type(items[0][1]) if items else T.INT
            return ("dict", kt, vt)
        t = T.of_class(type(v))
        if t is None:
            raise S.Unsupported(f"value {v!r}")
        return t

    def value_term(self, v, t=None) -> str:
        t = t or self.value_type(v)
        k = t[0]
        if k == "bool":
            return "true" if v else "false"
        if k == "int":
            return f"({v} : Int)"
        if k == "uint":
            return f"(⟨{int(v)}⟩ : {self.b.names.lean(t)})"
        if k == "boolean":
            return f"(⟨{'true' if v else 'false'}⟩ : Boolean)"
        if k in ("bytes", "bytesN"):
            body = f"[{', '.join(str(x) for x in bytes(v))}]"
            return body if k == "bytes" else f"(⟨{body}⟩ : {self.b.names.lean(t)})"
        if k == "str":
            return S.lean_str(v)
        if k == "list":
            return f"[{', '.join(self.value_term(x, t[1]) for x in v)}]"
        if k == "tuple":
            return f"({', '.join(self.value_term(x, tt) for x, tt in zip(v, t[1]))})"
        if k == "dict":
            return "[" + ", ".join(f"({self.value_term(a, t[1])}, {self.value_term(x, t[2])})"
                                   for a, x in v.items()) + "]"
        if k == "container":
            c = t[1]
            if dataclasses.is_dataclass(c):
                hints = dict(self.b.dataclass_fields[c])
                parts = [f"{T.ident(f)} := {self.value_term(getattr(v, f), type_of_hint(self.b, hints[f]))}"
                         for f in hints]
            else:
                parts = [f"{T.ident(f)} := {self.value_term(getattr(v, f), T.of_class(ft))}"
                         for f, ft in c._FIELD_TYPES]
            return "{ " + ", ".join(parts) + " }"
        raise S.Unsupported(f"constant {v!r}")

    def emit_constants(self) -> str:
        out = []
        for name in sorted(self.b.consts):
            v = self.b.consts[name]
            t = self.value_type(v)
            self.b.const_types = getattr(self.b, "const_types", {})
            self.b.const_types[name] = t
            out.append(f"def {T.ident(name)} : {self.b.names.lean(t)} := {self.value_term(v, t)}")
        return "\n".join(out) + "\n"

    def emit_config(self) -> str:
        b = self.b
        b.config_types = {}
        fields, defaults = [], []
        record = ""
        for name in sorted(b.config):
            v = b.config[name]
            if name == "BLOB_SCHEDULE":
                # Entries of `BLOB_SCHEDULE` are records with an epoch and a blob count.
                t = ("list", ("record", "BlobScheduleEntry",
                              (("EPOCH", ("uint", b.spec.Epoch)),
                               ("MAX_BLOBS_PER_BLOCK", ("uint", b.spec.Uint64)))), None)
                record = ("structure BlobScheduleEntry where\n  EPOCH : Epoch\n"
                          "  MAX_BLOBS_PER_BLOCK : Uint64\n"
                          "  deriving DecidableEq, Repr, Inhabited, BEq\n\n")
                b.config_types[name] = t
                fields.append(f"  {name} : List BlobScheduleEntry")
                vals = ", ".join(f"{{ EPOCH := ⟨{int(e['EPOCH'])}⟩, MAX_BLOBS_PER_BLOCK := "
                                 f"⟨{int(e['MAX_BLOBS_PER_BLOCK'])}⟩ }}" for e in v)
                defaults.append(f"  {name} := [{vals}]")
                continue
            t = self.value_type(v)
            b.config_types[name] = t
            fields.append(f"  {T.ident(name)} : {b.names.lean(t)}")
            defaults.append(f"  {T.ident(name)} := {self.value_term(v, t)}")
        overrides = []
        for name in sorted(b.config):
            t = b.config_types[name]
            dec = self.dec_of(t)
            base = f"Cfg.default.{T.ident(name)}"
            if dec is None:
                overrides.append(f"  {T.ident(name)} := {base}")
            else:
                overrides.append(f"  {T.ident(name)} := ((ov.lookup Scope.Id.«{name}»).bind "
                                 f"({dec} Heap.empty)).getD {base}")
        return (record + "/-- The runtime configuration values that the scope reads. -/\nclass Cfg where\n"
                + "\n".join(fields) + "\n\n/-- The configuration of the preset. -/\n"
                "@[reducible] def Cfg.default : Cfg where\n" + "\n".join(defaults) + "\n\n"
                "/-- The configuration with the values of a test case in place. -/\n"
                "@[reducible] def Cfg.ofOverrides (ov : List (Name × Value)) : Cfg where\n"
                + "\n".join(overrides) + "\n")

    # --- functions ------------------------------------------------------------------------

    def build_sigs(self):
        import rd_fn
        from footprint import footprint
        b, spec = self.b, self.b.spec
        ssz_names = {n for n in dir(spec) if isinstance(getattr(spec, n), type)
                     and T.of_class(getattr(spec, n)) is not None}

        def is_heap(t, steps):
            return True
        _, _, per_fn = footprint(b.fns, ssz_names, lambda t, s: True)
        self.sigs = {}
        for name, tree in b.fns.items():
            params = []
            defaults = {}
            args = tree.args
            nd = len(args.defaults)
            for j, a in enumerate(args.args):
                try:
                    t = type_of_annotation(b, a.annotation)
                except S.Unsupported:
                    t = T.ANY
                params.append((a.arg, t))
                if j >= len(args.args) - nd:
                    defaults[a.arg] = args.defaults[j - (len(args.args) - nd)]
            # A sequence of any class, with an element of any class: a type variable.
            if any(t == T.ANY and isinstance(a.annotation, ast.BinOp)
                   for (p, t), a in zip(params, args.args)):
                params = [(p, ("list", ("tvar", "α"), None) if isinstance(a.annotation, ast.BinOp)
                           else ("tvar", "α") if t == T.ANY else t)
                          for (p, t), a in zip(params, args.args)]
            try:
                ret = type_of_annotation(b, tree.returns)
            except S.Unsupported:
                ret = T.ANY
            if ret == T.ANY and params:
                ret = params[0][1]
            mutated = sorted({j for j, _ in per_fn.get(name, [])
                              if params[j][1][0] in ("container", "list", "set", "dict", "tvar")})
            self.sigs[name] = rd_fn.Sig(name, params, defaults, ret, mutated, set())

    def emit_functions(self, only) -> str:
        import rd_fn
        b = self.b
        self.build_sigs()
        self.while_measures = {}
        for line in (Path(__file__).parent / "while_measures.txt").read_text().splitlines():
            if line.strip() and not line.startswith("#"):
                k, v = line.split(":", 1)
                self.while_measures[k.strip()] = v.strip()
        # Callees first.
        order, seen = [], set()

        def visit(n):
            if n in seen or n not in b.fns:
                return
            seen.add(n)
            for c in sorted(S.free_names(b.fns[n])):
                visit(c)
            order.append(n)
        for n in sorted(b.fns):
            visit(n)
        out = []
        self.failures = []
        for n in order:
            if only and n not in only:
                continue
            fn = rd_fn.Fn(self, self.sigs[n], b.fns[n])
            try:
                body = fn.compile()
            except (rd_fn.Unsupported, S.Unsupported, KeyError, TypeError, IndexError,
                    ValueError, AttributeError) as e:
                self.failures.append((n, f"{type(e).__name__}: {e}"))
                out.append(f"-- NOT TRANSLATED: {n}: {e}\n")
                continue
            self.count += 1
            sig = self.sigs[n]
            tv = "{α : Type} [BEq α] " if any(t[0] == "tvar" or (t[0] == "list" and t[1] and
                                                   t[1][0] == "tvar") for _, t in sig.params) else ""
            if any(t[0] == "utvar" for _, t in sig.params):
                tv += "{β : Type} [UintC β] "
            params = " ".join(f"({T.ident(p)} : {self.lean_param(t)})" for p, t in sig.params)
            outs = rd_fn.out_types(sig)
            out_ty = ("Unit" if not outs else self.lean_param(outs[0]) if len(outs) == 1 else
                      "(" + " × ".join(self.lean_param(t) for t in outs) + ")")
            src = b.sources_text[n].rstrip().replace("-/", "- /").replace("/-", "/ -")
            loops = "\n".join(fn.loops)
            out.append(f"{loops}\n/-- ```python\n{src}\n``` -/\n"
                       f"def {T.ident(n)} {tv}{params} : SpecM {out_ty} := do\n{body}\n")
        return "\n".join(out)

    def dec_of(self, t):
        """A decoder of interpreter values for a parameter type, or None."""
        from translate import dec_term
        k = t[0]
        if k in ("uint", "bytesN", "container"):
            return dec_term(self.b, t[1])
        if k == "boolean":
            return "decBooleanV"
        if k == "bool":
            return "decBoolV"
        if k == "int":
            return "decIntV"
        if k == "list" and t[2] is not None:
            return dec_term(self.b, t[2])
        if k == "list" and t[1] is not None:
            inner = self.dec_of(t[1])
            return f"(decListV {inner})" if inner else None
        return None

    def emit_entries(self) -> str:
        """The functions that the EF runner calls, on a readable state and decoded arguments."""
        import rd_fn
        b = self.b
        state_t = ("container", b.spec.BeaconState)
        out = []
        for n, sig in sorted(self.sigs.items()):
            if any(f == n for f, _ in self.failures):
                continue
            if not sig.params or sig.params[0][1] != state_t:
                continue
            if any(t[0] in ("tvar", "utvar") for _, t in sig.params):
                continue
            decs = [self.dec_of(t) for _, t in sig.params[1:]]
            if any(d is None for d in decs):
                continue
            outs = rd_fn.out_types(sig)
            k = outs.index(state_t) if 0 in sig.mutated else None
            pats = ", ".join(f"v{j}" for j in range(1, len(sig.params)))
            binds = "".join(f" let x{j} ← {d} h v{j};" for j, d in zip(range(1, len(sig.params)), decs))
            args = " ".join(f"x{j}" for j in range(1, len(sig.params)))
            if k is None:
                res = "st"
            else:
                res = "r" if len(outs) == 1 else f"({rd_fn.Fn.proj(None, 'r', k, len(outs))})"
            alts = [f"    | [{pats}] => do{binds} some (do let r ← {T.ident(n)} st {args}; pure {res})"]
            # A missing last argument takes its default.
            if sig.params[-1][0] in sig.defaults and len(sig.params) > 1:
                d = sig.defaults[sig.params[-1][0]]
                if isinstance(d, ast.Constant) and type(d.value) is bool:
                    pats2 = ", ".join(f"v{j}" for j in range(1, len(sig.params) - 1))
                    binds2 = "".join(f" let x{j} ← {dd} h v{j};" for j, dd in
                                     zip(range(1, len(sig.params) - 1), decs[:-1]))
                    args2 = " ".join(f"x{j}" for j in range(1, len(sig.params) - 1)) + \
                        (" true" if d.value else " false")
                    alts.append(f"    | [{pats2}] => do{binds2} some (do let r ← {T.ident(n)} st {args2}; pure {res})")
            out.append(f"  (\"{n}\", fun (st : BeaconState) (h : Heap) (vs : List Value) =>\n"
                       f"    match vs with\n" + "\n".join(alts) +
                       "\n    | _ => none)")
        up = ""
        if "upgrade_to_gloas" in self.sigs:
            pre_t = self.sigs["upgrade_to_gloas"].params[0][1]
            up = (f"/-- The fork runner: the upgrade of a decoded older-fork state. -/\n"
                  f"def upgradeEntry (h : Heap) (v : Value) : Option (SpecM BeaconState) := do\n"
                  f"  let pre ← {self.dec_of(pre_t)} h v\n  some (upgrade_to_gloas pre)\n\n")
        bs = b.spec.BeaconState
        diffs = " ++\n    ".join(f"(if a.{T.ident(f)} == b.{T.ident(f)} then [] else [\"{f}\"])"
                                for f, _ in bs._FIELD_TYPES)
        up += ("/-- The fields of two states that differ. The runner prints them on a mismatch. -/\n"
               f"def diffBeaconState (a b : BeaconState) : List String :=\n    {diffs}\n\n")
        return (up + "/-- The entry points of the EF runner: a function on a readable state, with the other\n"
                "arguments as interpreter values. -/\n"
                "def entries : List (String × (BeaconState → Heap → List Value → "
                "Option (SpecM BeaconState))) := [\n" + ",\n".join(out) + "]\n")

    def lean_param(self, t):
        if t == T.ANY:
            return "SszObj"
        if t[0] in ("tvar", "utvar"):
            return t[1]
        if t[0] == "list" and t[1] and t[1][0] == "tvar":
            return f"(List {t[1][1]})"
        return self.b.names.lean(t)
