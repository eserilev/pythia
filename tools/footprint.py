"""The global footprint FP of a set of spec functions (SPEC 9.2).

A pattern is `(T, steps)`: the root is an object of SSZ type `T`, and each step is a field
name or `*` for any element. FP holds the patterns of every object that a function changes in
place: a container whose field is set, and a list whose element is set, that gets an append or
that gets a slice assignment.

The analysis is flow-insensitive. A local gets the patterns of every value assigned to it. A
pattern rooted at a parameter goes to the callers: each call site puts the argument's
patterns in front of it. A pattern rooted at a type (a parameter's annotation, or a
constructor call) goes to FP.
"""

import ast

MUTATORS = {"append", "extend", "insert", "pop", "remove", "clear", "add", "update", "sort",
            "reverse"}


class Fn:
    def __init__(self, name, tree):
        self.name = name
        self.tree = tree
        self.params = [a.arg for a in tree.args.args]
        # Writes: (line, root, steps). A root is ("param", i) or ("type", T).
        self.writes = set()
        # Calls: (callee, [patterns of each argument]).
        self.calls = []


def annotation_type(ann, ssz_names):
    match ann:
        case ast.Name(id=x) if x in ssz_names:
            return x
        case ast.Attribute(attr=x) if x in ssz_names:
            return x
    return None


def analyze(name, tree, ssz_names, returns):
    """`ssz_names`: SSZ type names. `returns`: return type of each spec function, or None."""
    fn = Fn(name, tree)
    env: dict[str, set] = {}
    for i, p in enumerate(fn.params):
        env[p] = {(("param", i), ())}

    def pats(e) -> set:
        match e:
            case ast.Name(id=x):
                return env.get(x, set())
            case ast.Attribute(value=o, attr=f):
                return {(r, s + (f,)) for r, s in pats(o)}
            case ast.Subscript(value=o, slice=ast.Slice()):
                return set()
            case ast.Subscript(value=o):
                return {(r, s + ("*",)) for r, s in pats(o)}
            case ast.Call(func=ast.Name(id=t)) if t in ssz_names:
                return {(("type", t), ())}
            case ast.Call(func=ast.Name(id=g)) if returns.get(g) in ssz_names:
                return {(("type", returns[g]), ())}
            case ast.Call(func=ast.Attribute(value=o, attr="copy")):
                # A deep copy is a new root of the same type.
                return {(("copy", r), s) for r, s in pats(o)}
        return set()

    def write(line, e):
        for r, s in pats(e):
            fn.writes.add((line, r, s))

    def bind(t, ps):
        match t:
            case ast.Name(id=x):
                env.setdefault(x, set()).update(ps)
            case ast.Tuple(elts=ts) | ast.List(elts=ts):
                for x in ts:
                    bind(x, set())

    def target(t, line):
        match t:
            case ast.Attribute(value=o):
                write(line, o)
            case ast.Subscript(value=o):
                write(line, o)
            case ast.Tuple(elts=ts) | ast.List(elts=ts):
                for x in ts:
                    target(x, line)

    def expr(e):
        for n in ast.walk(e):
            match n:
                case ast.Call(func=ast.Attribute(value=o, attr=m)) if m in MUTATORS:
                    write(n.lineno, o)
                case ast.Call(func=ast.Name(id=g), args=args):
                    fn.calls.append((g, [pats(a) for a in args]))

    def stmt(s):
        match s:
            case ast.Assign(targets=ts, value=v):
                expr(v)
                for t in ts:
                    target(t, s.lineno)
                    bind(t, pats(v))
            case ast.AnnAssign(target=t, value=v) if v is not None:
                expr(v)
                target(t, s.lineno)
                bind(t, pats(v))
            case ast.AugAssign(target=t, value=v):
                expr(v)
                target(t, s.lineno)
                if isinstance(t, ast.Name):
                    write(s.lineno, t)
            case ast.For(target=t, iter=it, body=b, orelse=o):
                expr(it)
                match it, t:
                    case ast.Call(func=ast.Name(id="enumerate"), args=[x]), ast.Tuple(elts=[i, v]):
                        bind(i, set())
                        bind(v, {(r, s2 + ("*",)) for r, s2 in pats(x)})
                    case _:
                        bind(t, {(r, s2 + ("*",)) for r, s2 in pats(it)})
                for x in b + o:
                    stmt(x)
            case ast.While(test=c, body=b, orelse=o) | ast.If(test=c, body=b, orelse=o):
                expr(c)
                for x in b + o:
                    stmt(x)
            case ast.FunctionDef(body=b):
                for x in b:
                    stmt(x)
            case _:
                for n in ast.iter_child_nodes(s):
                    if isinstance(n, ast.expr):
                        expr(n)

    # Two passes, so a local assigned after its first use still gets its patterns.
    for _ in range(2):
        for s in tree.body:
            stmt(s)
    # A call through a parameter, as `fn(state, operation)` in the nested `for_ops`, may call
    # any spec function that the code passes as an argument.
    refs = {a.id for n in ast.walk(tree) if isinstance(n, ast.Call)
            for a in n.args if isinstance(a, ast.Name) and a.id in returns}
    fn.calls += [(r, args) for g, args in fn.calls if g not in returns for r in refs]
    return fn


def footprint(fns: dict, ssz_names: set, is_heap):
    """FP, the write sites and `Footprint f` of each function. `fns`: name -> ast.FunctionDef. `is_heap(T, steps)` tells if
    the pattern names a container or a list. A pattern that names a uint comes from `x += y`
    on a local, which rebinds `x`: it is not in FP."""
    returns = {n: annotation_type(t.returns, ssz_names) for n, t in fns.items()}
    info = {n: analyze(n, t, ssz_names, returns) for n, t in fns.items()}
    # Summary: param-rooted patterns that each function writes, through its callees too.
    summary = {n: {(r[1], s) for _, r, s in f.writes if r[0] == "param"} for n, f in info.items()}
    typed = set()
    changed = True
    while changed:
        changed = False
        for n, f in info.items():
            for g, args in f.calls:
                for j, s in summary.get(g, set()).copy():
                    if j >= len(args):
                        continue
                    for r, s0 in args[j]:
                        new = (r, s0 + s)
                        if r[0] == "param" and (r[1], new[1]) not in summary[n]:
                            summary[n].add((r[1], new[1]))
                            changed = True
                        elif r[0] == "type":
                            typed.add((r[1], new[1]))
    fp = set(typed)

    def root_type(n, r):
        if r[0] == "param":
            return annotation_type(fns[n].args.args[r[1]].annotation, ssz_names)
        if r[0] == "type":
            return r[1]
        return None

    sites = []
    for n, f in info.items():
        for line, r, s in f.writes:
            if r[0] == "copy":
                r = r[1]
            t = root_type(n, r)
            if t is not None and is_heap(t, s):
                fp.add((t, s))
                sites.append((n, line, t, s))
        for j, s in summary[n]:
            t = root_type(n, ("param", j))
            if t is not None and is_heap(t, s):
                fp.add((t, s))
    # Footprint f: the parameter-rooted patterns that f writes, through its callees too. A
    # pattern under a parameter of unknown type stays: the check finds no object there.
    per_fn = {}
    for n in info:
        keep = []
        for j, s in summary[n]:
            t = root_type(n, ("param", j))
            if t is None or is_heap(t, s):
                keep.append((j, s))
        per_fn[n] = sorted(keep)
    return sorted(t for t in fp if is_heap(*t)), sorted(sites), per_fn
