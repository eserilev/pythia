"""Types of the readable Lean (SPEC 9.1): the static type of each Python value in the spec.

A type is a small tuple:

- ("uint", cls): a uint class of pyspec, such as `Gwei` or `Uint64`.
- ("boolean",): SSZ `Boolean`.
- ("bytesN", cls): a byte vector class, such as `Bytes32` or `Root`.
- ("container", cls): an SSZ container or a dataclass.
- ("list", elem, cls): a sequence. `cls` is the SSZ list class, or None for a Python list.
- ("int",), ("bool",), ("bytes",), ("str",), ("none",).
- ("tuple", (t1, t2, ...)), ("set", elem), ("dict", k, v), ("option", t).
- ("fn", name): a spec function used as a value. ("any",): a generic SSZ object.
"""

import keyword

import ssz.bitfields
import ssz.boolean
import ssz.byte_arrays
import ssz.collections
import ssz.container
import ssz.uint

INT = ("int",)
BOOL = ("bool",)
BYTES = ("bytes",)
STR = ("str",)
NONE = ("none",)
BOOLEAN = ("boolean",)
ANY = ("any",)

WIDTHS = {8, 16, 32, 64, 128, 256}

LEAN_KEYWORDS = {"from", "fun", "end", "at", "by", "do", "then", "else", "if", "let", "in",
                 "match", "with", "have", "show", "def", "theorem", "where", "open", "import",
                 "namespace", "section", "variable", "instance", "structure", "class", "return",
                 "for", "unless", "mut", "break", "continue", "try", "catch", "finally", "type",
                 "Type", "Prop", "Sort", "deriving", "extends", "local", "private", "protected",
                 "partial", "noncomputable", "macro", "syntax", "export", "universe", "true",
                 "false", "λ", "∀", "∃", "this"}


def ident(name: str) -> str:
    """A Lean identifier for a Python name."""
    if name in LEAN_KEYWORDS or keyword.iskeyword(name) and name not in ("None",):
        return f"«{name}»"
    return name


def is_uint_cls(c) -> bool:
    return isinstance(c, type) and issubclass(c, ssz.uint.BaseUint)


def is_container_cls(c) -> bool:
    return isinstance(c, type) and issubclass(
        c, (ssz.container.Container, ssz.container.ProgressiveContainer))


def is_bytesn_cls(c) -> bool:
    return isinstance(c, type) and issubclass(c, ssz.byte_arrays.ByteVector)


def list_info(c):
    """`(kind, elem class, limit)` of an SSZ list class, or None."""
    if not isinstance(c, type):
        return None
    for kind, base in [("progressiveBitlist", ssz.bitfields.ProgressiveBitList),
                       ("bitlist", ssz.bitfields.BitList), ("bitvector", ssz.bitfields.BitVector)]:
        if issubclass(c, base):
            limit = c.LENGTH if kind == "bitvector" else getattr(c, "LIMIT", None)
            return kind, ssz.boolean.Boolean, limit
    if issubclass(c, ssz.byte_arrays.ByteList):
        return "list", ssz.uint.Uint8, c.LIMIT
    for kind, base in [("progressiveList", ssz.collections.ProgressiveList),
                       ("list", ssz.collections.List), ("vector", ssz.collections.Vector)]:
        if issubclass(c, base):
            if "ELEMENT_TYPE" not in dir(c) and not hasattr(c, "_ELEMENT_TYPE"):
                try:
                    c.ELEMENT_TYPE
                except AttributeError:
                    return None
            limit = None if kind == "progressiveList" else (c.LIMIT if kind == "list" else c.LENGTH)
            return kind, c.ELEMENT_TYPE, limit
    return None


def of_class(c):
    """The type of a value of class `c`."""
    if c is int:
        return INT
    if c is bool:
        return BOOL
    if c is bytes:
        return BYTES
    if c is str:
        return STR
    if c is type(None):
        return NONE
    if is_uint_cls(c):
        return ("uint", c)
    if isinstance(c, type) and issubclass(c, ssz.boolean.Boolean):
        return BOOLEAN
    if is_bytesn_cls(c):
        return ("bytesN", c)
    if is_container_cls(c):
        return ("container", c)
    li = list_info(c)
    if li is not None:
        return ("list", of_class(li[1]), c)
    import dataclasses
    if isinstance(c, type) and dataclasses.is_dataclass(c):
        return ("container", c)
    return None


def uint_width(c) -> type:
    """The width class of a uint class: `Uint64` for `Gwei`."""
    for b in c.__mro__:
        if b.__bases__ and ssz.uint.BaseUint in b.__bases__:
            return b
    return c


def uint_bits(c) -> int:
    return c.BITS


def derive(a, b):
    """The class of `a op b` for two uint types: the more derived class wins."""
    ca, cb = a[1], b[1]
    if ca is cb or issubclass(ca, cb):
        return a
    if issubclass(cb, ca):
        return b
    return a


class Names:
    """Lean names of pyspec classes. A class of an older fork gets the fork prefix."""

    def __init__(self, spec, prev_fork="fulu"):
        self.spec = spec
        self.prev = prev_fork

    def cls(self, c) -> str:
        n = c.__name__
        if getattr(self.spec, n, None) is c:
            return n
        if is_uint_cls(c) and c.BITS in WIDTHS and n == f"Uint{c.BITS}":
            return n
        return f"{self.prev}_{n}"

    def scope(self, c) -> str:
        """The name of a class in the interpreter build (`fulu.BeaconState`)."""
        n = self.cls(c)
        return n.replace(f"{self.prev}_", f"{self.prev}.", 1) if n.startswith(f"{self.prev}_") else n

    def lean(self, t) -> str:
        k = t[0]
        if k == "uint":
            return self.cls(t[1])
        if k == "boolean":
            return "Boolean"
        if k == "bytesN":
            return self.cls(t[1])
        if k == "container":
            return self.cls(t[1])
        if k == "list":
            return f"(List {self.lean(t[1])})"
        if k == "int":
            return "Int"
        if k == "bool":
            return "Bool"
        if k == "bytes":
            return "Bytes"
        if k == "str":
            return "String"
        if k == "none":
            return "Unit"
        if k == "tuple":
            return "(" + " × ".join(self.lean(x) for x in t[1]) + ")" if t[1] else "Unit"
        if k == "set":
            return f"(List {self.lean(t[1])})"
        if k == "dict":
            return f"(List ({self.lean(t[1])} × {self.lean(t[2])}))"
        if k == "option":
            return f"(Option {self.lean(t[1])})"
        if k in ("tvar", "utvar"):
            return t[1]
        if k == "record":
            return t[1]
        if k == "nat":
            return "Nat"
        if k == "any":
            return "SszObj"
        raise ValueError(f"no Lean type for {t}")
