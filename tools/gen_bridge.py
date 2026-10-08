"""Generate the step 6 bridge: the readable Lean (SpecLean.Rd.Gen) against the hand-written spec of
the Lighthouse epoch proofs (EpochProofs.Spec).

    python3 tools/gen_bridge.py [--hand DIR]

It reads SpecLean/Gen/Readable.lean and the hand spec sources, and writes
Bridge/Bridge/Gen/Types.lean: for each type in both models, `abs_T` (readable to hand) and
`IR_T` (each uint in range, each byte vector of its length), and one `rfl` check per constant
that both models define.
"""

import argparse
import glob
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HAND = ROOT.parent / "lighthouse-epoch-proofs/consensus/state_processing/proofs/EpochProofs/Spec"
HNS = "EpochProofs.Spec"

# Constants whose hand value is not the minimal preset value (the build of the `decide` check
# fails for them). The hand spec writes the mainnet value as a global constant.
KNOWN_DIFF = {"PENDING_CONSOLIDATIONS_LIMIT", "PENDING_PARTIAL_WITHDRAWALS_LIMIT",
              "MIN_BUILDER_WITHDRAWABILITY_DELAY", "CONSOLIDATION_CHURN_LIMIT_QUOTIENT"}


def structs(text):
    out = {}
    for m in re.finditer(r"^structure (\w+) where\n((?:  .*\n)+)", text, re.M):
        fs = []
        for line in m.group(2).split("\n"):
            mm = re.match(r"  (\w+) : (.+?)(?: := .*)?$", line)
            if mm and not line.strip().startswith("deriving"):
                fs.append((mm.group(1), strip_parens(mm.group(2).strip())))
        out[m.group(1)] = fs
    return out


def strip_parens(t):
    t = t.strip()
    while t.startswith("(") and t.endswith(")") and balanced(t[1:-1]):
        t = t[1:-1].strip()
    return t


def split_prod(t):
    """Split a product type at its top-level `×`."""
    parts, d, cur = [], 0, ""
    for c in t:
        if c == "(":
            d += 1
        elif c == ")":
            d -= 1
        if c == "×" and d == 0:
            parts.append(strip_parens(cur))
            cur = ""
        else:
            cur += c
    parts.append(strip_parens(cur))
    return parts


def balanced(s):
    d = 0
    for c in s:
        d += c == "("
        d -= c == ")"
        if d < 0:
            return False
    return d == 0


# The readable Lean of each preset, the output directory, and the module name of the readable Lean.
PRESETS = {
    "minimal": ("SpecLean/Gen/Readable.lean", "Gen", "SpecLean.Gen.Readable"),
    "mainnet": ("Bridge/Bridge/Mainnet/Readable.lean", "GenMainnet", "Bridge.Mainnet.Readable"),
}


def for_preset(text, preset):
    """The minimal text, rewritten for `preset`: readable namespace, output modules, namespace,
    the hand preset, and the readable module."""
    if preset == "minimal":
        return text.replace("import Bridge.Tactic\n", "import Bridge.Tactic\nimport SpecLean.Gen.Readable\n")
    types = "import Bridge.Tactic\n" in text
    text = text.replace("import Bridge.Tactic\n",
                        "import Bridge.Tactic\nimport Bridge.Mainnet.Readable\n")
    text = re.sub(r"\bBridge\.Gen\.", "Bridge.GenMainnet.", text)
    text = re.sub(r"(?<![\w.])Gen\.", "GenMainnet.", text)
    hand = ("/-- The preset of this bridge: mainnet. -/\n"
            "abbrev Hand := EpochProofs.Spec.Preset.mainnet\n") if types else ""
    text = text.replace("namespace Pythia.Bridge\n",
                        "namespace Pythia.Bridge.Mainnet\n\nopen Pythia.Bridge\n\n" + hand)
    text = text.replace("end Pythia.Bridge\n", "end Pythia.Bridge.Mainnet\n")
    text = text.replace("Preset.minimal", "Preset.mainnet")
    return text


class Model:
    def __init__(self, hand_dir, preset="minimal"):
        self.rd_text = (ROOT / PRESETS[preset][0]).read_text()
        self.hd_text = "\n".join(Path(f).read_text()
                                 for f in sorted(glob.glob(f"{hand_dir}/**/*.lean", recursive=True)))
        self.rd = structs(self.rd_text)
        self.hd = structs(self.hd_text)
        self.uints = {m.group(1): int(m.group(2)) for m in
                      re.finditer(r"^instance : UintC (\w+) := ⟨(\d+),", self.rd_text, re.M)}
        self.bytes = {m.group(1): int(m.group(2)) for m in
                      re.finditer(r"^instance : BytesC (\w+) := ⟨(\d+),", self.rd_text, re.M)}
        self.habbrev = {m.group(1): m.group(2).strip() for m in
                        re.finditer(r"^abbrev (\w+) := (.+)$", self.hd_text, re.M)}

    def hresolve(self, t):
        t = strip_parens(t)
        seen = 0
        while t in self.habbrev and seen < 10:
            t = strip_parens(self.habbrev[t])
            seen += 1
        return t

    def conv(self, rt, ht):
        """A function term from readable type `rt` to hand type `ht`, or None."""
        rt, h = strip_parens(rt), self.hresolve(ht)
        rps, hps = split_prod(rt), split_prod(h)
        if len(rps) > 1 or len(hps) > 1:
            if len(rps) != len(hps):
                return None
            cs = [self.conv(a, b) for a, b in zip(rps, hps)]
            if any(c is None for c in cs):
                return None
            return self.prod_conv(rps, cs)
        if rt.startswith("Option ") and h.startswith("Option "):
            inner = self.conv(rt[7:], h[7:])
            return None if inner is None else f"(Option.map {inner})"
        if rt.startswith("List ") and h.startswith("List "):
            inner = self.conv(rt[5:], h[5:])
            return None if inner is None else f"(List.map {inner})"
        if rt in self.uints:
            if h == "Nat":
                return f"(fun x : Gen.{rt} => x.val)"
            if h == "UInt8":
                return f"(fun x : Gen.{rt} => UInt8.ofNat x.val)"
            return None
        if rt in self.bytes:
            m = re.fullmatch(r"Vector UInt8 (\d+)", h)
            if m and int(m.group(1)) == self.bytes[rt]:
                return f"(fun x : Gen.{rt} => toVec {m.group(1)} x.data)"
            return None
        if rt == "Boolean" and h == "Bool":
            return "Boolean.val"
        if rt == "Int" and h == "Nat":
            return "Int.toNat"
        if rt == "Bool" and h == "Bool":
            return "(fun x : Bool => x)"
        if rt in self.rd and h == rt and rt in self.hd:
            return f"abs_{rt}"
        if rt in ("Bytes", "List UInt8") and h == "List UInt8":
            return "(fun x : List UInt8 => x)"
        return None

    def prod_conv(self, rps, cs):
        if len(cs) == 1:
            return cs[0]
        rest = self.prod_conv(rps[1:], cs[1:])
        return f"(fun x : {self.rty(' × '.join(f'({r})' for r in rps))} => ({cs[0]} x.1, {rest} x.2))"

    def ir(self, rt):
        """A predicate term on readable type `rt`: in range."""
        rt = strip_parens(rt)
        if len(split_prod(rt)) > 1:
            return "(fun _ => True)"
        if rt.startswith("Option "):
            return f"(fun o : Option ({self.rty(rt[7:])}) => ∀ y ∈ o, {self.ir(rt[7:])} y)"
        if rt.startswith("List "):
            return (f"(fun xs : List ({self.rty(rt[5:])}) => xs.length < 2 ^ 64 ∧ "
                    f"∀ y ∈ xs, {self.ir(rt[5:])} y)")
        if rt in self.uints:
            return f"(fun x : Gen.{rt} => x.val < 2 ^ {self.uints[rt]})"
        if rt in self.bytes:
            return f"(fun x : Gen.{rt} => x.data.length = {self.bytes[rt]})"
        if rt in self.rd:
            return f"IR_{rt}"
        if rt == "Int":
            return "(fun x : Int => 0 ≤ x)"
        return "(fun _ => True)"

    def rty(self, rt):
        rt = strip_parens(rt)
        if rt.startswith("Option "):
            return f"Option ({self.rty(rt[7:])})"
        ps = split_prod(rt)
        if len(ps) > 1:
            return " × ".join(f"({self.rty(p)})" for p in ps)
        if rt.startswith("List "):
            return f"List ({self.rty(rt[5:])})"
        if rt in self.uints or rt in self.bytes or rt in self.rd:
            return f"Gen.{rt}"
        return rt


def beta(conv, arg):
    """`conv arg`, with a `fun x : T => body` applied by substitution."""
    mm = re.fullmatch(r"\(fun x : [^=]+ => (.+)\)", conv)
    if mm:
        return re.sub(r"\bx\b", f"({arg})", mm.group(1))
    return f"{conv} {arg}"


def gen_oracle(m):
    """`OracleAgrees o`: the hand oracle `o` agrees with the readable oracle (`Spec`) on values in
    range: `sha256`, each `hash_tree_root_T` whose type both models have, and the BLS functions."""
    fields = dict(m.hd.get("Oracle", []))
    encs = set(re.findall(r"^def enc_(\w+) ", m.rd_text, re.M))
    lines = ["", "/-- The hand oracle `o` agrees with the oracle of the readable Lean on values in range. -/",
             "structure OracleAgrees [Spec] (o : EpochProofs.Spec.Oracle) : Prop where",
             "  hash : ∀ l : List UInt8, (Spec.sha256 l).length = 32 ∧ toVec 32 (Spec.sha256 l) = o.hash l"]
    for f, ty in fields.items():
        mm = re.fullmatch(r"hash_tree_root_(\w+)", f)
        if not mm:
            continue
        t = mm.group(1)
        hin = ty.split("→")[0].strip()
        if t not in encs:
            continue
        conv = m.conv(t, hin)
        if conv is None:
            continue
        ir = m.ir(t)
        lines.append(f"  htr_{t} : ∀ x : {m.rty(t)}, {ir} x → ∃ r, htr enc_{t} x = .ok r ∧ "
                     f"r.length = 32 ∧ toVec 32 r = o.{f} ({beta(conv, 'x')})")
    if "bls_Verify" in fields:
        lines.append("  bls_Verify : ∀ pk m sig : List UInt8, pk.length = 48 → m.length = 32 → "
                     "sig.length = 96 → Spec.blsVerify pk m sig = "
                     "o.bls_Verify (toVec 48 pk) (toVec 32 m) (toVec 96 sig)")
    if "bls_FastAggregateVerify" in fields:
        lines.append("  bls_FastAggregateVerify : ∀ (pks : List (List UInt8)) (m sig : List UInt8), "
                     "(∀ pk ∈ pks, pk.length = 48) → m.length = 32 → sig.length = 96 → "
                     "Spec.blsFastAggregateVerify pks m sig = "
                     "o.bls_FastAggregateVerify (pks.map (toVec 48)) (toVec 32 m) (toVec 96 sig)")
    if "bls_AggregatePKs" in fields:
        lines.append("  bls_AggregatePKs : ∀ pks : List (List UInt8), (∀ pk ∈ pks, pk.length = 48) → "
                     "(Spec.blsAggregatePKs pks).length = 48 ∧ "
                     "toVec 48 (Spec.blsAggregatePKs pks) = o.bls_AggregatePKs (pks.map (toVec 48))")
    if "bls_KeyValidate" in fields:
        lines.append("  bls_KeyValidate : ∀ pk : List UInt8, pk.length = 48 → "
                     "Spec.blsKeyValidate pk = o.bls_KeyValidate (toVec 48 pk)")
    if "bls_SubtractPK" in fields:
        lines.append("  bls_SubtractPK : ∀ a b : List UInt8, a.length = 48 → b.length = 48 → "
                     "(Spec.blsG1Add a (Spec.blsG1Neg b)).length = 48 ∧ "
                     "toVec 48 (Spec.blsG1Add a (Spec.blsG1Neg b)) = o.bls_SubtractPK (toVec 48 a) (toVec 48 b)")
    lines.append("")
    return lines


def gen_types(m):
    out = ["-- Generated by tools/gen_bridge.py. Do not edit.",
           "import Bridge.Tactic", "", "namespace Pythia.Bridge", "",
           "open SpecLean SpecLean.Rd", "", "set_option maxRecDepth 4000", ""]
    for u, bits in m.uints.items():
        out.append(f"@[simp, bridge_simp, bridge_ir, bridge_cast] theorem val_{u} (x : Gen.{u}) : UintC.val x = x.val := rfl")
        out.append(f"@[simp, bridge_simp, bridge_cast] theorem ofNat_{u} (n : Nat) : "
                   f"(UintC.ofNat n : Gen.{u}).val = n := rfl")
        out.append(f"@[simp, bridge_simp, bridge_ir] theorem bits_{u} : UintC.bits Gen.{u} = {bits} := rfl")
    for b, n in m.bytes.items():
        out.append(f"@[simp, bridge_simp, bridge_ir, bridge_cast] theorem len_{b} : BytesC.len Gen.{b} = {n} := rfl")
        out.append(f"@[simp, bridge_simp, bridge_cast] theorem data_{b} (x : Gen.{b}) : BytesC.data x = x.data := rfl")
    out.append("")
    done, skipped = [], []
    for name, fields in m.rd.items():
        if name in m.uints or name in m.bytes or name not in m.hd:
            continue
        hf = dict(m.hd[name])
        convs = []
        for f, rt in fields:
            c = m.conv(rt, hf.get(f, "?"))
            convs.append((f, rt, c))
        if [f for f, _ in fields] != [f for f, _ in m.hd[name]] or any(c is None for _, _, c in convs):
            skipped.append(name)
            continue
        body = ", ".join(f"{f} := {c} x.{f}" for f, _, c in convs)
        out.append(f"@[bridge_simp] def abs_{name} (x : Gen.{name}) : {HNS}.{name} := {{ {body} }}")
        irs = " ∧ ".join(f"{m.ir(rt)} x.{f}" for f, rt, _ in convs) or "True"
        out.append(f"@[bridge_ir] def IR_{name} (x : Gen.{name}) : Prop := {irs}")
        out.append("")
        done.append(name)
    out.append(f"-- {len(done)} types. Not mapped: {', '.join(skipped) or 'none'}.")
    out.append("")
    # Constants that both models define.
    rconst = {mm.group(1): mm.group(2) for mm in
              re.finditer(r"^def ([A-Z][A-Z0-9_]+) : (\w+) :=", m.rd_text, re.M)}
    hconst = {mm.group(1): mm.group(2).strip() for mm in
              re.finditer(r"^def ([A-Z][A-Z0-9_]+) : (.+?) :=", m.hd_text, re.M)}
    preset = [f for f, _ in m.hd.get("Preset", [])]
    checks = []
    for c, rt in sorted(rconst.items()):
        if c in hconst:
            target, ht = f"{HNS}.{c}", hconst[c]
        elif c in preset:
            target, ht = f"Hand.{c}", dict(m.hd["Preset"])[c]
        else:
            continue
        conv = m.conv(rt, ht)
        if conv is None:
            continue
        if c in KNOWN_DIFF:
            out.append(f"-- differs: {c} (the hand spec has the mainnet value)")
            continue
        checks.append(c)
        out.append(f"@[bridge_const] theorem const_{c} : {beta(conv, f'Gen.{c}')} = {target} := by decide")
        if rt in m.bytes:
            out.append(f"@[bridge_const] theorem constL_{c} : (Gen.{c}).data = ({target}).toList := by decide")
        if not target.startswith("Hand."):
            out.append(f"attribute [bridge_simp] Gen.{c} {target}")
        else:
            out.append(f"attribute [bridge_simp] Gen.{c}")
    # Configuration values: the readable `Cfg.default` (minimal) against the hand value.
    cm = re.search(r"^class Cfg where\n((?:  .*\n)+)", m.rd_text, re.M)
    for line in (cm.group(1).split("\n") if cm else []):
        mm = re.match(r"  (\w+) : (\w+)$", line)
        if not mm:
            continue
        c, rt = mm.group(1), mm.group(2)
        if c in hconst:
            target, ht = f"{HNS}.{c}", hconst[c]
        elif c in preset:
            target, ht = f"Hand.{c}", dict(m.hd["Preset"])[c]
        else:
            continue
        conv = m.conv(rt, ht)
        if conv is None:
            continue
        if c in KNOWN_DIFF:
            out.append(f"-- differs: Cfg.{c} (the hand spec has the mainnet value)")
            continue
        checks.append("Cfg." + c)
        out.append(f"@[bridge_const] theorem const_cfg_{c} : "
                   f"{beta(conv, f'(Gen.Cfg.default).{c}')} = {target} := by decide")
    out.append("@[bridge_const] theorem const_zero32 : toVec 32 (List.replicate 32 0) = "
               "EpochProofs.Spec.Bytes32.zero := by decide")
    out += gen_oracle(m)
    out.append("attribute [bridge_simp] Hand EpochProofs.Spec.Preset.minimal")
    for c in sorted(rconst):
        if c not in checks:
            out.append(f"attribute [bridge_simp] Gen.{c}")
    for c in sorted(hconst):
        if c not in checks and c not in KNOWN_DIFF and re.match(r"^[A-Z_0-9]+$", c):
            out.append(f"attribute [bridge_simp] {HNS}.{c}")
    out.append("")
    out.append("end Pythia.Bridge")
    return "\n".join(out) + "\n", done, skipped, checks


LEAN_KEYWORDS = {"from", "at", "end", "fun", "let", "in", "do", "then", "else", "if", "match",
                 "with", "by", "have", "show", "where", "open", "import", "theorem", "def"}


def split_binders(sig):
    """`(a b : T) (c : U) : R` -> ([(a, T), (b, T), (c, U)], R). Skips `{}` and `[]` binders."""
    out, i, n = [], 0, len(sig)
    while i < n:
        c = sig[i]
        if c in "([{":
            close = {"(": ")", "[": "]", "{": "}"}[c]
            d, j = 0, i
            while j < n:
                if sig[j] in "([{":
                    d += 1
                elif sig[j] in ")]}":
                    d -= 1
                    if d == 0:
                        break
                j += 1
            inner = sig[i + 1:j]
            if c == "(" and " : " in inner:
                names, ty = inner.split(" : ", 1)
                ty = ty.split(" := ")[0]
                for nm in names.split():
                    out.append((nm, strip_parens(ty)))
            i = j + 1
        elif c == ":":
            return out, sig[i + 1:].strip()
        else:
            i += 1
    return out, None


def fn_sigs(text, multiline):
    sigs = {}
    for m in re.finditer(r"^def ([A-Za-z_0-9]+) ", text, re.M):
        if m.group(1) in sigs:
            continue
        # The signature runs to the first `:=` outside parentheses.
        i, d, sig = m.end(), 0, None
        while i < len(text) - 1:
            c = text[i]
            if c in "([{":
                d += 1
            elif c in ")]}":
                d -= 1
            elif d == 0 and text.startswith(":=", i):
                sig = text[m.end():i]
                break
            elif not multiline and c == "\n":
                break
            i += 1
        if sig is None:
            continue
        binders, ret = split_binders(sig.replace("\n", " "))
        if ret is not None:
            sigs[m.group(1)] = (binders, ret)
    return sigs


def bodies(text):
    out = {}
    for m in re.finditer(r"^def ([A-Za-z_0-9.]+) .*?(?=^def |^/--|^theorem |^end |\Z)", text,
                         re.M | re.S):
        out.setdefault(m.group(1), m.group(0))
    return out


def q(n):
    return f"«{n}»"


class Stmt:
    def __init__(self, name, binders, irs, rd_call, hd_call, ret_conv, pure, post):
        self.post = post
        self.name, self.binders, self.irs = name, binders, irs
        self.rd_call, self.hd_call, self.ret_conv, self.pure = rd_call, hd_call, ret_conv, pure

    def prop(self):
        bs = " ".join(f"({q(n)} : {t})" for n, t in self.binders)
        hs = " → ".join(self.irs + [""]) if self.irs else ""
        hd = f"(pure ({self.hd_call}))" if self.pure else f"({self.hd_call})"
        lead = f"∀ {bs}, " if bs else ""
        return f"{lead}{hs}SimI {self.post} {self.ret_conv} ({self.rd_call}) {hd}"


def statement(m, name, rsigs, hsigs):
    """The bridge statement of `name`, or the reason there is none."""
    if name not in rsigs or name not in hsigs:
        return None, "no signature"
    rbs, rret = rsigs[name]
    hbs, hret = hsigs[name]
    rmap = dict(rbs)
    oracle = False
    if name == "compute_signing_root":
        return signing_root_statement(m, rbs, hbs, hret)
    rm = re.fullmatch(r"SpecM (.+)", rret)
    if not rm:
        return None, "readable return"
    rret = strip_parens(rm.group(1))
    args, used = [], set()
    for n, t in hbs:
        if t == "Preset":
            args.append("Hand")
            continue
        if t == "Oracle":
            args.append("o")
            oracle = True
            continue
        if n not in rmap:
            return None, "parameters"
        c = m.conv(rmap[n], t)
        if c is None:
            return None, f"type of {n}"
        args.append(f"({c} {q(n)})")
        used.add(n)
    if set(rmap) != used:
        return None, "parameters"
    hm = re.fullmatch(r"SpecM (.+)", hret)
    pure = hm is None
    hret_t = strip_parens(hret if pure else hm.group(1))
    rc = m.conv(rret, hret_t)
    if rc is None:
        return None, "return type"
    binders = [(n, m.rty(t)) for n, t in rbs]
    irs = []
    for n, t in rbs:
        ir = m.ir(t)
        if ir != "(fun _ => True)":
            irs.append(f"{ir} {q(n)}")
    rd_call = f"Gen.{name} " + " ".join(q(n) for n, _ in rbs) if rbs else f"Gen.{name}"
    hd_call = f"{HNS}.{name} " + " ".join(args) if args else f"{HNS}.{name}"
    post = m.ir(rret) if (rret in m.uints or rret in m.bytes) else "(fun _ => True)"
    if oracle:
        binders = [("o", "EpochProofs.Spec.Oracle")] + binders
        irs = ["OracleAgrees «o»"] + irs
        hd_call = hd_call.replace(" o ", " «o» ").replace(" o)", " «o»)")
        if hd_call.endswith(" o"):
            hd_call = hd_call[:-2] + " «o»"
    return Stmt(name, binders, irs, rd_call, hd_call, rc, pure, post), None


def signing_root_statement(m, rbs, hbs, hret):
    """`compute_signing_root`: the readable Lean takes the object, the hand spec takes its root."""
    if [n for n, _ in rbs] != ["ssz_object", "domain"]:
        return None, "parameters"
    binders = [("o", "EpochProofs.Spec.Oracle"), ("ssz_object", "SszObj"), ("r", "List UInt8"),
               ("domain", "Gen.Domain")]
    irs = ["OracleAgrees «o»", "htrObj «ssz_object» = .ok «r»", "«r».length = 32",
           "«domain».data.length = 32"]
    st = Stmt("compute_signing_root", binders, irs, "Gen.compute_signing_root «ssz_object» «domain»",
              f"{HNS}.compute_signing_root «o» (toVec 32 «r») (toVec 32 «domain».data)",
              "(fun x : Gen.Root => toVec 32 x.data)", True, "(fun x : Gen.Root => x.data.length = 32)")
    return st, None


HEADER = """import {imp}

namespace Pythia.Bridge

open SpecLean SpecLean.Rd

attribute [local instance] Gen.Cfg.default
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable [Spec]
"""


def plan(m):
    """The statements, the callees of each function, and the functions without a statement."""
    rsigs, hsigs = fn_sigs(m.rd_text, False), fn_sigs(m.hd_text, True)
    mapped = (ROOT / "tools/bridge_targets.txt").read_text().split()
    # The mapped functions, and the other functions that both models define (their callees).
    targets = mapped + [n for n in rsigs if n in hsigs and n not in mapped]
    stmts, why = {}, {}
    for n in targets:
        st, reason = statement(m, n, rsigs, hsigs)
        if st:
            stmts[n] = st
        else:
            why[n] = reason
    rbodies = bodies(m.rd_text)
    loops = {n for n in targets if f"{n}.loop1" in rbodies}
    callees = {}
    for n in stmts:
        text = "".join(b for k, b in rbodies.items() if k == n or k.startswith(n + ".loop"))
        callees[n] = sorted(c for c in stmts if c != n and re.search(rf"\b{c}\b", text))
    return stmts, why, loops, callees


def gen_specs(stmts):
    out = ["-- Generated by tools/gen_bridge.py. Do not edit.", HEADER.format(imp="Bridge.Gen.Types")]
    for n, st in stmts.items():
        out.append(f"/-- The bridge statement of `{n}`. -/")
        out.append(f"abbrev spec_{n} : Prop :=\n  {st.prop()}\n")
    out.append("end Pythia.Bridge")
    return "\n".join(out) + "\n"


def proof(st, callees):
    names = [q(n) for n, _ in st.binders] + [f"hr{i}" for i in range(len(st.irs))]
    intro = f"  intro {' '.join(names)}\n" if names else ""
    opts = [q(n) for n, t in st.binders if t.startswith("Option ")]
    cases = "  " + " <;> ".join(f"cases {n}" for n in opts) + "\n"
    body = (f"bridge_split; unfold Gen.{st.name} {HNS}.{st.name}; "
            f"(try simp only [bind_pure, Option.map_none, Option.map_some]); (try dsimp only); bridge_main")
    if opts:
        return f"{intro}{cases}  all_goals ({body})\n"
    return (f"{intro}  bridge_split\n  unfold Gen.{st.name} {HNS}.{st.name}\n"
            f"  try simp only [bind_pure]\n  bridge_main\n")


def cond_theorem(st, callees):
    hyps = " ".join(f"(h_{c} : spec_{c})" for c in callees)
    return f"theorem cond_{st.name} {hyps} : spec_{st.name} := by\n{proof(st, callees)}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hand", default=str(HAND))
    ap.add_argument("--trials", default=None, help="write one trial file per function here")
    ap.add_argument("--proved", default=None, help="file with the names whose trial passed")
    ap.add_argument("--preset", default="minimal", choices=sorted(PRESETS))
    args = ap.parse_args()
    global KNOWN_DIFF
    if args.preset == "mainnet":
        KNOWN_DIFF = set()
    m = Model(args.hand, args.preset)
    gen = PRESETS[args.preset][1]
    outdir = ROOT / "Bridge/Bridge" / gen
    outdir.mkdir(parents=True, exist_ok=True)
    fp = lambda t: for_preset(t, args.preset)
    text, done, skipped, checks = gen_types(m)
    (outdir / "Types.lean").write_text(fp(text))
    print(f"types: {len(done)} mapped, {len(skipped)} skipped {skipped}; constants: {len(checks)}")
    stmts, why, loops, callees = plan(m)
    (outdir / "Specs.lean").write_text(fp(gen_specs(stmts)))
    print(f"statements: {len(stmts)}; none: {len(why)}")
    if args.trials:
        d = Path(args.trials)
        d.mkdir(parents=True, exist_ok=True)
        for n, st in stmts.items():
            if n in loops:
                continue
            body = HEADER.format(imp="Bridge.Gen.Specs") + "\n" + cond_theorem(st, callees[n])
            (d / f"{n}.lean").write_text(fp(body + "\nend Pythia.Bridge\n"))
    if args.proved:
        proved = set(Path(args.proved).read_text().split())
        write_eqs(stmts, why, loops, callees, proved, outdir, fp)


def write_eqs(stmts, why, loops, callees, proved, outdir, fp):
    out = ["-- Generated by tools/gen_bridge.py. Do not edit.", HEADER.format(imp="Bridge.Gen.Specs")]
    order = []
    seen = set()

    def visit(n):
        if n in seen:
            return
        seen.add(n)
        for c in callees[n]:
            visit(c)
        order.append(n)
    for n in stmts:
        visit(n)
    full = set()
    for n in order:
        if n not in proved:
            continue
        out.append(cond_theorem(stmts[n], callees[n]))
        if all(c in full for c in callees[n]):
            full.add(n)
            args = " ".join(f"full_{c}" for c in callees[n])
            out.append(f"theorem full_{n} : spec_{n} := cond_{n} {args}\n")
    mapped = (ROOT / "tools/bridge_targets.txt").read_text().split()
    nonloop = [n for n in stmts if n not in loops]
    mnl = [n for n in mapped if n not in loops]
    out.append(f"-- Mapped functions: {len(mapped)}, {len(mnl)} without a loop, "
               f"{len([n for n in mnl if n in stmts])} of them with a statement.")
    out.append(f"-- Conditional: {len([n for n in mnl if n in proved])} mapped, "
               f"{len([n for n in proved if n not in mapped])} callees "
               f"({len(proved)} of {len(nonloop)} statements without a loop).")
    out.append(f"-- Full: {len([n for n in mnl if n in full])} mapped, "
               f"{len([n for n in full if n not in mapped])} callees.")
    out.append(f"-- Not proved: {', '.join(sorted(set(nonloop) - proved)) or 'none'}.")
    out.append(f"-- Loops (statement only): {', '.join(sorted(n for n in stmts if n in loops))}.")
    for reason in sorted(set(why[n] for n in mapped if n in why)):
        out.append(f"-- No statement ({reason}): "
                   f"{', '.join(sorted(n for n in mapped if why.get(n) == reason))}.")
    out.append("")
    out.append("end Pythia.Bridge")
    (outdir / "Eqs.lean").write_text(fp("\n".join(out) + "\n"))
    print(f"conditional {len(proved)}, full {len(full)}")


if __name__ == "__main__":
    main()
