"""Parse the syntax trees of SpecLean/Gen/Scope.lean into Python tuples."""
import re

TOK = re.compile(r'\s*(?:(\()|(\))|(\[)|(\])|(,)|(\.?[A-Za-z_«][A-Za-z_0-9.«»]*)|(-?\d+)|("(?:[^"\\]|\\.)*")|(\{[^}]*\}))')

def tokenize(s):
    out = []
    i = 0
    while i < len(s):
        m = TOK.match(s, i)
        if not m or m.end() == i:
            if s[i].isspace():
                i += 1
                continue
            raise ValueError("bad token at %r" % s[i:i + 40])
        i = m.end()
        out.append(next(g for g in m.groups() if g is not None))
    return out

class P:
    def __init__(self, toks):
        self.t = toks
        self.i = 0
    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None
    def next(self):
        x = self.t[self.i]; self.i += 1; return x
    def term(self):
        x = self.next()
        if x == '(':
            if self.peek() == ')':
                self.next(); return ('unit',)
            items = [self.term()]
            while self.peek() == ',':
                self.next(); items.append(self.term())
            # application inside parens
            while self.peek() not in (')', None):
                items[-1] = self.app(items[-1])
            assert self.next() == ')'
            return items[0] if len(items) == 1 else ('tuple',) + tuple(items)
        if x == '[':
            items = []
            if self.peek() == ']':
                self.next(); return ('list', [])
            items.append(self.full())
            while self.peek() == ',':
                self.next(); items.append(self.full())
            assert self.next() == ']'
            return ('list', items)
        if re.fullmatch(r'-?\d+', x):
            return ('num', int(x))
        if x.startswith('"'):
            return ('str', x)
        if x.startswith('{'):
            return ('raw', x)
        return ('id', x)
    def app(self, head):
        arg = self.term()
        if head[0] == 'app':
            return head + (arg,)
        return ('app', head, arg)
    def full(self):
        h = self.term()
        while self.peek() not in (')', ']', ',', None):
            h = self.app(h)
        return h

def parse(s):
    p = P(tokenize(s))
    r = p.full()
    return r

def ctor(t):
    """('app', ('id', '.binop'), a, b, ...) -> ('binop', [a, b, ...])"""
    if t[0] == 'app' and t[1][0] == 'id':
        return t[1][1].lstrip('.'), list(t[2:])
    if t[0] == 'id':
        return t[1].lstrip('.'), []
    return None, [t]

def load_scope(path):
    s = open(path).read()
    fns = {}
    for m in re.finditer(r'^def fn_(\w+) : FunctionDef where\n  name := (\d+)\n  params := \{ names := \[([^\]]*)\], defaults := \[([^\]]*)\], vararg := (\w+) \}\n  line := \d+\n  body := (\[.*?\])\n\n', s, re.M | re.S):
        name, fid, pn, dfl, va, body = m.groups()
        fns[name] = dict(id=int(fid), params=[int(x) for x in pn.split(',') if x.strip()],
                         defaults=dfl.strip(), vararg=va, body=parse(body))
    ids = {int(m.group(2)): m.group(1) for m in re.finditer(r'abbrev «([^»]+)» : Name := (\d+)', s)}
    globs = {}
    g = s[s.index('def globals'):]
    g = g[:g.index('\ndef config')]
    for m in re.finditer(r'^  \((\d+), \((.*)\)\),?$', g, re.M):
        globs[int(m.group(1))] = m.group(2)
    return fns, ids, globs
