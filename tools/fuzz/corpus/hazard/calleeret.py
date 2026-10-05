# expect-hit: write f: Box.p has 2 paths
def mk():
    return [Box(), []]


def get(b: Box) -> Pt:
    return b.p


def f(b: Box, log):
    b.q = get(b)
    b.q.a = Uint64(9)
    return b.p.a
