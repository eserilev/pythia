# expect-hit: write f: Box.p has 2 paths
def mk():
    return [Box(), []]


def f(b: Box, log):
    b.p = b.q
    b.p.a = Uint64(1)
    return b.q.a
