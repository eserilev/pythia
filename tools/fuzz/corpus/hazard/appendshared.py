# expect-hit: write f: Box.p has 2 paths
def mk():
    return [Box(), []]


def f(b: Box, log):
    b.ps.append(b.p)
    b.p.a = Uint64(2)
    return b.ps[0].a
