# expect-hit: write g: Box.p has 2 paths
def mk():
    o = Pt()
    return [Box(p=o, q=o), []]


def g(x: Pt):
    x.a = Uint64(7)


def f(b: Box, log):
    g(b.p)
    return b.q.a
