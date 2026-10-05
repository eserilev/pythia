# expect-hit: write h: Box.p has 2 paths
def mk():
    o = Pt()
    return [PBox(pair=PtPair(data=[o, Pt()])), Box(p=o), []]


def h(p: Pt):
    p.s = Slot(4)


def g(v: PtPair):
    h(v[0])


def f(pb: PBox, b: Box, log):
    g(pb.pair)
    return b.p.s
