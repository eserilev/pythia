# expect-hit: WTree top entry f: Box.p has 2 paths
def mk():
    o = Pt()
    return [o, Box(p=o), []]


def f(x: Pt, b: Box, log):
    x.s = Slot(3)
    return b.p.s
