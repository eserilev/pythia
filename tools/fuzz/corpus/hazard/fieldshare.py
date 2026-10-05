# expect-hit: write f: Box.ps has 2 paths
def mk():
    return [Box(ps=Pts(data=[Pt()])), []]


def f(a: Box, log):
    p = Box(ps=a.ps)
    p.ps[0] = Pt(a=Uint64(1))
    return p
