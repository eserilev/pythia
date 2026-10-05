# expect-hit: write f: list.* has 2 paths
def mk():
    return [Pt(), []]


def f(x: Pt, log):
    l = Pts(data=[x, x])
    l[0].a = Uint64(5)
    return l[1].a
