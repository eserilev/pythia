# expect-hit: write f: Box.p has 2 paths
def mk():
    return [Pt(), []]


def f(a0: Pt, log):
    v1 = Box(p=a0)
    a0.a = Uint64(1)
    return v1
