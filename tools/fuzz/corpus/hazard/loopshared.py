# expect-hit: write f: list.* has 2 paths
def mk():
    o = Pt()
    return [Pts(data=[o, o]), []]


def f(xs: Pts, log):
    for x in xs:
        x.a += 1
    return xs[0].a
