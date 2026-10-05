# expect-no-sharing-hit (the old object is out of the box when it is written)
def mk():
    return [Box(), []]


def f(b: Box, log):
    v = b.p
    b.p = Pt()
    v.a = Uint64(1)
    return b.p.a
