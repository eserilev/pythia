# expect-hit: write f: PBox.pp has 2 paths
def mk():
    return [PPts(data=[Pt()]), []]


def f(a0: PPts, log):
    v1 = PBox(pp=a0)
    a0.append(Pt())
    return v1
