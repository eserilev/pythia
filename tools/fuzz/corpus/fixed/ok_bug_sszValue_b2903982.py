# signature: ok / bug:sszValue
# python: ok ret=None | a0=#0=Vector[Pt,2][#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}] | a1=#3=Misc{fl=#4=Bitvector[4][Boolean:False,Boolean:False,Boolean:False,Boolean:False],bl=#5=List[Uint8,4][int:0,int:0],n=Uint64:0,cp=#6=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000}} | a2=#7=list[]
# lean:   err bug:sszValue

def mk():
    o0 = Pt()
    o1 = Pt()
    o2 = PtPair(data=[o0, o1])
    o3 = Blob(data=bytes([0]))
    o4 = Checkpoint(root=Root(bytes([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    o5 = Misc(bl=o3, cp=o4)
    return [o2, o5, []]

def tr(log, k, v):
    log.append(k)
    return v


def grow(xs, v):
    if len(xs) < 5:
        xs.append(v)
    return v


def each(xs, fn):
    for x in xs:
        fn(x)

def f(a0: PtPair, a1: Misc, log):
    for x1 in a1.bl:
        a1.bl.append(0)