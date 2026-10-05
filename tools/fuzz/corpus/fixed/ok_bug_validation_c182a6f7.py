# signature: ok / bug:validation
# python: ok ret=#0=Box{p=#1=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#3=List[Pt,3][],ns=#4=List[Gwei,3][],es=#5=ProgressiveList[Epoch][],bs=#6=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a0=#7=List[Gwei,3][] | a1=#8=List[Gwei,3][Gwei:0] | a2=#9=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000} | a3=#10=list[]
# lean:   err bug:validation

def mk():
    o0 = Gweis(data=[])
    o1 = Gweis2(data=[Gwei(0)])
    o2 = Checkpoint(root=Root(bytes([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    return [o0, o1, o2, []]

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

def f(a0: Gweis, a1: Gweis2, a2: Checkpoint, log):
    return Box(k=Boolean(False))

