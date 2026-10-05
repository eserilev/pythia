# signature: ok / bug:typeError
# python: ok ret=None | a0=#0=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000} | a1=Uint64:0 | a2=#1=Box{p=#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#3=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#4=List[Pt,3][],ns=#5=List[Gwei,3][],es=#6=ProgressiveList[Epoch][Epoch:0],bs=#7=Bitlist[4][Boolean:False,Boolean:False],i=ValidatorIndex:0,k=Uint8:0} | a3=#8=list[]
# lean:   err bug:typeError

def mk():
    o0 = Checkpoint(epoch=Epoch(0), root=Root(bytes([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    o1 = Pt(a=Uint64(0))
    o2 = Epochs(data=[Epoch(0)])
    o3 = Bits(data=[Boolean(False)])
    o4 = Box(q=o1, es=o2, bs=o3, i=ValidatorIndex(0), k=Uint8(0))
    return [o0, Uint64(0), o4, []]

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

def f(a0: Checkpoint, a1: Uint64, a2: Box, log):
    a2.bs.append(Gwei(0))