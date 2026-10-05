# signature: ok-ok Slot/Uint64
# python: ok ret=None | a0=#0=PBox{g=Gwei:0,pp=#1=ProgressiveList[Pt][#2=Pt{a=Slot:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}],pair=#3=Vector[Pt,2][#4=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#5=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]} | a1=#6=List[Gwei,3][Gwei:0] | a2=#7=list[]
# lean:   ok ret=None | a0=#0=PBox{g=Gwei:0,pp=#1=ProgressiveList[Pt][#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}],pair=#3=Vector[Pt,2][#4=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#5=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]} | a1=#6=List[Gwei,3][Gwei:0] | a2=#7=list[]

def mk():
    o0 = PBox()
    o1 = Gweis(data=[Gwei(0)])
    return [o0, o1, []]

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

def f(a0, a1, log):
    a0.pp[0:1] = [Pt()]
    a0.pp[0] = Pt(a=(Uint64(0) + Slot(0)))