# signature: ok (hand-written bytelist_reads)
# python: ok ret=(int:7,bytes:0203,#0=list[int:7,int:2,int:3,int:1],int:1,bool:True) | a0=#1=Misc{fl=#2=Bitvector[4][Boolean:False,Boolean:False,Boolean:False,Boolean:False],bl=#3=List[Uint8,4][int:7,int:2,int:3,int:1],n=Uint64:0,cp=#4=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000}} | a1=#5=list[]
# lean:   ok ret=(int:7,bytes:0203,#0=list[int:7,int:2,int:3,int:1],int:1,bool:True) | a0=#1=Misc{fl=#2=Bitvector[4][Boolean:False,Boolean:False,Boolean:False,Boolean:False],bl=#3=List[Uint8,4][int:7,int:2,int:3,int:1],n=Uint64:0,cp=#4=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000}} | a1=#5=list[]

def mk():
    o0 = Misc(bl=Blob(data=[1, 2, 3]))
    return [o0, []]

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

def f(a0: Misc, log):
    b = a0.bl
    b[0] = Gwei(7)
    b.append(True)
    return (b[0], b[1:3], [x for x in b], b.index(2), Gwei(2) in b)
