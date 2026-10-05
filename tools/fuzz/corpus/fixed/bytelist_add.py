# signature: ok (hand-written bytelist_add)
# python: ok ret=(bytes:01020304,bytes:04010203,bytes:0102030000,bytes:00010203,bytes:010203) | a0=#0=Misc{fl=#1=Bitvector[4][Boolean:False,Boolean:False,Boolean:False,Boolean:False],bl=#2=List[Uint8,4][int:1,int:2,int:3],n=Uint64:0,cp=#3=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000}} | a1=#4=list[]
# lean:   ok ret=(bytes:01020304,bytes:04010203,bytes:0102030000,bytes:00010203,bytes:010203) | a0=#0=Misc{fl=#1=Bitvector[4][Boolean:False,Boolean:False,Boolean:False,Boolean:False],bl=#2=List[Uint8,4][int:1,int:2,int:3],n=Uint64:0,cp=#3=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000}} | a1=#4=list[]

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
    return (b + [4], [4] + b, b + 2, Gwei(1) + b, Gweis() + b)
