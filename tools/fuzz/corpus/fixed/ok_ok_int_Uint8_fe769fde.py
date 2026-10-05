# signature: ok-ok int/Uint8
# python: ok ret=#0=Misc{fl=#1=Bitvector[4][Boolean:False,Boolean:False,Boolean:False,Boolean:False],bl=#2=List[Uint8,4][int:0,int:0,int:0,int:0],n=Uint64:0,cp=#3=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000}} | a0=#4=Box{p=#5=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#6=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#7=List[Pt,3][],ns=#8=List[Gwei,3][],es=#9=ProgressiveList[Epoch][],bs=#10=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a1=#11=PBox{g=Gwei:0,pp=#12=ProgressiveList[Pt][],pair=#13=Vector[Pt,2][#14=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#15=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]} | a2=#16=List[Gwei,3][Gwei:0] | a3=#17=list[]
# lean:   ok ret=#0=Misc{fl=#1=Bitvector[4][Boolean:False,Boolean:False,Boolean:False,Boolean:False],bl=#2=List[Uint8,4][Uint8:0,Uint8:0,Uint8:0,Uint8:0],n=Uint64:0,cp=#3=Checkpoint{epoch=Epoch:0,root=Root:0000000000000000000000000000000000000000000000000000000000000000}} | a0=#4=Box{p=#5=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},q=#6=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},ps=#7=List[Pt,3][],ns=#8=List[Gwei,3][],es=#9=ProgressiveList[Epoch][],bs=#10=Bitlist[4][],i=ValidatorIndex:0,k=Uint8:0} | a1=#11=PBox{g=Gwei:0,pp=#12=ProgressiveList[Pt][],pair=#13=Vector[Pt,2][#14=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#15=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]} | a2=#16=List[Gwei,3][Gwei:0] | a3=#17=list[]

def mk():
    o0 = Box()
    o1 = PBox()
    o2 = Gweis(data=[Gwei(0)])
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

def f(a0: Box, a1: PBox, a2: Gweis, log):
    return Misc(bl=Blob(data=[0, 0, 0, 0]))

