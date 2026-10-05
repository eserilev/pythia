# signature: hazard-miss ok (hand-written)
# python: ok ret=#0=PBox{g=Gwei:0,pp=#1=ProgressiveList[Pt][#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#3=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}],pair=#4=Vector[Pt,2][#5=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#6=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]} | a0=#1 | a1=#7=list[]
# lean:   ok ret=#0=PBox{g=Gwei:0,pp=#1=ProgressiveList[Pt][#2=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#3=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}],pair=#4=Vector[Pt,2][#5=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},#6=Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]} | a0=#1 | a1=#7=list[]
# hit:    FP miss f: PBox.pp (x1)
# copy-on-store model: ok ret=PBox{g=Gwei:0,pp=ProgressiveList[Pt][Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}],pair=Vector[Pt,2][Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}]} | a0=ProgressiveList[Pt][Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000},Pt{a=Uint64:0,s=Slot:0,f=Boolean:False,r=Bytes4:00000000}] | a1=list[]

def mk():
    return [PPts(data=[Pt()]), []]


def f(a0: PPts, log):
    v1 = PBox(pp=a0)
    a0.append(Pt())
    return v1
