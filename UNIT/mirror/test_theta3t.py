import random, sys, itertools
from theta3 import Fail, subst
from theta3t import ThetaT as Theta
Y=('Y',); one=('one',)
def S(a,b): return ('sum',a,b)
def D(a): return ('D',a)
def om(a): return ('om',a)
Ps = {
 'D(Y+1)'        : D(S(Y,one)),
 'om D(Y+1)'     : om(D(S(Y,one))),
 'D(D(Y))'       : D(D(Y)),
 'om D(Y)'       : om(D(Y)),
 'om(D Y)+D(1+Y)': S(om(D(Y)), D(S(one,Y))),
 'om D(om(Y)+1)' : om(D(S(om(Y),one))),
 'om Dw(Y)'      : om(('Dw',Y)),
 'om Dw(Y)+1'    : S(om(('Dw',Y)),one),
}
def samples(th, T, n, d):
    out=[]; tries=0
    while len(out)<n and tries<20000:
        tries+=1
        try: x=th.rand(T,d)
        except (Fail,RecursionError): continue
        if th.size(x)<400 and x not in out: out.append(x)
    return out
import time
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
for name,P in Ps.items():
    th=Theta(P); bad=0; t0=time.time(); print("start",name,flush=True)
    for nb in (0,1,2):
        T=D(('base',nb)); xs=samples(th,T,50,6); print('  base',nb,'samples',len(xs),flush=True)
        for a,b in itertools.product(xs,repeat=2):
            c=th.cmp(T,a,b)
            assert c==-th.cmp(T,b,a)
            assert (c==0)==(a==b), (a,b)
        for a,b,c in itertools.product(xs[:25],repeat=3):
            if th.lt(T,a,b) and th.lt(T,b,c): assert th.lt(T,a,c),(a,b,c)
        # naturality along increasing f : base nb -> base nb+2
        for f in itertools.combinations(range(nb+2),nb):
            g=lambda i,f=f: f[i]
            for a,b in itertools.product(xs[:30],repeat=2):
                fa=th.fmapD(lambda z:th.fmap(Y,g,z),a); fb=th.fmapD(lambda z:th.fmap(Y,g,z),b)
                assert th.cmp(D(('base',nb+2)),fa,fb)==th.cmp(T,a,b)
    print("ok", name, round(time.time()-t0,1), flush=True)
