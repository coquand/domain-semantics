import random, itertools, sys
from theta3 import Fail
from theta3t import ThetaT
from theta3tl import ThetaTL
Y=('Y',); one=('one',)
Ps={'om D(Y)':('om',('D',Y)),'D(Y+1)':('D',('sum',Y,one)),'om D(Y+1)':('om',('D',('sum',Y,one))),'D(D(Y))':('D',('D',Y)),'om Dw(Y)':('om',('Dw',Y))}
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
for name,P in Ps.items():
  th=(ThetaTL if len(sys.argv)>2 else ThetaT)(P); best=None
  for nb in (0,1,2):
    T=('D',('base',nb)); xs=[]; tries=0
    while len(xs)<60 and tries<20000:
        tries+=1
        try: x=th.rand(T,4)
        except Fail: continue
        if x not in xs: xs.append(x)
    for a,b in itertools.product(xs,repeat=2):
        if th.cmp(T,a,b)!=-th.cmp(T,b,a):
            sz=th.size(a)+th.size(b)
            if best is None or sz<best[0]: best=(sz,nb,a,b,th.cmp(T,a,b),th.cmp(T,b,a))
  print(name, best)
