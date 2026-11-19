import itertools, functools, sys
from theta3 import Theta, Fail, subst
Y=('Y',); one=('one',)
def S(a,b): return ('sum',a,b)
def D(a): return ('D',a)
def om(a): return ('om',a)
def enum(th, T, n):
    """all elements of type T of size <= n"""
    t=T[0]; out=[]
    if n<=0: return []
    if t=='base': return list(range(T[1])) if n>=1 else []
    if t=='one': return ['*'] if n>=1 else []
    if t=='sum':
        return [('L',x) for x in enum(th,T[1],n-1)]+[('R',x) for x in enum(th,T[2],n-1)]
    if t=='om':
        xs=sorted(enum(th,T[1],n-2),key=functools.cmp_to_key(lambda a,b:th.cmp(T[1],a,b)),reverse=True)
        res=[()]
        def go(pre,i,budget):
            for j in range(i,len(xs)):
                c=th.size(xs[j])
                if c<=budget:
                    w=pre+(xs[j],); res.append(w); go(w,j,budget-c)
        go((),0,n-1); return res
    A=T[1]
    return [('at',x) for x in enum(th,A,n-1)]+[('th',s) for s in enum(th,subst(th.P,A),n-1)]
def show(x):
    if x=='*': return '*'
    if isinstance(x,int): return 'y%d'%x
    if x==(): return '0'
    if x[0]=='at': return show(x[1]) if isinstance(x[1],int) or x[1][0] in ('L','R') else '<'+show(x[1])+'>'
    if x[0]=='th': return 'T('+show(x[1])+')'
    if x[0] in('L','R'): return x[0].lower()+show(x[1])
    return '+'.join('w^'+show(e) for e in x)
P=eval(sys.argv[1]); n=int(sys.argv[2]); nb=int(sys.argv[3])
th=Theta(P); T=D(('base',nb))
xs=sorted(enum(th,T,n),key=functools.cmp_to_key(lambda a,b:th.cmp(T,a,b)))
for x in xs[:int(sys.argv[4]) if len(sys.argv)>4 else 40]: print(show(x))
print(len(xs),'elements')
