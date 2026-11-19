"""Mirror of the type-3 candidate Theta_P (PLAN-THETA3.md, step 2c, design (L)).

P : 2-ptyx given as an expression in Y over the combinators
   ('Y',) | ('one',) | ('sum',A,B) | ('om',A) | ('D',A)
where ('D',A) is Delta applied to A (Delta = the dilator being built).
Delta(A) := atoms ('at',a), a in A  (below all collapses)
          | collapses ('th',s), s in P(Delta)(A).
Order on collapses (Freund/Buchholz shape):
  th s < th t  iff (s < t and K(s) < th t) or th s <= k for some k in K(t)
K_A(s) = maximal components of s that are elements of Delta(A): A-atoms and
Delta-subterms that pull back along the canonical embedding A -> B.
"""
import random, itertools, sys
sys.setrecursionlimit(100000)

class Fail(Exception): pass

def subst(E, F):
    t = E[0]
    if t == 'Y': return F
    if t == 'one' or t == 'base': return E
    if t == 'sum': return ('sum', subst(E[1], F), subst(E[2], F))
    return (t, subst(E[1], F))

def Dn(A, n):
    for _ in range(n): A = ('D', A)
    return A

def lift(x, k):
    for _ in range(k): x = ('at', x)
    return x

class Theta:
    def __init__(self, P): self.P = P; self.memo = {}; self.kmemo = {}

    # ---- order -------------------------------------------------------
    def cmp(self, T, a, b):
        key=(T,a,b)
        r=self.memo.get(key)
        if r is None:
            r=self.cmp_(T,a,b); self.memo[key]=r
        return r

    def cmp_(self, T, a, b):
        t = T[0]
        if t == 'base': return (a > b) - (a < b)
        if t == 'sym':
            A, bb, k = T[1], T[2], T[3]
            if a[0] == 's' and b[0] == 's': return (a[1] > b[1]) - (a[1] < b[1])
            if a[0] == 'a' and b[0] == 'a': return self.cmp(A, a[1], b[1])
            if a[0] == 'a':   # x vs bb^- : x below bb  <=>  x below the symbols
                return -1 if self.cmp(('D', A), ('at', a[1]), bb) < 0 else 1
            return 1 if self.cmp(('D', A), ('at', b[1]), bb) < 0 else -1
        if t == 'one': return 0
        if t == 'sum':
            if a[0] != b[0]: return -1 if a[0] == 'L' else 1
            return self.cmp(T[1] if a[0] == 'L' else T[2], a[1], b[1])
        if t == 'om':                      # Cantor normal forms, lexicographic
            for x, y in zip(a, b):
                c = self.cmp(T[1], x, y)
                if c: return c
            return (len(a) > len(b)) - (len(a) < len(b))
        if t == 'Dw':                      # Delta^omega(A), ('w', n, x)
            k = max(a[1], b[1])
            return self.cmp(Dn(T[1], k), lift(a[2], k - a[1]), lift(b[2], k - b[1]))
        A = T[1]                           # Delta(A)
        if a[0] == 'at' and b[0] == 'at': return self.cmp(A, a[1], b[1])
        if a[0] == 'at': return -1
        if b[0] == 'at': return 1
        return self.cmpth(A, a, b)

    def lt(self, T, a, b): return self.cmp(T, a, b) < 0

    def cmpth(self, A, a, b):
        if a == b: return 0
        if self.lt_th(A, a, b): return -1
        if self.lt_th(A, b, a): return 1
        raise AssertionError(('not linear', a, b))

    def lt_th(self, A, a, b):
        DA = ('D', A); PA = subst(self.P, A)
        s, t = a[1], b[1]
        if self.lt(PA, s, t) and all(self.lt(DA, k, b) for k in self.K(A, s)):
            return True
        return any(self.cmp(DA, a, k) <= 0 for k in self.K(A, t))

    # ---- functoriality (partial maps) --------------------------------
    def fmap(self, E, f, x):
        t = E[0]
        if t == 'Y': return f(x)
        if t in ('one', 'base'): return x
        if t == 'sum':
            return (x[0], self.fmap(E[1] if x[0] == 'L' else E[2], f, x[1]))
        if t == 'om': return tuple(self.fmap(E[1], f, y) for y in x)
        if t == 'Dw': return ('w', x[1], self.fmap(Dn(E[1], x[1]), f, x[2]))
        return self.fmapD(lambda z: self.fmap(E[1], f, z), x)

    def fmapD(self, g, x):
        if x[0] == 'at': return ('at', g(x[1]))
        return ('th', self.fmap(self.P, g, x[1]))

    def pull(self, E):
        """partial inverse of the canonical embedding Y -> E, or None"""
        t = E[0]
        if t == 'Y': return lambda x: x
        if t == 'sum':
            l, r = self.pull(E[1]), self.pull(E[2])
            if (l is None) == (r is None): return None
            if l:
                return lambda x: l(x[1]) if x[0] == 'L' else self._fail()
            return lambda x: r(x[1]) if x[0] == 'R' else self._fail()
        if t == 'om':
            p = self.pull(E[1])
            if p is None: return None
            return lambda x: p(x[0]) if len(x) == 1 else self._fail()
        if t == 'Dw':
            p = self.pull(E[1])
            if p is None: return None
            return lambda x: p(x[2]) if x[1] == 0 else self._fail()
        if t == 'D':
            p = self.pull(E[1])
            if p is None: return None
            return lambda x: p(x[1]) if x[0] == 'at' else self._fail()
        return None
    def _fail(self): raise Fail()

    # ---- coefficient sets --------------------------------------------
    def K(self, A, s):
        if s in self.kmemo: return self.kmemo[s]
        out = []
        self.walkK(self.P, s, out)
        self.kmemo[s] = out
        return out

    def walkK(self, E, s, out):
        t = E[0]
        if t == 'Y': out.append(('at', s)); return
        if t in ('one', 'base'): return
        if t == 'sum': return self.walkK(E[1] if s[0] == 'L' else E[2], s[1], out)
        if t == 'om':
            for y in s: self.walkK(E[1], y, out)
            return
        if t == 'Dw': return self.walkK(Dn(E[1], s[1]), s[2], out)
        E1 = E[1]                          # s in Delta(E1[A])
        p = self.pull(E1)
        if p is not None:
            try:
                out.append(self.fmapD(p, s)); return
            except Fail: pass
        if s[0] == 'at': return self.walkK(E1, s[1], out)
        return self.walkK(subst(self.P, E1), s[1], out)

    # ---- random elements ---------------------------------------------
    def rand(self, T, d):
        t = T[0]
        if t == 'base':
            if T[1] == 0: raise Fail()
            return random.randrange(T[1])
        if t == 'one': return '*'
        if t == 'sum':
            for side in random.sample(['L', 'R'], 2):
                try: return (side, self.rand(T[1] if side == 'L' else T[2], d))
                except Fail: pass
            raise Fail()
        if t == 'om':
            n = random.randrange(0, 3 if d > 0 else 1)
            xs = []
            for _ in range(n):
                try: xs.append(self.rand(T[1], d - 1))
                except Fail: pass
            xs.sort(key=__import__('functools').cmp_to_key(lambda a, b: self.cmp(T[1], a, b)), reverse=True)
            return tuple(xs)
        if t == 'Dw':
            n = random.randrange(3)
            x = self.rand(Dn(T[1], n), d)
            while n > 0 and x[0] == 'at': n, x = n - 1, x[1]
            return ('w', n, x)
        A = T[1]
        if d > 0 and random.random() < 0.7:
            return ('th', self.rand(subst(self.P, A), d - 1))
        return ('at', self.rand(A, d))

    def size(self, x):
        if isinstance(x, tuple): return 1 + sum(self.size(y) for y in x)
        return 1
