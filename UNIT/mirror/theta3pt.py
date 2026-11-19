"""Variant of theta3 with GENERIC coefficient sets (PLAN-THETA3 step 3a):
the Delta-support of sigma in P(Delta)(A) is a list of TRACE POINTS of Delta,
compared in the Pt2 order (image in Delta(omega), then arity).  Atoms are
below all collapses, so the A-support condition is automatic in design (L).
  th s < th t  iff  (s < t and supp(s) <Pt tr(th t))  or  tr(th s) <=Pt p
                    for some p in supp(t).
"""
import functools
from theta3 import Theta, subst, Dn

class ThetaPt(Theta):
    # support of x in E[base] as a list of base elements
    def supp(self, E, x):
        t = E[0]
        if t == 'Y': return [x]
        if t in ('one', 'base'): return []
        if t == 'sum': return self.supp(E[1] if x[0] == 'L' else E[2], x[1])
        if t == 'om': return [b for y in x for b in self.supp(E[1], y)]
        if t == 'Dw': return self.supp(Dn(E[1], x[1]), x[2])
        if x[0] == 'at': return self.supp(E[1], x[1])
        return self.supp(subst(self.P, E[1]), x[1])

    def tr(self, B, x):
        """trace point (c, xhat) of x in Delta(B)"""
        key = ('tr', B, x)
        if key in self.memo: return self.memo[key]
        S = []
        for b in self.supp(('D', ('Y',)), x):
            if b not in S: S.append(b)
        S.sort(key=functools.cmp_to_key(lambda a, b: self.cmp(B, a, b)))
        idx = {b: i for i, b in enumerate(S)}
        r = (len(S), self.fmapD(lambda b: idx[b], x))
        self.memo[key] = r
        return r

    def cmpPt(self, p, q):
        k = max(p[0], q[0])
        c = self.cmp(('D', ('base', k)), p[1], q[1])
        return c if c else (p[0] > q[0]) - (p[0] < q[0])

    # Delta-support of x in E[A] as trace points
    def pts(self, E, A, x, out):
        t = E[0]
        if t in ('Y', 'one', 'base'): return
        if t == 'sum': return self.pts(E[1] if x[0] == 'L' else E[2], A, x[1], out)
        if t == 'om':
            for y in x: self.pts(E[1], A, y, out)
            return
        if t == 'Dw': return self.pts(Dn(E[1], x[1]), A, x[2], out)
        B = subst(E[1], A)
        out.append(self.tr(B, x))
        for b in self.supp(('D', ('Y',)), x):
            self.pts(E[1], A, b, out)

    def K(self, A, s):
        key = (A, s)
        if key in self.kmemo: return self.kmemo[key]
        out = []
        self.pts(self.P, A, s, out)
        self.kmemo[key] = out
        return out

    def lt_th(self, A, a, b):
        PA = subst(self.P, A)
        s, t = a[1], b[1]
        ta, tb = self.tr(A, a), self.tr(A, b)
        if self.lt(PA, s, t) and all(self.cmpPt(p, tb) < 0 for p in self.K(A, s)):
            return True
        return any(self.cmpPt(ta, p) <= 0 for p in self.K(A, t))
