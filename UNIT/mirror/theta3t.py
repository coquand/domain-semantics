"""Theta_P reworked after Towsner (PLAN-THETA3, rework of 3a/2c):
 * atoms are cardinal-like (design H): y < th s iff y <= some A-argument of s;
 * supports are trace points (functions); closure rule:
     th s < th t  if some y in Asupp(t) has th s <= y,
                  or some gamma in supp(t) has gamma[vars := (th s)^-] >= th s;
     th s > th t  symmetrically;
     otherwise compare s, t in P(Delta)(A).
   gamma[vars := b^-]: the k variables of the trace point become k points
   just below b (above everything below b), in order.
"""
from theta3 import subst
from theta3pt import ThetaPt

class ThetaT(ThetaPt):
    def hasSym(self, c):
        return any(isinstance(y, tuple) and len(y) == 2 and y[0] == 's'
                   for y in self.supp(('D', ('Y',)), c))

    def asupp(self, A, s):
        out = []
        for y in self.supp(self.P, s):
            if y not in out: out.append(y)
        return out

    def notClosed(self, A, b, p):
        """gamma[vars := b^-] >= b, for the trace point p = (k, g) and b = th s in Delta(A)"""
        k, g = p
        B = ('sym', A, b, k)
        gi = self.fmapD(lambda i: ('s', i), g)
        bl = self.fmapD(lambda y: ('a', y), b)
        return self.cmp(('D', B), gi, bl) >= 0

    def cmp_(self, T, a, b):
        if T[0] == 'D' and (a[0] == 'at') != (b[0] == 'at'):
            A = T[1]
            if A[0] == 'sym':           # a symbolic point is just below A's bound,
                bl = self.fmapD(lambda y: ('a', y), A[2])   # compared semantically
                if a[0] == 'at' and a[1][0] == 's' and not self.hasSym(b):   # with sym-free terms
                    return -1 if self.cmp(T, bl, b) <= 0 else 1
                if b[0] == 'at' and b[1][0] == 's' and not self.hasSym(a):
                    return 1 if self.cmp(T, bl, a) <= 0 else -1
            if a[0] == 'at':
                return -1 if any(self.cmp(A, a[1], y) <= 0 for y in self.asupp(A, b[1])) else 1
            return 1 if any(self.cmp(A, b[1], y) <= 0 for y in self.asupp(A, a[1])) else -1
        return super().cmp_(T, a, b)

    def cmpth(self, A, a, b):
        if a == b: return 0
        DA = ('D', A); PA = subst(self.P, A)
        if any(self.cmp(DA, a, ('at', y)) <= 0 for y in self.asupp(A, b[1])) or \
           any(self.notClosed(A, a, p) for p in self.K(A, b[1])):
            return -1
        if any(self.cmp(DA, b, ('at', y)) <= 0 for y in self.asupp(A, a[1])) or \
           any(self.notClosed(A, b, p) for p in self.K(A, a[1])):
            return 1
        c = self.cmp(PA, a[1], b[1])
        if c == 0: raise AssertionError(('equal args, distinct terms', a, b))
        return c
