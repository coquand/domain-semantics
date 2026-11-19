"""Closure rule (Towsner) with atoms LOW (design L): atoms below all collapses."""
from theta3t import ThetaT

class ThetaTL(ThetaT):
    def cmp_(self, T, a, b):
        if T[0] == 'D' and (a[0] == 'at') != (b[0] == 'at'):
            A = T[1]
            if A[0] == 'sym':
                bl = self.fmapD(lambda y: ('a', y), A[2])
                if a[0] == 'at' and a[1][0] == 's' and not self.hasSym(b):
                    return -1 if self.cmp(T, bl, b) <= 0 else 1
                if b[0] == 'at' and b[1][0] == 's' and not self.hasSym(a):
                    return 1 if self.cmp(T, bl, a) <= 0 else -1
            return -1 if a[0] == 'at' else 1
        return super(ThetaT, self).cmp_(T, a, b)

    def cmpth(self, A, a, b):
        if a == b: return 0
        from theta3 import subst
        PA = subst(self.P, A)
        if any(self.notClosed(A, a, p) for p in self.K(A, b[1])): return -1
        if any(self.notClosed(A, b, p) for p in self.K(A, a[1])): return 1
        c = self.cmp(PA, a[1], b[1])
        if c == 0: raise AssertionError(('equal args, distinct terms', a, b))
        return c
