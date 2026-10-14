from fractions import Fraction as Q
from math import comb
class Poly:
    def __init__(self, value=0):
        if isinstance(value, dict): self.c = {k: Q(v) for k, v in value.items() if v}
        else: self.c = {(0, 0): Q(value)} if value else {}
    def __add__(self, o):
        o = o if isinstance(o, Poly) else Poly(o); out = dict(self.c)
        for k, v in o.c.items(): out[k] = out.get(k, Q(0)) + v
        return Poly(out)
    __radd__ = __add__
    def __neg__(self): return Poly({k: -v for k, v in self.c.items()})
    def __sub__(self, o): return self + (-(o if isinstance(o, Poly) else Poly(o)))
    def __rsub__(self, o): return (-self) + o
    def __mul__(self, o):
        o = o if isinstance(o, Poly) else Poly(o); out = {}
        for (i, j), a in self.c.items():
            for (k, l), b in o.c.items():
                out[(i+k, j+l)] = out.get((i+k, j+l), Q(0)) + a*b
        return Poly(out)
    __rmul__ = __mul__
    def __truediv__(self, o): return self * (1/Q(o))
    def at(self, a, b): return sum(v * Q(a)**i * Q(b)**j for (i, j), v in self.c.items())
    def deg(self):
        return (max([i for i, j in self.c] or [0]), max([j for i, j in self.c] or [0]))
delta = Poly({(1, 0): 1}); p = Poly({(0, 1): 1})
def bernstein(poly, box, m, n):
    a, b, c, d = map(Q, box)
    f = {}
    for (i, j), value in poly.c.items():
        assert i <= m and j <= n, (i, j, m, n)
        for r in range(i+1):
            for s in range(j+1):
                f[(r, s)] = f.get((r, s), Q(0)) + value*comb(i, r)*a**(i-r)*(b-a)**r*comb(j, s)*c**(j-s)*(d-c)**s
    # power basis in (u,v) on [0,1]^2 -> Bernstein degree (m,n)
    return [[sum(f.get((r, s), Q(0))*Q(comb(i, r), comb(m, r))*Q(comb(j, s), comb(n, s))
                 for r in range(i+1) for s in range(j+1)) for j in range(n+1)] for i in range(m+1)]
def certify(poly, box, m, n, maxdepth=30, minsplit=None):
    """adaptive subdivision; returns list of (box, coeffs)"""
    out = []; stack = [(tuple(map(Q, box)), 0)]
    while stack:
        bx, dep = stack.pop()
        co = bernstein(poly, bx, m, n)
        if min(min(r) for r in co) > 0:
            out.append((bx, co)); continue
        if dep >= maxdepth: raise Exception(('fail', [float(t) for t in bx]))
        a, b, c, d = bx
        # split the longer side relative to domain scale (delta range 3/4, p range 1/2)
        if (b-a)/Q(3,4) >= (d-c)/Q(1,2):
            mid = (a+b)/2; stack += [((a, mid, c, d), dep+1), ((mid, b, c, d), dep+1)]
        else:
            mid = (c+d)/2; stack += [((a, b, c, mid), dep+1), ((a, b, mid, d), dep+1)]
    return out
