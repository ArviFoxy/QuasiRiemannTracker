"""Exact Bernstein positivity on boxes (rational arithmetic, sympy QQ polynomials).

positive(P, vars, box, strict=True): certify P > 0 (or >= 0) on the closed box by tensor
Bernstein coefficients, subdividing the widest normalized side when needed.
Returns (ok, n_boxes) or raises on a corner counterexample."""
from fractions import Fraction as Fr
from math import comb
import sympy as sp

def _poly_coeff_array(P, vars):
    """dict {(k1..kd): Fraction} of a sympy Poly in vars."""
    Pp = sp.Poly(P, *vars, domain='QQ')
    out = {}
    for monom, c in Pp.terms():
        out[monom] = Fr(int(c.p), int(c.q))
    degs = [Pp.degree(v) for v in vars]
    return out, degs

def _shift_scale(coeffs, degs, lo, hi):
    """coefficients of P(lo + (hi-lo) u) in u (per variable), exact."""
    d = len(degs)
    cur = dict(coeffs)
    for ax in range(d):
        a, w = lo[ax], hi[ax]-lo[ax]
        nxt = {}
        for monom, c in cur.items():
            k = monom[ax]
            # (a + w u)^k = sum_j C(k,j) a^(k-j) w^j u^j
            for j in range(k+1):
                term = c*comb(k, j)*(a**(k-j))*(w**j)
                if term == 0: continue
                m = list(monom); m[ax] = j; m = tuple(m)
                nxt[m] = nxt.get(m, 0)+term
        cur = nxt
    return cur

def _bernstein(coeffs, degs):
    """tensor Bernstein coefficients on [0,1]^d from power coefficients."""
    import itertools
    d = len(degs)
    # dense array
    shape = [n+1 for n in degs]
    arr = {}
    for idx in itertools.product(*[range(s) for s in shape]):
        arr[idx] = Fr(coeffs.get(idx, 0))
    for ax in range(d):
        n = degs[ax]
        new = {}
        for idx in arr:
            i = idx[ax]
            s = Fr(0)
            for k in range(i+1):
                m = list(idx); m[ax] = k
                s += arr[tuple(m)]*Fr(comb(i, k), comb(n, k)) if n > 0 else arr[tuple(m)]
            new[idx] = s
        arr = new
    return arr

def positive(P, vars, box, strict=True, maxdepth=14, _depth=0):
    if sp.expand(P) == 0:
        if strict:
            raise ValueError("zero polynomial is not strictly positive")
        return True, 1
    lo = [Fr(b[0]) for b in box]; hi = [Fr(b[1]) for b in box]
    coeffs, degs = _poly_coeff_array(P, vars)
    return _positive_coeffs(coeffs, degs, lo, hi, strict, maxdepth, 0)

def _positive_coeffs(coeffs, degs, lo, hi, strict, maxdepth, depth):
    sc = _shift_scale(coeffs, degs, lo, hi)
    B = _bernstein(sc, degs)
    mn = min(B.values())
    if (mn > 0) or (not strict and mn >= 0):
        return True, 1
    # corner values are exact function values: a nonpositive corner is a genuine failure
    import itertools
    for corner in itertools.product(*[(0, n) for n in degs]):
        v = B[corner]
        if (strict and v <= 0) or ((not strict) and v < 0):
            raise ValueError(f"corner failure at depth {depth}: value {float(v):.3e}, box {[(float(a),float(b)) for a,b in zip(lo,hi)]}, corner {corner}")
    if depth >= maxdepth:
        raise ValueError(f"max depth reached; min Bernstein {float(mn):.3e} on box {[(float(a),float(b)) for a,b in zip(lo,hi)]}")
    # split the axis with largest (width * degree)
    ax = max(range(len(degs)), key=lambda i: (hi[i]-lo[i])*max(degs[i], 1))
    mid = (lo[ax]+hi[ax])/2
    n1 = n2 = 0
    l1, h1 = list(lo), list(hi); h1[ax] = mid
    l2, h2 = list(lo), list(hi); l2[ax] = mid
    ok1, n1 = _positive_coeffs(coeffs, degs, l1, h1, strict, maxdepth, depth+1)
    ok2, n2 = _positive_coeffs(coeffs, degs, l2, h2, strict, maxdepth, depth+1)
    return ok1 and ok2, n1+n2

def sign_definite_rational(expr, vars, box, strict=True, maxdepth=14):
    """Certify expr > 0 (strict) / >= 0 on box, expr a rational function: numerator and
    denominator are each certified sign-definite with matching signs."""
    num, den = sp.fraction(sp.together(sp.nsimplify(expr) if False else expr))
    num = sp.expand(num); den = sp.expand(den)
    # denominator must be strictly sign-definite
    try:
        okd, nd = positive(den, vars, box, strict=True, maxdepth=maxdepth)
        sgn = 1
    except ValueError:
        okd, nd = positive(-den, vars, box, strict=True, maxdepth=maxdepth)
        sgn = -1
    okn, nn = positive(sgn*num, vars, box, strict=strict, maxdepth=maxdepth)
    return okn and okd, nn+nd
