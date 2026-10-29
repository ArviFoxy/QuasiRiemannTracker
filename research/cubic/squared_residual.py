"""squared_residual.py -- the cubic transfer that exists INSIDE the sextic framework: squared columns.

Sextic Gauss sums on a squared modulus are cubic (imprimitive reduction, Lean `square_gauss`).
  S1  g6(D^2 n, D H') = g6(D^2, D H') g6(n, D^3 H')                (R1/R2 doubled block, simple residual n; c = 2*2+2 = 6)
  S2  g6(D^2 m^2, D H') = g6(D^2, D H') g6(m^2, H')                (squared residual m^2: NO dilation; c = 2*2-1 = 3)
  S3  g6(D^2 m^2, D H') = c * g6(D^2,DH') g6(m^2, D^s D H') with c constant over m  <=>  s = 2 (mod 3)  [k(2m+s) = 0 mod 6, k = 2]
  S4  imprimitive reduction g6(m^2, m Y) = N(m) * conj?/phase * g3(m, Y)  -- report the ratio pattern for squarefree m
"""
import sys, math, cmath, random
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/newpowers/r1')
sys.path.insert(0, '$SCRATCH/cubic')
import zw
from zw import mul, pw, norm
import importlib.util

rng = random.Random(7)
PR = [p for p in zw.prime_elements(60) if norm(p) > 4]


def gauss_k(s, h, k):
    import numpy as np
    S = zw.get_modulus(s)
    X, Y = S.reps()
    h0, h1 = S.mod.reduce(h)
    P0 = h0 * X - h1 * Y
    P1 = h0 * Y + h1 * X - h1 * Y
    c0, c1 = S.cs
    W1 = P0 * c1 + P1 * c0 - P1 * c1
    ph = np.exp(2j * np.pi * ((W1 % S.N) / S.N))
    ex = S.exps()
    m = ex >= 0
    zeta = np.exp(2j * np.pi * ((k * ex[m]) % 6) / 6.0)
    return complex(np.sum(zeta * ph[m]))


def chi(s, x):
    return zw.get_modulus(s).chi(x)


def rand_h(cop, R=30):
    while True:
        h = (rng.randrange(-R, R), rng.randrange(-R, R))
        if h != (0, 0) and chi(cop, h) is not None:
            return h


TOL = 1e-7
NCAP = 300000
ok1 = ok2 = tot = 0
for _ in range(150):
    D = rng.choice([p for p in PR if norm(p) <= 31])
    k = rng.choice([1, 2])
    ms = rng.sample([p for p in PR if norm(p) <= 19 and p != D], k)
    m = (1, 0)
    for p in ms:
        m = mul(m, p)
    n = m
    if norm(D) ** 2 * norm(m) ** 2 > NCAP:
        continue
    Y = rand_h(mul(D, m))
    H = mul(m, Y)            # residual columns m^2 are supported on m || frequency: H' = m Y
    h = mul(D, H)
    D2 = pw(D, 2)
    # S1: simple residual n = m (squarefree), residual at D^3 H'
    if norm(D) ** 2 * norm(n) <= NCAP:
        l1 = gauss_k(mul(D2, n), mul(D, Y), 1)
        r1 = gauss_k(D2, mul(D, Y), 1) * gauss_k(n, mul(pw(D, 3), Y), 1)
        ok1 += abs(l1 - r1) < TOL * max(1, abs(l1))
    # S2: squared residual m^2, residual at H' (no dilation)
    m2 = pw(m, 2)
    l2 = gauss_k(mul(D2, m2), h, 1)
    r2 = gauss_k(D2, h, 1) * gauss_k(m2, H, 1)
    ok2 += abs(l2 - r2) < TOL * max(1, abs(l2))
    nz2 = globals().get('nz2', 0) + (abs(l2) > 1e-6); globals()['nz2'] = nz2
    tot += 1
print(f"S1 doubled block, simple residual at D^3 H': {ok1}/{tot}")
print(f"S2 doubled block, squared residual at H' (no dilation): {ok2}/{tot}  (nonzero cases: {globals().get('nz2',0)})")

# S3: exponent scan for squared residuals
res = {}
for s in range(-1, 6):
    consts = set(); good = True; nz = 0
    for _ in range(25):
        D = rng.choice([p for p in PR if norm(p) <= 31])
        m = rng.choice([p for p in PR if norm(p) <= 37 and p != D])
        if norm(D) ** 2 * norm(m) ** 2 > NCAP:
            continue
        Y = rand_h(mul(D, m))
        H = mul(m, Y)
        h = mul(D, H)
        m2 = pw(m, 2)
        X = H if s == -1 else mul(pw(D, s), h)
        lhs = gauss_k(mul(pw(D, 2), m2), h, 1)
        rhs0 = gauss_k(pw(D, 2), h, 1) * gauss_k(m2, X, 1)
        if abs(rhs0) < 1e-6:
            # residual vanishes off m | X: here X is prime to m, so g6(m^2,X) = 0 identically -> test on X*m instead
            pass
        if abs(rhs0) < 1e-6:
            continue
        nz += 1
        r = lhs / rhs0
        a = cmath.phase(r) / (2 * math.pi) * 6
        if abs(abs(r) - 1) > 1e-6 or abs(a - round(a)) > 1e-6:
            good = False; break
        consts.add(round(a) % 6)
    res[s] = (good and len(consts) == 1, sorted(consts), nz)
print("S3 squared residual, s = -1..5:", res)
