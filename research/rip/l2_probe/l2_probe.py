"""(L2) probe for D1: do cubic Gauss sums over primes, twisted by a quadratic character (k/pi)_2, lose the Patterson
main term?  Sums over primary split primes pi with N(pi) = p <= X (normalized g~(pi) = g(pi)/sqrt(p), |g~| = 1):
  T0(X)       = sum g~(pi)                                   (Heath-Brown-Patterson: main term ~ X^{5/6})
  Tcub(X; k)  = sum g~(pi) (k/pi)_3      = sum g~(k^2, pi)   (parameter k^2: theta coefficient at a square)
  Tcub2(X; k) = sum g~(pi) conj (k/pi)_3 = sum g~(k, pi)     (parameter k: Patterson main term expected)
  Tquad(X; k) = sum g~(pi) (k/pi)_2                          (quadratic twist: no main term expected, k != square)
  Tsex(X; k)  = sum g~(pi) (k/pi)_2 conj((k/pi)_3)           (the sextic twist that D1's dual produces)
Reports |T| / sqrt(#primes) and local slopes d log|T| / d log X.  usage: python3 -I l2_probe.py X Kmax nk
"""
import sys, os, math, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
MP = os.path.normpath(os.path.join(HERE, '..', 'moments_probe'))
sys.path.insert(0, MP)
import numpy as np
import fastgauss as FG
from zw import Arith

X = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
NK = int(sys.argv[3]) if len(sys.argv) > 3 else 12
t0 = time.time()
ar = Arith(max(X, KMAX) + 10)
primes = ar.elems(1, X, primes_only=True)
tab, worst = FG.prime_table(primes, ar.spf, verbose=True)
P = np.array([e['ps'][0] for e in primes], dtype=np.int64)
R = np.array([e['rs'][0] for e in primes], dtype=np.int64)
G = np.array([tab[(e['ps'][0], e['rs'][0])][2] for e in primes])
print(f'{len(primes)} primes with N <= {X}; max snap error {worst:.1e} ({time.time()-t0:.1f}s)', flush=True)
W3 = np.exp(2j * np.pi / 3)


def quad(ka, kb):
    v = (ka + kb * R) % P
    out = np.array([pow(int(x), int((p - 1) // 2), int(p)) if x else 0 for x, p in zip(v, P)], dtype=np.int64)
    return np.where(out == 0, 0, np.where(out == 1, 1, -1))


def cub(ka, kb):
    v = (ka + kb * R) % P
    out = np.zeros(len(P), dtype=complex)
    for i, (x, p, r) in enumerate(zip(v, P, R)):
        if x == 0:
            continue
        t = pow(int(x), int((p - 1) // 3), int(p))
        out[i] = 1 if t == 1 else (W3 if t == r % p else W3 * W3)
    return out


grid = [int(X * f) for f in (1/64, 1/32, 1/16, 1/8, 1/4, 1/2, 1)]
idx = [int(np.searchsorted(P, x, side='right')) for x in grid]


def report(name, vals):
    cs = np.cumsum(vals)
    T = [cs[i - 1] if i > 0 else 0 for i in idx]
    absT = np.abs(T)
    norm = [abs(t) / math.sqrt(i) if i else 0 for t, i in zip(T, idx)]
    sl = np.polyfit(np.log(grid[2:]), np.log(np.maximum(absT[2:], 1e-9)), 1)[0]
    return name, absT[-1], norm[-1], sl


rows = [report('T0 (k = 1)', G)]
ks = [e for e in ar.elems(1, KMAX)][::max(1, len(ar.elems(1, KMAX)) // NK)][:NK]
for e in ks:
    ka, kb, kn = e['a'], e['b'], e['N']
    q = quad(ka, kb); c = cub(ka, kb)
    rows.append(report(f'Tcub  k={ka}+{kb}w N={kn}', G * c))
    rows.append(report(f'Tcub2 k={ka}+{kb}w N={kn}', G * np.conj(c)))
    rows.append(report(f'Tquad k={ka}+{kb}w N={kn}', G * q))
    rows.append(report(f'Tsex  k={ka}+{kb}w N={kn}', G * q * np.conj(c)))
print(f'\n{"sum":34s} {"|T(X)|":>10s} {"|T|/sqrt(#pi)":>14s} {"slope dlog|T|/dlogX":>20s}')
for name, a, n_, s in rows:
    print(f'{name:34s} {a:10.1f} {n_:14.2f} {s:20.3f}')
print(f'\n#primes = {idx[-1]}; random-walk slope = 0.5 (in X, up to log); Patterson main term slope = 5/6 = 0.833')
print(f'done ({time.time()-t0:.1f}s)')
