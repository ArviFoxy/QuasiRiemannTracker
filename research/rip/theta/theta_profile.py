"""Theta span V of the sextic large sieve: where does the excess live, and what is left off it?

Matrix E[z, x] = chi_z(x) = prod_{pi | z} (x/pi)_6: rows z = squarefree ideals with N(z) in [B, 2B] coprime to 6 (the
moduli), columns x = primary elements with squarefree norm <= L (the sources).  Xu-Sang (arXiv 2610.17675) attain the
de Faveri excess with Gauss-sum vectors on the moduli side, c_z = conj G(z,1) * profile(N z / B): their Gram main term
is a rank-one form in the profile, proportional to I(U) = int U(t) t^{-5/6} dt.  This script measures, at the sizes we
can reach:
  * the dual energy ratio r(c) = ||E^T c||^2 / (S ||c||^2) of theta row vectors (random c gives 1; the Marchenko-
    Pastur edge is (sqrt R + sqrt S)^2 / S), with Gauss-sum conjugation/unit-twist variants;
  * the Gram of theta vectors across radial profiles (rank-one test against I(U));
  * the overlap of the theta direction with the top singular vectors of E;
  * the projections of detectors (plain sum, prime pool, random) onto the source-side theta direction E^T c / |.|;
  * the top singular value of E with the theta direction removed ("large sieve off V").
G(z,1) uses the Kubota character e(Tr(x/(sqrt(-3) z))) (ppcore 'canon'), extended to composite z by
G(c1 c2) = (c1/c2)_6 (c2/c1)_6 G(c1) G(c2).

usage: python3 -I theta_span.py B L
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'prime_pool'))
sys.path.insert(0, os.path.join(HERE, '..'))
import ppcore as pc          # noqa: E402
import zomega as zo          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
rng = np.random.default_rng(5)
t0 = time.time()
ID = pc.Ideals(max(2 * B, L) + 16)
rows = pc.enumerate_rows(B, ID)
R = rows['R']
# sources: primary elements with squarefree odd norm, coprime to 3, 1 < N <= L
SA, SB, SN = pc.primary_elements(L)
spf = ID.spf


def sqfree_int(n):
    while n > 1:
        p = int(spf[n]); n //= p
        if n % p == 0:
            return False
    return True


keep = np.array([(1 < n) and (n % 2 == 1) and (n % 3 != 0) and sqfree_int(int(n)) for n in SN])
SA, SB, SN = SA[keep], SB[keep], SN[keep]
S = len(SA)
uid = np.unique(rows['PID'][rows['PID'] >= 0])
T = pc.symbol_table(ID, uid, SA, SB)
LOC = pc.local_index(rows['PID'], uid)
E = pc.chi_chunk(LOC, T, 0, R).astype(np.complex128)
print('B=%d L=%d  R=%d rows  S=%d sources   built in %.1fs' % (B, L, R, S, time.time() - t0), flush=True)

# ---------------------------------------------------------------- Gauss sums of the moduli (rows)
gen_cache = {}


def generator(i):
    """primary generator (a, b) and a symbol function for prime ideal id i."""
    if i in gen_cache:
        return gen_cache[i]
    if i < ID.ns:
        p, r = ID.split_pr(np.array([i]))
        p = int(p[0]); r = int(r[0])
        a, b = pc.primary_generator(p, r)
        gs, gc = pc.gauss_sums(dict(p=p, r=r, a=a, b=b))
        val = dict(a=a, b=b, G=gc, prime=zo.Prime(p, (a, b)))
    else:
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        # inert Gauss sum over F_{q^2} with the Kubota character: Tr(x/(sqrt(-3) q)) = b_x / q
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                k = pr.sym((aa, bb))
                if k is None:
                    continue
                tot += np.exp(2j * np.pi * k / 6) * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    gen_cache[i] = val
    return val


def sym(prime, x):
    k = prime.sym((int(x[0]), int(x[1])))
    return None if k is None else np.exp(2j * np.pi * k / 6)


Grow = np.zeros(R, complex)
unit_tw = np.zeros((R, 6), complex)          # chi_z(u) for the six units u (twist variants)
for zi in range(R):
    ids = [int(i) for i in rows['PID'][zi] if i >= 0]
    gens = [generator(i) for i in ids]
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            s1 = sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b']))
            s2 = sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
            g *= s1 * s2
    Grow[zi] = g
    for k, u in enumerate(pc.UNITS):
        v = 1 + 0j
        for gi in gens:
            v *= sym(gi['prime'], u)
        unit_tw[zi, k] = v
print('  |G(z,1)|: min %.3f max %.3f   (built %.1fs)' % (np.abs(Grow).min(), np.abs(Grow).max(), time.time() - t0), flush=True)


# ---------------------------------------------------------------- profile test: is the theta excess rank one in the profile?
def ratio(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))
tN = rows['N'] / B
base = np.conj(Grow) * unit_tw[:, 0]
tt = np.linspace(1, 2, 4001)
def Ival(f):
    return np.trapezoid(f(tt) * tt ** (-5 / 6), tt)
# profile family on [1,2] (as functions of t = N/B); weights t^{-1/2} as in Xu-Sang
p_main = lambda t: t ** (-5 / 6)                      # the I-representer direction
p_lin = lambda t: (t - 1.5)                           # adjust to I = 0 below
alpha = Ival(p_lin) / Ival(lambda t: np.ones_like(t))
p_zero = lambda t: (t - 1.5) - alpha                  # I(p_zero) = 0
p_osc = lambda t: np.cos(2 * np.pi * (t - 1))
beta = Ival(p_osc) / Ival(lambda t: np.ones_like(t))
p_osc0 = lambda t: np.cos(2 * np.pi * (t - 1)) - beta # I = 0
print('I(p_zero) = %.2e, I(p_osc0) = %.2e' % (Ival(p_zero), Ival(p_osc0)))
for name, pf in (('t^-5/6 (I-direction)', p_main), ('flat', lambda t: np.ones_like(t)),
                 ('linear, I=0', p_zero), ('cosine, I=0', p_osc0)):
    w = pf(tN) * tN ** -0.5
    rt = ratio(base * w)
    rr = [ratio(np.exp(2j * np.pi * rng.random(R)) * w) for _ in range(20)]
    print('  profile %-22s theta r = %.3f   random-phase r = %.3f +- %.3f   excess %+.1f%% (%.1f sd)' %
          (name, rt, np.mean(rr), np.std(rr), 100 * (rt / np.mean(rr) - 1), (rt - np.mean(rr)) / np.std(rr)))
