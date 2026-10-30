"""Direct check of the functional equation (Poisson summation over Z[w]) for single rows, with the 3-part of the conductor.

For primary n, chi_u(n) = chi_u(-1) Phi(n) with Phi(x) = chi_u(d_x x), d_x the unit with d_x x = 1 mod 3; Phi is a character
mod 3u, trivial on units, with conductor f = u (k = 0), (1 - w) u (k = 3), 3u (k in {1,2,4,5}),  k = ((N(u) - 1)/6) mod 6.
Poisson summation over the lattice Z[w] (trace pairing, dual lattice f^-1 d^-1, d = (sqrt -3)) gives, with
  Gh(rho) = pi * int_0^inf w(t) J0(2 pi rho sqrt t) dt   (2-D Fourier transform of x -> w(|x|^2)),
  c >= 1:  |S_u(N)| = 2N/sqrt(3 Nf) * | sum_{n primary} conj chi_u(n) Gh(2 sqrt(N N(n) / (3 Nf))) |,       Nf = 3^c N(u)
  c  = 0:  |S_u(N)| = 2N/(3 sqrt(3 N(u))) * | sum_n conj chi_u(n) [2 sum_{j>=0} lam^-j g_j(n) - lam g_{-1}(n)] |,
           g_j(n) = Gh(2 sqrt(N 3^j N(n) / (3 N(u)))),  lam = chi_u(1 - w)
(the c = 0 sum is imprimitive at 1 - w: S = (T(N) - lam T(N/3))/6 with T the full lattice sum).
The script compares the two sides for chosen rows and N, and prints the dual mass profile (where the dual sum lives).
usage: python3 -I primerows_dual.py --B 30000 --m 0.4 0.5 0.6 0.7 --nrows 3
"""
import sys, os, math, time, argparse
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import j0
import probeB as PB
import primerows_core as PC

SIG = PC.SIG


class Ghat:
    """Gh(rho) on a grid (rho <= rmax), linear interpolation; w smooth (log-normal, cut at |log t| = 1) or sharp [1,2)."""

    def __init__(self, kind='smooth', rmax=40.0, drho=0.0025, ns=40001):
        self.kind = kind
        if kind == 'smooth':
            s = np.linspace(-1.0, 1.0, ns)
            f = np.exp(-s ** 2 / (2 * SIG ** 2)) * np.exp(s)
            sq = np.exp(s / 2)
        else:
            s = np.linspace(0.0, math.log(2.0), ns)
            f = np.exp(s); sq = np.exp(s / 2)
        wq = np.full(ns, s[1] - s[0]); wq[0] *= 0.5; wq[-1] *= 0.5
        self.rho = np.arange(0.0, rmax + drho, drho)
        out = np.empty(len(self.rho))
        for i0 in range(0, len(self.rho), 200):
            r = self.rho[i0:i0 + 200]
            out[i0:i0 + 200] = math.pi * (j0(2 * math.pi * r[:, None] * sq[None, :]) * (f * wq)[None, :]).sum(1)
        self.val = out
        self.rmax = rmax

    def __call__(self, r):
        r = np.asarray(r, dtype=np.float64)
        v = np.interp(r, self.rho, self.val)
        v[r > self.rmax] = 0.0
        return v


def chi_exp(PI, fac, A, B):
    """exponent of chi_u(A + B w) (sum over the factors), and the zero mask."""
    E, Z = PB.sextic_table(PC.subPI(PI, np.array(fac)), A, B)
    return E.astype(np.int64).sum(0) % 6, Z.any(0)


def chi_val(PI, fac, A, B):
    e, z = chi_exp(PI, fac, A, B)
    return np.where(z, 0, np.exp(2j * np.pi * e / 6))


def direct(PI, fac, N, kind):
    lo, hi = PC.support(kind)
    A, Bb, NN = PB.primary_window(int(math.floor(N * lo)), int(math.ceil(N * hi)) + 1)
    w = PC.weight(NN / N, kind)
    return np.sum(chi_val(PI, fac, A, Bb) * w), np.sum(w ** 2)


def dual(PI, fac, Nu, k, N, gh, want_profile=False):
    rmax = gh.rmax
    if k == 0:
        Nf = Nu
        X = rmax ** 2 * 9 * Nf / (4 * N)                  # g_{-1} has the longest reach
    else:
        Nf = Nu * (3 if k == 3 else 9)
        X = rmax ** 2 * 3 * Nf / (4 * N)
    A, Bb, NN = PB.primary_window(1, int(X) + 2)
    cv = np.conj(chi_val(PI, fac, A, Bb))
    if k != 0:
        H = gh(2 * np.sqrt(N * NN / (3.0 * Nf)))
        val = 2 * N / math.sqrt(3 * Nf) * np.sum(cv * H)
    else:
        lam = chi_val(PI, fac, np.array([1]), np.array([-1]))[0]     # chi_u(1 - w)
        H = -lam * gh(2 * np.sqrt(N * NN / (9.0 * Nu))).astype(np.complex128)
        j = 0
        while True:
            arg = 2 * np.sqrt(N * (3.0 ** j) * NN / (3.0 * Nu))
            if arg.min() > rmax:
                break
            H += 2 * np.conj(lam) ** j * gh(arg)
            j += 1
        val = 2 * N / (3 * math.sqrt(3 * Nu)) * np.sum(cv * H)
    prof = None
    if want_profile:
        # where the dual mass lives: quantiles of N(n) under |H|^2
        mm = np.abs(H) ** 2
        c = np.cumsum(mm) / mm.sum()
        prof = [float(NN[np.searchsorted(c, q)]) for q in (0.1, 0.5, 0.9)]
    return val, prof, len(NN)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, default=30000)
    ap.add_argument('--m', type=float, nargs='+', default=[0.4, 0.5, 0.6, 0.7])
    ap.add_argument('--nrows', type=int, default=2)
    ap.add_argument('--weight', default='smooth')
    ap.add_argument('--rmax', type=float, default=40.0)
    ap.add_argument('--seed', type=int, default=3)
    a = ap.parse_args()
    t0 = time.time()
    gh = Ghat(a.weight, rmax=a.rmax)
    print(f'Gh table ({time.time()-t0:.1f}s): Gh(0) = {gh.val[0]:.5f} (= pi int w = {math.pi*np.trapezoid(PC.weight(np.exp(np.linspace(-1,1,200001)), "smooth")*np.exp(np.linspace(-1,1,200001)), np.linspace(-1,1,200001)):.5f}),'
          f' |Gh| at rho = 1, 2, 5, 10, 20: ' + ', '.join(f'{abs(v):.2e}' for v in gh(np.array([1, 2, 5, 10, 20.]))))
    B = a.B
    ar = PB.Arith(2 * B + 10)
    PI = PB.prime_ideals(ar, 2 * B)
    rows = PB.build_rows(PI['norm'], B, 2 * B)
    rng = np.random.default_rng(a.seed)
    picks = []
    for cls in ('prime', 'composite'):
        for kk in (0, 3, 1, 2, 4, 5):
            cand = [r for r in rows if (len(r) == 1) == (cls == 'prime') and ((int(np.prod([int(PI['norm'][j]) for j in r])) - 1) // 6) % 6 == kk
                    and all(PI['kind'][j] == 0 for j in r)]
            for i in rng.choice(len(cand), size=min(a.nrows if kk in (0, 3, 1) else 1, len(cand)), replace=False):
                picks.append((cls, kk, cand[i]))
    print(' class      k  N(u)      factors(norms)            m     N        |S| direct      |S| dual      rel.diff   dual terms   dual mass quantiles N(n) 10/50/90%')
    for cls, kk, r in picks:
        Nu = int(np.prod([int(PI['norm'][j]) for j in r]))
        for m in a.m:
            N = B ** m
            s, mass = direct(PI, list(r), N, a.weight)
            dv, prof, nt = dual(PI, list(r), Nu, kk, N, gh, want_profile=True)
            print(f' {cls:9s} {kk}  {Nu:7d}  {str([int(PI["norm"][j]) for j in r]):24s}  {m:.2f} {N:8.1f}  {abs(s):12.5f}  {abs(dv):12.5f}   {abs(abs(s)-abs(dv))/max(abs(s),1e-12):.1e}   {nt:8d}   '
                  + ' / '.join(f'{q:.0f}' for q in prof), flush=True)
    print(f'done ({time.time()-t0:.1f}s)')
