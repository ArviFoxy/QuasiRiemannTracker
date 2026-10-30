"""PROBE A (directions.md D2): fixed-index cross-correlations of the cubic-theta columns.

  S_K(k, P) = sum_n  g~(n) (n/k)_2 conj((n/P)_3) W( N(n) / (c K N(P)) ),
  G_{PP'}(K) = sum_{N(k) <= K}  S_K(k, P) conj S_K(k, P'),

over primary split-squarefree n (the columns of research/round7/signal-processing/build.py), rows k = primary
split-squarefree elements with 1 < N(k) <= K (the rows of build.py), P among the smallest primary split primes.
c = --cscale (default 1, the self-dual point N = K N(P)).

usage: python3 -I probeA.py OUT.npz [--kmax 20000] [--nprimes 10] [--w lin|sq|bump] [--gmode true|randphase|randcube]
                                    [--ngrid 14] [--kmin 250] [--seed 1] [--nrep 1] [--threads 4] [--cscale 1]
gmode:  true      exact Gauss sums g~ (the actual problem)
        randphase i.i.d. uniform unimodular phase per column (no arithmetic at all)
        randcube  random cube root of lambda(pi) at every prime (|g~| = 1, g~^3 = lambda and twisted
                  multiplicativity all kept; only the Heath-Brown--Patterson cube-root choice is randomised)
        randphasesym / randcubesym: the same with the exact symmetry g~(conj n) = conj g~(n) of the Gauss sums imposed
                  (this symmetry forces G_{P,Pbar} to be a sum of R/2 doubled terms: E|G_{P Pbar}|^2 = 2 R D_P D_Pbar)
With --nrep > 1 (surrogates only) the files OUT_r0.npz, OUT_r1.npz, ... are written (Phi is built once).
Each .npz holds, for every K of the grid: R, #columns, G (nP x nP), G over the dyadic block (K/2, K],
Dcross (the n = m 'diagonal' of the cross term, G^diag = R * Dcross) and the prime data.
"""
import sys, os, math, time, argparse
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import fastgauss as fg
from zw import Arith, quad_row, col_arrays, cubic_exp

ap = argparse.ArgumentParser()
ap.add_argument('out')
ap.add_argument('--kmax', type=int, default=20000)
ap.add_argument('--kmin', type=int, default=250)
ap.add_argument('--ngrid', type=int, default=14)
ap.add_argument('--nprimes', type=int, default=10)
ap.add_argument('--w', default='lin')
ap.add_argument('--gmode', default='true')
ap.add_argument('--seed', type=int, default=1)
ap.add_argument('--threads', type=int, default=4)
ap.add_argument('--cscale', type=float, default=1.0, help='window X = cscale * K * N(P)')
ap.add_argument('--nrep', type=int, default=1, help='replicas (surrogate modes only; Phi is shared)')
args = ap.parse_args()
T0 = time.time()


def log(*a):
    print(f'[{time.time()-T0:7.1f}s]', *a, flush=True)


def wfun(kind, u):
    u = np.asarray(u, dtype=float)
    out = np.zeros_like(u)
    m = u < 1.0
    if kind == 'lin':
        out[m] = 1.0 - u[m]
    elif kind == 'sq':
        out[m] = (1.0 - u[m]) ** 2
    elif kind == 'bump':
        out[m] = np.exp(1.0 - 1.0 / (1.0 - u[m] ** 2))
    else:
        raise ValueError(kind)
    return out


W3 = fg.W3

# ---------------------------------------------------------------- primes P
ar0 = Arith(1000)
Pall = sorted(ar0.elems(1, 900, primes_only=True), key=lambda e: (e['N'], e['a'], e['b']))
P = Pall[:args.nprimes]
Nmax_P = max(e['N'] for e in P)
KMAX = args.kmax
XMAX = int(args.cscale * KMAX * Nmax_P)
log(f'primes P (smallest {len(P)}):', [(e['N'], e['a'], e['b']) for e in P])
log(f'K_max={KMAX}, window X_max = cscale*K*N(P)_max = {XMAX}')

# ------------------------------------------------------- columns and rows
ar = Arith(max(XMAX, KMAX) + 10)
cols = ar.elems(1, XMAX)
rows = ar.elems(1, KMAX)
colN = np.array([c['N'] for c in cols]); rowN = np.array([r['N'] for r in rows])
log(f'columns (primary split-squarefree, 1 < N <= {XMAX}): {len(cols)};  rows (1 < N <= {KMAX}): {len(rows)}')
A, B = col_arrays(cols)

# ---------------------------------------------------------------- g~(n)
primes_cols = [c for c in cols if len(c['ps']) == 1]
ptab_true = None
if args.gmode in ('true', 'randcube', 'randcubesym'):
    ptab_true, worst = fg.prime_table(primes_cols, ar.spf, nthreads=args.threads, verbose=True)
    log(f'prime Gauss sums done (max snap {worst:.1e})')


def conj_partner_index():
    """index of the conjugate column (a + b w -> (a - b) - b w) for every column."""
    pos = {(int(c['a']), int(c['b'])): i for i, c in enumerate(cols)}
    return np.array([pos[(int(c['a']) - int(c['b']), -int(c['b']))] for c in cols])


def make_gt(rep):
    """g~ vector for the chosen mode (replica rep for the surrogates).
    true        exact Gauss sums
    randphase   i.i.d. phases                        randphasesym   same with theta(conj n) = -theta(n)
    randcube    random cube roots at the primes      randcubesym    same with g~(conj pi) = conj g~(pi)
    (the 'sym' versions keep the exact symmetry g~(conj n) = conj g~(n) of the Gauss sums)"""
    rr = np.random.default_rng(args.seed + 1000 * rep)
    if args.gmode == 'true':
        return fg.gt_array(cols, ptab_true)
    if args.gmode in ('randcube', 'randcubesym'):
        ptab2 = {}
        for key, (a, b, g) in ptab_true.items():
            if key in ptab2:
                continue
            p, r = key
            lam = fg.lam_of(a, b)
            base = np.angle(lam) / 3.0
            j = int(rr.integers(0, 3))
            val = np.exp(1j * (base + 2 * np.pi * j / 3.0))
            ptab2[key] = (a, b, val)
            if args.gmode == 'randcubesym':
                pk = (p, (r * r) % p)
                if pk != key and pk in ptab_true:
                    ptab2[pk] = (ptab_true[pk][0], ptab_true[pk][1], np.conj(val))
        for key, (a, b, g) in ptab_true.items():       # non-sym mode: independent draws for the remaining keys
            if key not in ptab2:
                lam = fg.lam_of(a, b)
                ptab2[key] = (a, b, np.exp(1j * (np.angle(lam) / 3.0 + 2 * np.pi * int(rr.integers(0, 3)) / 3.0)))
        return fg.gt_array(cols, ptab2)
    if args.gmode in ('randphase', 'randphasesym'):
        th = np.exp(2j * np.pi * rr.random(len(cols)))
        if args.gmode == 'randphasesym':
            cp = conj_partner_index()
            idx = np.arange(len(cols))
            keep = idx < cp
            th2 = th.copy()
            th2[cp[keep]] = np.conj(th[keep])
            th = th2
        return th
    raise ValueError(args.gmode)


# ------------------------------------------------- cubic slot symbols (n/P)_3
nP = len(P)
Xe = np.zeros((len(cols), nP), dtype=np.int8)
for j, Pj in enumerate(P):
    Xe[:, j] = cubic_exp(ar, A, B, Pj)
chi_conj = np.where(Xe < 0, 0, np.conj(W3 ** np.where(Xe < 0, 0, Xe).astype(np.int64)))   # conj((n/P)_3), 0 if P | n

# ------------------------------------------------------------ Phi (rows x columns), int8
t1 = time.time()
Phi = np.empty((len(rows), len(cols)), dtype=np.int8)
for i, k in enumerate(rows):
    Phi[i] = quad_row(ar, A, B, k)
log(f'Phi {Phi.shape} built in {time.time()-t1:.1f}s ({Phi.nbytes/1e6:.0f} MB)')

# ----------------------------------------------------------------- K grid
Kgrid = np.unique(np.round(np.geomspace(args.kmin, KMAX, args.ngrid)).astype(int))
NPm = np.array([e['N'] for e in P], dtype=float)
CH = 8192


def run_one(gt, outfn, verbose=True):
    res = dict(K=[], R=[], Rhalf=[], ncol=[], G=[], Ghalf=[], Dcross=[], ncolP=[])
    for K in Kgrid:
        R = int(np.searchsorted(rowN, K, side='right'))
        Rh = int(np.searchsorted(rowN, K // 2, side='right'))
        nc = int(np.searchsorted(colN, args.cscale * K * Nmax_P, side='right'))
        # weighted column vectors C[n, P] = g~(n) conj((n/P)_3) W(N(n)/(c K N(P)))
        u = colN[:nc, None] / (args.cscale * K * NPm[None, :])
        Wm = wfun(args.w, u)
        C = gt[:nc, None] * chi_conj[:nc] * Wm
        S = np.zeros((R, nP), dtype=complex)
        for j0 in range(0, nc, CH):                      # S = Phi[:R, :nc] @ C in column chunks (float64)
            j1 = min(nc, j0 + CH)
            Aj = Phi[:R, j0:j1].astype(np.float64)
            S += Aj @ C[j0:j1].real + 1j * (Aj @ C[j0:j1].imag)
        G = S.T @ S.conj()                               # G[P,P'] = sum_k S[k,P] conj S[k,P']
        Gh = S[Rh:].T @ S[Rh:].conj()                    # same over the dyadic block K/2 < N(k) <= K
        # n = m 'diagonal' of the cross term:  sum_n |g~|^2 conj chi_P chi_P' W_P W_P'   (G^diag = R * Dcross)
        Cn = chi_conj[:nc] * Wm
        Dcross = Cn.T @ Cn.conj()
        res['K'].append(int(K)); res['R'].append(R); res['Rhalf'].append(R - Rh); res['ncol'].append(nc)
        res['G'].append(G); res['Ghalf'].append(Gh); res['Dcross'].append(Dcross)
        res['ncolP'].append(np.sum(Wm > 0, axis=0))
        if verbose:
            dg = np.real(np.diag(G)); dd = R * np.real(np.diag(Dcross))
            iu = np.triu_indices(nP, 1)
            rho = np.abs(G[iu]) / np.sqrt(dg[iu[0]] * dg[iu[1]])
            log(f'K={K:6d} R={R:5d} cols={nc:7d}  G_PP/(R D_P): mean {np.mean(dg/dd):.3f} [{np.min(dg/dd):.3f},{np.max(dg/dd):.3f}]'
                f'   rho mean {rho.mean():.4f} rms*sqrt(R) {math.sqrt(np.mean(rho**2))*math.sqrt(R):.3f}')
    np.savez_compressed(outfn, K=np.array(res['K']), R=np.array(res['R']), Rhalf=np.array(res['Rhalf']),
                        ncol=np.array(res['ncol']), G=np.array(res['G']), Ghalf=np.array(res['Ghalf']),
                        Dcross=np.array(res['Dcross']), ncolP=np.array(res['ncolP']),
                        PN=np.array([e['N'] for e in P]), Pa=np.array([e['a'] for e in P]),
                        Pb=np.array([e['b'] for e in P]), meta=np.array(str(vars(args))))
    log('saved', outfn)


if args.gmode == 'true' or args.nrep == 1:
    run_one(make_gt(0), args.out)
else:
    base = args.out[:-4] if args.out.endswith('.npz') else args.out
    for rep in range(args.nrep):
        run_one(make_gt(rep), f'{base}_r{rep}.npz', verbose=(rep == 0))
