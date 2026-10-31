"""Task B4: restrictions of E to row / source subsets and what happens to the outlier.

For every variant (rows Rsub, sources Ssub) the script prints
  * the top singular value s^2/S' of the sextic submatrix and of a masked-random matrix of the same shape and zero pattern (one
    draw, two for the core set), and the excess (sextic / random - 1);
  * the prediction of the class-signed source-theta mechanism: the 12 class coefficients are REFITTED on the submatrix
    (compressed top eigenvalue lambda of Q^*(X^*X)Q/R' for the span of conj g~ N^-1/3 lam3 parsign restricted to Ssub); the value
    1 + bonus of a random-phase span with the same classes is subtracted, sigma^2 = (lambda - 1 - bonus) R'/v0 in units of the noise
    variance v0 (= fraction of nonzero entries, the mask), and the BBP outlier v0 (sigma^2 + R')(sigma^2 + S')/sigma^2 / S' is
    reported when sigma^2 > sqrt(R' S') (else the masked random edge).
The mechanism predicts: the spike is a flat rank-one component, so on a row subset of relative size r its strength falls like
sqrt(r) (no special role of lattice classes: the class-signed structure is refitted), on source subsets it falls with the mass
sum_x N^(-2/3) kept, and it needs the sources' Gauss-sum phases (class-signed conj g~).

usage: python3 -I theta_mech_restrict.py B L [core|full]          (set SCRATCH to a scratch directory)
"""
import os, sys, math, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '2')
import numpy as np
from scipy.sparse.linalg import svds

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_util as tu          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
which = sys.argv[3] if len(sys.argv) > 3 else 'full'
t0 = time.time()
A_ = tu.load_all(B, L, 8)
F, sd, rd, sc, R, S = A_.F, A_.sd, A_.rd, A_.sc, A_.R, A_.S
E = F.E
SN = F.SN.astype(float)
rng = np.random.default_rng(23)
base_full, _ = tu.class_signed_fit(A_, 1 / 3)
print('full matrix: top s^2/S %s' % np.round(A_.s[:3] ** 2 / S, 3), flush=True)


def top_sv(X, k=1):
    if min(X.shape) <= 400:
        return np.linalg.svd(X, compute_uv=False)[:k]
    s = svds(X, k=k, return_singular_vectors=False, random_state=0)
    return np.sort(s)[::-1]


def run(name, rows, cols, ndraw=1, core=False):
    if which != 'full' and not core:
        return
    X = E[np.ix_(rows, cols)]
    Rp, Sp = X.shape
    sx = top_sv(X, 2)
    edges = []
    mk = np.abs(X) > 0.5
    for _ in range(ndraw):
        Xr = mk * np.exp(2j * np.pi * rng.random(X.shape))
        edges.append(top_sv(Xr, 1)[0] ** 2 / Sp)
    edge = float(np.mean(edges))
    # refit the class-signed span on the submatrix
    base = base_full[cols]
    X12 = tu.class_span(sc['c4'][cols], base)
    keep = np.linalg.norm(X12, axis=0) > 1e-12
    X12 = X12[:, keep]
    if X12.shape[1] == 0:
        lam, bonus, pred = float('nan'), float('nan'), float('nan')
    else:
        Xn = X12 / np.linalg.norm(X12, axis=0, keepdims=True)
        XQ = X @ Xn
        M = XQ.conj().T @ XQ / Rp
        lam = np.linalg.eigvalsh((M + M.conj().T) / 2)[-1]
        # fit bonus: random-phase span with the same classes
        bo = []
        for _ in range(3):
            Xr12 = tu.class_span(sc['c4'][cols], np.exp(2j * np.pi * rng.random(len(cols))) * np.abs(base))
            Xr12 = Xr12[:, np.linalg.norm(Xr12, axis=0) > 1e-12]
            Xrn = Xr12 / np.linalg.norm(Xr12, axis=0, keepdims=True)
            XQr = X @ Xrn
            Mr = XQr.conj().T @ XQr / Rp
            bo.append(np.linalg.eigvalsh((Mr + Mr.conj().T) / 2)[-1])
        bonus = np.mean(bo) - 1.0
        v0 = mk.mean()                                   # noise variance per entry: the fraction of nonzero entries (the mask)
        sig2 = (lam - (bonus + 1.0)) * Rp / v0           # spike sigma^2 in units of the noise variance (lambda - random-span value)
        if sig2 > math.sqrt(Rp * Sp):
            pred = max(edge, v0 * (sig2 + Rp) * (sig2 + Sp) / sig2 / Sp)
        else:
            pred = edge
    print('  %-46s R\'=%5d S\'=%5d | sextic %.3f %.3f | random %.3f | excess %+6.1f%% | span lambda %.3f (bonus %.3f) -> predicted %.3f (%+6.1f%%)' %
          (name, Rp, Sp, sx[0] ** 2 / Sp, sx[1] ** 2 / Sp, edge, 100 * (sx[0] ** 2 / Sp / edge - 1), lam, bonus, pred, 100 * (pred / edge - 1)), flush=True)


allr = np.arange(R); alls = np.arange(S)
odd_r = rd['chim1'] < 0
c4r = rd['cls4']
big_c4 = np.bincount(c4r[c4r > 0]).argmax()
uc = rd['chim1'] * 3 + rd['chiw']
big_uc = np.bincount(uc - uc.min()).argmax() + uc.min()
odd_s = sc['odd']
print('\nrows restricted (all sources):')
run('all', allr, alls, 2, core=True)
run('prime rows (omega(z) = 1)', np.nonzero(rd['nprime'] == 1)[0], alls, 2, core=True)
run('composite rows (omega(z) >= 2)', np.nonzero(rd['nprime'] >= 2)[0], alls)
run('rows omega(z) = 2 only', np.nonzero(rd['nprime'] == 2)[0], alls)
run('rows with chi_z(-1) = +1 (6 classes mod 4)', np.nonzero(~odd_r)[0], alls, core=True)
run('rows with chi_z(-1) = -1 (6 classes mod 4)', np.nonzero(odd_r)[0], alls)
run('rows in one class mod 4 (largest)', np.nonzero(c4r == big_c4)[0], alls, core=True)
run('rows in one unit class (chi(-1), chi(w))', np.nonzero(uc == big_uc)[0], alls)
run('rows with even omega(z)', np.nonzero(rd['par'] == 0)[0], alls)
run('rows with odd omega(z)', np.nonzero(rd['par'] == 1)[0], alls)
for frac in (0.5, 0.25):
    run('random %.0f%% of the rows' % (100 * frac), np.sort(rng.choice(R, int(frac * R), replace=False)), alls, 2, core=(frac == 0.5))
run('rows N(z) in [B, 1.2B] (narrow window)', np.nonzero(F.rows['N'] <= 1.2 * B)[0], alls)

print('\nsources restricted (all rows):')
run('prime sources (omega(x) = 1)', allr, np.nonzero(sd['nprime'] == 1)[0], 2, core=True)
run('composite sources (omega(x) >= 2)', allr, np.nonzero(sd['nprime'] >= 2)[0])
run('sources with chi_x(-1) = +1', allr, np.nonzero(~odd_s)[0])
run('sources in one class mod 4', allr, np.nonzero(sc['c4'] == np.bincount(sc['c4']).argmax())[0])
run('sources with t = 0 only (n = 0 mod 3)', allr, np.nonzero(sc['t'] == 0)[0], core=True)
for X0 in (30, 100, 300, 1000, 3000):
    run('sources N(x) > %d' % X0, allr, np.nonzero(SN > X0)[0], core=(X0 == 300))
for X0 in (3000, 1000, 300):
    run('sources N(x) <= %d' % X0, allr, np.nonzero(SN <= X0)[0], core=(X0 == 1000))
for frac in (0.5, 0.25):
    run('random %.0f%% of the sources' % (100 * frac), allr, np.sort(rng.choice(S, int(frac * S), replace=False)), 2, core=(frac == 0.5))
run('prime rows x prime sources', np.nonzero(rd['nprime'] == 1)[0], np.nonzero(sd['nprime'] == 1)[0])
run('sources N(x) in (B/10, B]', allr, np.nonzero(SN > B / 10)[0])
print('\ndone in %.0fs' % (time.time() - t0))
