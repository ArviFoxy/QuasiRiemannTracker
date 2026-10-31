"""Prime dilation: the Gauss-sum vector convolved with a prime pool loses its spike alignment.

Rows N(z) in [A, 2A], sources x of squarefree norm N(x) <= L.  Vectors (unit-modulus coefficients):
  * gauss: alpha(x) = conj g~(x) * (class sign), the spike direction itself, on all x;
  * gauss restricted to N(x) <= X1 (the long factor alone);
  * gauss * pool: lambda(x) = sum over x = s p of alpha(s) a(p), p in a prime pool N(p) in [P0, 2 P0], N(s) <= X1,
    with a = 1 or a(p) = conj g~(p);
  * the same supports with random phases.
For each it prints |E v|^2/|v|^2 over the masked null (mode 1, mean of three seeds) and the normalized correlation
S |<v, f_m>|^2 / (|v|^2 |f_m|^2) with the twisted source thetas f_m, N(m) <= Mtw (max and mean; random level 1).

Prediction (journal 2026-10-31, "The reference wall needs no metaplectic input"): by twisted multiplicativity
<alpha * a, f_m> = sum_{s,p} u_s v_p (p/s)_6^{-2} * (class sign), a bilinear form, so the convolutions sit at the
random level in both columns although the long factor alone is the spike.

usage: python3 -I theta_prime_dilation.py A [L] [Mtw] [threads]
"""
import os, sys, time, math
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402
import theta_util as tu          # noqa: E402

A = int(sys.argv[1])
L = int(sys.argv[2]) if len(sys.argv) > 2 else int(round(A ** (2.0 / 3)))
Mtw = int(sys.argv[3]) if len(sys.argv) > 3 else 60
nth = int(sys.argv[4]) if len(sys.argv) > 4 else 2
t0 = time.time()
Tb = tc.build_tables(A, L, verbose=False)
R, S = Tb.R, Tb.S
Ff = tu.free_namespace(Tb)
sd = tu.source_data(Ff)
Gsrc, utw, nprime = sd['Gsrc'], sd['utw'], sd['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SN = Tb.SN.astype(float)
parsign = np.where((utw[:, 3].real < 0) & (nprime % 2 == 1), -1.0, 1.0)
gauss = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign
theta = gauss * SN ** (-1.0 / 3)
print('A=%d L=%d (A^%.2f, square-root barrier at %d): R=%d S=%d, |gauss| in [%.3f, %.3f]   (%.0fs)'
      % (A, L, math.log(L) / math.log(A), int(math.sqrt(A)), R, S, np.abs(gauss).min(), np.abs(gauss).max(),
         time.time() - t0), flush=True)
rng = np.random.default_rng(23)


def ratio(v):
    e = np.linalg.norm(K.forward(v[:, None], mode=0)[:, 0]) ** 2
    n = np.mean([np.linalg.norm(K.forward(v[:, None], mode=1, seed=s)[:, 0]) ** 2 for s in (3, 4, 5)])
    return e / n


# prime-ideal ids of every source, and the index of each id set
ids_of = [tuple(sorted(tu.source_prime_ids(Ff, Tb.SA[j], Tb.SB[j], Tb.SN[j]))) for j in range(S)]
index = {frozenset(t): j for j, t in enumerate(ids_of)}
pnorm = {}
for j, t in enumerate(ids_of):
    if len(t) == 1:
        pnorm[t[0]] = int(Tb.SN[j])

# twisted source thetas (as in theta_reference_detector.py)
uid = Tb.uid
order = np.argsort(SN, kind='stable')
tw = []
for j in order:
    if SN[j] > Mtw:
        break
    ids = tu.source_prime_ids(Ff, Tb.SA[j], Tb.SB[j], Tb.SN[j])
    pos = np.searchsorted(uid, ids)
    if not (np.all(pos < len(uid)) and np.all(uid[pos] == ids)):
        continue
    codes = np.zeros(S, np.int64); zero = np.zeros(S, bool)
    for p_ in pos:
        r = Tb.T[p_].astype(np.int64); zero |= (r & 0x40) != 0; codes += r & 7
    tw.append((int(SN[j]), theta * np.where(zero, 0, np.exp(2j * np.pi * (codes % 6) / 6))))
Fm = np.stack([f / np.linalg.norm(f) for _, f in tw], axis=1)


def corr(v):
    c = np.abs(Fm.conj().T @ (v / np.linalg.norm(v))) ** 2 * S
    return c.max(), c.mean()


def dilate(alpha, P0, X1, twist):
    """lambda(x) = sum over x = s p, p in the pool, N(s) <= X1, of alpha(s) a(p)."""
    lam = np.zeros(S, complex)
    for j, t in enumerate(ids_of):
        for i in t:
            p = pnorm.get(i)
            if p is None or not (P0 <= p <= 2 * P0) or SN[j] / p > X1 or len(t) < 2:
                continue
            js = index.get(frozenset(t) - {i})
            if js is None:
                continue
            ap = np.conj(gauss[index[frozenset((i,))]]) if twist else 1.0
            lam[j] += alpha[js] * ap
    return lam


vecs = [('gauss, all x', gauss.astype(complex)),
        ('theta (gauss * N^-1/3), all x', theta.astype(complex)),
        ('random phases, all x', np.exp(2j * np.pi * rng.random(S)))]
for P0 in (8, 20, 50):
    X1 = L / (2 * P0)
    short = np.where(SN <= X1, gauss, 0).astype(complex)
    vecs.append(('gauss restricted to N <= X1 = %.0f' % X1, short))
    for twist in (False, True):
        lam = dilate(gauss, P0, X1, twist)
        vecs.append(('gauss * pool[%d, %d], a = %s' % (P0, 2 * P0, 'conj g~(p)' if twist else '1'), lam))
    vecs.append(('  same support, random phases', np.where(np.abs(lam) > 0, np.exp(2j * np.pi * rng.random(S)), 0)))
    vecs.append(('  same support, gauss phases (no dilation)', np.where(np.abs(lam) > 0, gauss, 0).astype(complex)))
# a broad pool: most sources have a prime factor in [7, Pmax]
for Pmax in (100, 400):
    lam = np.zeros(S, complex)
    for j, t in enumerate(ids_of):
        if len(t) < 2:
            continue
        for i in t:
            p = pnorm.get(i)
            if p is None or p > Pmax:
                continue
            js = index.get(frozenset(t) - {i})
            if js is not None:
                lam[j] += gauss[js]
    vecs.append(('gauss * pool[7, %d], a = 1, no length cap' % Pmax, lam))
    vecs.append(('  same support, random phases', np.where(np.abs(lam) > 0, np.exp(2j * np.pi * rng.random(S)), 0)))
    vecs.append(('  same support, gauss phases (no dilation)', np.where(np.abs(lam) > 0, gauss, 0).astype(complex)))
print('|E v|^2/|v|^2 over the masked null, and max / mean of S|<v, f_m>|^2/(|v|^2|f_m|^2) over %d twisted thetas '
      '(N(m) <= %d; random level 1):' % (len(tw), Mtw), flush=True)
for name, v in vecs:
    if np.linalg.norm(v) == 0:
        print('  %-44s empty' % name)
        continue
    cm, ca = corr(v)
    print('  %-44s support %5d   ratio %.3f   corr max %8.2f mean %7.2f' % (name, int(np.sum(np.abs(v) > 0)),
                                                                           ratio(v), cm, ca), flush=True)
print('done in %.0fs' % (time.time() - t0))
