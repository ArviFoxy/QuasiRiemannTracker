"""The reference wall's detector condition: do smooth x prime vectors see the theta past the square-root barrier?

Rows z with N(z) in [A, 2A], sources x up to L = A^{2/3} (past the square-root barrier L = A^{1/2}).  In this regime
one Poisson step writes the Gram as A I plus the Poisson spikes (twisted source thetas with twists up to L^2/A), so a
vector has a diagonal large sieve exactly when its correlations with those spikes are small (frontier, "Roadmap for
the faces").  The script prints |E v|^2 / |v|^2 divided by the same for the masked random matrix (mode 1, mean of
three seeds) for:
  * smooth x prime vectors v(x) = sum over x = s p of w(N s / X1) with p in a prime pool N(p) in [P0, 2 P0]
    (w = indicator of N s <= X1, or the bump (1 - N s/X1)), for several splits X1 * P0 ~ L;
  * the same support with random phases;
  * the prime pool alone, the smooth vector alone (all x with N x <= L), and the class-signed source theta;
and the normalized correlation |<v, f_m>|^2 / (|v|^2 |f_m|^2) * S of each vector with the twisted source thetas
f_m = f (x/m)^{+1}, N(m) <= Mtw (random level 1).

usage: python3 -I theta_reference_detector.py A [L] [Mtw] [threads]
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
theta = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign * SN ** (-1.0 / 3)
print('A=%d L=%d (A^%.2f, square-root barrier at %d): R=%d S=%d   (%.0fs)'
      % (A, L, math.log(L) / math.log(A), int(math.sqrt(A)), R, S, time.time() - t0), flush=True)
rng = np.random.default_rng(17)


def ratio(v):
    e = np.linalg.norm(K.forward(v[:, None], mode=0)[:, 0]) ** 2
    n = np.mean([np.linalg.norm(K.forward(v[:, None], mode=1, seed=s)[:, 0]) ** 2 for s in (3, 4, 5)])
    return e / n


# prime factor norms of each source (sources have squarefree norm)
pnorms = []
for n in Tb.SN:
    n = int(n); ps = []
    while n > 1:
        p = int(Tb.spf[n]); ps.append(p); n //= p
    pnorms.append(ps)
# twisted source thetas
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


vecs = []
for P0 in (8, 20, 50):
    X1 = L / (2 * P0)
    for wname in ('ind', 'bump'):
        v = np.zeros(S)
        for j, ps in enumerate(pnorms):
            for p in ps:
                if P0 <= p <= 2 * P0:
                    s = SN[j] / p
                    if s <= X1:
                        v[j] += 1.0 if wname == 'ind' else (1 - s / X1)
        vecs.append(('smooth x prime, P0=%d X1=%.0f %s' % (P0, X1, wname), v.astype(complex)))
        if wname == 'ind':
            vecs.append(('  same support, random phases', v * np.exp(2j * np.pi * rng.random(S))))
pool = np.array([1.0 if (len(ps) == 1 and 50 <= ps[0] <= L) else 0.0 for ps in pnorms])
vecs.append(('prime pool, 50 <= N(p) <= L', pool.astype(complex)))
vecs.append(('smooth: all x, weight 1', np.ones(S, complex)))
vecs.append(('smooth: all x, bump (1 - N x/L)', (1 - SN / L).astype(complex)))
vecs.append(('class-signed source theta', theta))
vecs.append(('random phases, all x', np.exp(2j * np.pi * rng.random(S))))
print('|E v|^2/|v|^2 over the masked null, and max / mean of S|<v, f_m>|^2/(|v|^2|f_m|^2) over %d twisted thetas '
      '(N(m) <= %d; random level 1):' % (len(tw), Mtw), flush=True)
for name, v in vecs:
    if np.linalg.norm(v) == 0:
        continue
    cm, ca = corr(v)
    print('  %-42s support %5d   ratio %.3f   corr max %7.2f mean %6.2f' % (name, int(np.sum(np.abs(v) > 0)),
                                                                          ratio(v), cm, ca), flush=True)
print('done in %.0fs' % (time.time() - t0))
