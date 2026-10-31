"""Task B2: source side of the top singular pair of E = [chi_z(x)] (rows z, sources x), B = L.

For the top right singular vectors v_k (E^* u_k = s_k v_k) the script reports
  1. the radial profile S|v|^2 in bins of N(x) (random = 1), a fit S|v0|^2 ~ a N^-p + b, and the same profile for the top vector of
     a masked-random matrix (E's zero pattern, random phases) as the null;
  2. global overlaps |<v, f>|/|f| (random level 1/sqrt(S)) with: conj g~, g~, conj g~ * chi_x(u) (six units), mu(x) = (-1)^omega(x),
     omega(x) (centred), the prime indicator (centred), and the energy of v in the span of the 12 class indicators mod 4;
  3. class-wise coherence |sum_{x in class, range} v(x) g~(x)| / (sqrt(n) rms|v|) for the 12 classes mod 4 and three norm ranges
     (this is where the conjugate source theta shows up: it is invisible in the global overlap because the class phases differ);
  4. the overlap of v_k restricted to norm ranges with the class-signed model f (12 fitted class phases, lam3 = omega^-n,
     parsign, alpha = 1/3) -- in which N(x) range does v0 follow the model;
  5. the dependence of |v0|^2 and |f|^2 on omega(x) (primes versus composites).

usage: python3 -I theta_mech_src.py B L          (set SCRATCH to a scratch directory; top singular triples are cached there)
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
t0 = time.time()
A_ = tu.load_all(B, L, 8)
F, sd, sc, s, U, Vh, R, S = A_.F, A_.sd, A_.sc, A_.s, A_.U, A_.Vh, A_.R, A_.S
E = F.E
SN = F.SN.astype(float); Gs = sd['Gsrc']
rng = np.random.default_rng(11)
print('top s^2/S: %s' % np.round(s[:6] ** 2 / S, 3), flush=True)
V = [Vh[k].conj() for k in range(4)]
edges = np.array([1, 10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000, 1e9])
edges = edges[edges <= max(L, 10) * 10]

# null: top right singular vector of a masked-random matrix
mask = np.abs(E) > 0.5
Er = mask * np.exp(2j * np.pi * rng.random(E.shape))
_, sr, Vhr = svds(Er, k=2, random_state=0)
o = np.argsort(-sr); sr = sr[o]; Vhr = Vhr[o]
vr = Vhr[0].conj()
del Er
print('masked-random top s^2/S: %s' % np.round(sr ** 2 / S, 3), flush=True)


def binned(v):
    out = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        m = (SN > lo) & (SN <= hi)
        if m.sum():
            out.append((lo, hi, m.sum(), np.mean(np.abs(v[m]) ** 2) * S))
    return out


print('\n1. radial profile S|v|^2 by N(x) bin  [count]')
pb = {k: binned(V[k]) for k in range(3)}
pbr = binned(vr)
for i, (lo, hi, n, _) in enumerate(pb[0]):
    print('   N in (%6g, %6g]  [%5d]   v0 %6.2f   v1 %6.2f   v2 %6.2f   masked-random top %6.2f' %
          (lo, hi, n, pb[0][i][3], pb[1][i][3], pb[2][i][3], pbr[i][3]))
xs = np.array([np.mean(SN[(SN > lo) & (SN <= hi)]) for lo, hi, n, _ in pb[0]]); cnts = np.array([n for _, _, n, _ in pb[0]], float)
print('   regression of the binned profile on b + a N^-p (weights = counts): residual rms (relative) for p in {1/4, 1/2, 2/3, 1, 3/2} -> the exponent 2*alpha of |f|^2 ~ N^-2alpha')
for k in range(2):
    ys = np.array([b_[3] for b_ in pb[k]])
    out = []
    for pexp in (0.25, 0.5, 2 / 3, 1.0, 1.5):
        Xr_ = np.vstack([np.ones_like(xs), xs ** (-pexp)]).T * np.sqrt(cnts)[:, None]
        coef_, *_ = np.linalg.lstsq(Xr_, ys * np.sqrt(cnts), rcond=None)
        res = ys - (coef_[0] + coef_[1] * xs ** (-pexp))
        out.append('p=%.2f: a=%.1f b=%.2f rms %.3f' % (pexp, coef_[1], coef_[0], math.sqrt(np.sum(cnts * res ** 2) / cnts.sum())))
    print('   v%d : %s' % (k, ' | '.join(out)))

print('\n2. global overlaps |<v, f>|/|f|  (random level 1/sqrt(S) = %.3f ; rms of the null over 10 random f: see last column)' % (1 / math.sqrt(S)))
om = sd['nprime'].astype(float)
fl = [('conj g~', np.conj(Gs)), ('g~', Gs)]
for k in range(6):
    fl.append(('conj g~ chi(u%d)' % k, np.conj(Gs) * sd['utw'][:, k]))
for k in range(1, 6):
    fl.append(('chi_x(u%d) (plain unit twist)' % k, sd['utw'][:, k]))
chi3 = np.array([np.prod([F.sym(gi['prime'], (3, 0)) for gi in sd['primes'][j]]) for j in range(S)])
lam3_ = tu.lam3(F, 0, -1)
fl.append(('chi_x(3)^2 = (3/x)_3', chi3 ** 2))
fl += [('mu = (-1)^omega', sd['mu'] + 0j), ('omega - mean', om - om.mean() + 0j), ('prime indicator - mean', (om == 1) - np.mean(om == 1) + 0j),
       ('N^-1/2', SN ** -0.5 + 0j), ('log N - mean', np.log(SN) - np.log(SN).mean() + 0j)]
print('   identification: lam3(x) = omega^(-n) equals chi_x(3)^2 = (3/x)_3 exactly: max deviation %.1e ; chi_x(3)^3 = chi_x(-1): %s' % (np.max(np.abs(lam3_ - chi3 ** 2)), bool(np.all(np.rint(np.real(chi3 ** 3)) == np.rint(sd['utw'][:, 3].real)))))
print('   %-30s %s' % ('f', 'v0     v1     v2     v3   | null top'))
for name, f in fl:
    fn = f / np.linalg.norm(f)
    print('   %-30s %.3f  %.3f  %.3f  %.3f | %.3f' % (name, *[abs(np.vdot(fn, V[k])) for k in range(4)], abs(np.vdot(fn, vr))))
cl = sc['c4']
X = tu.class_span(cl, np.ones(S, complex)); Xn = X / np.linalg.norm(X, axis=0, keepdims=True)
print('   energy in span of the %d class indicators mod 4 : v0 %.4f v1 %.4f v2 %.4f ; null %.4f ; random %.4f' %
      (Xn.shape[1], *[np.linalg.norm(Xn.conj().T @ V[k]) ** 2 for k in range(3)], np.linalg.norm(Xn.conj().T @ vr) ** 2, Xn.shape[1] / S))

print('\n3. coherence |sum v g|/(sqrt(n) rms|v|) over cells (class mod 4) x (norm range): v ~ conj g~  [first: no further twist; second: cells refined by the cubic class t = n mod 3 with parsign]')
ranges = [(0, 300), (300, 3000), (3000, 1e9)]
if L >= 20000:
    ranges = [(0, 1000), (1000, 10000), (10000, 1e9)]
tt = sc['t']; psg = sc['parsign']
for label, cellid, twist in (('class mod 4 only', cl * 3, np.ones(S)), ('class mod 4 x t, with parsign', cl * 3 + tt, psg)):
    for conj_ in (True, False):
        cells = []
        for c in sorted(set(cellid.tolist())):
            for lo, hi in ranges:
                m = (cellid == c) & (SN > lo) & (SN <= hi)
                n = m.sum()
                if n < 5:
                    continue
                rms = math.sqrt(np.mean(np.abs(V[0][m]) ** 2))
                g = (Gs[m] if conj_ else np.conj(Gs[m])) * twist[m]
                cells.append(abs(np.sum(V[0][m] * g)) / (math.sqrt(n) * rms))
        cells = np.array(cells)
        print('   %-30s v0 ~ %-7s : %2d cells, mean coherence %.2f (pure noise 0.89), cells > 2.5: %d (noise: %.1f), > 4: %d, max %.2f' %
              (label, 'conj g~' if conj_ else 'g~', len(cells), cells.mean(), (cells > 2.5).sum(), len(cells) * math.exp(-2.5 ** 2 / 1.0), (cells > 4).sum(), cells.max()))
print('   NOTE: within a cell the model also needs a constant class phase; the coherence |sum| is insensitive to it.')
print('   per-cell detail (class mod 4 x t, parsign, conj g~), rows = class (a,b) mod 4, columns = t = 0,1,2 for the three norm ranges:')
for c in sorted(set(cl.tolist())):
    row = []
    for lo, hi in ranges:
        for t_ in range(3):
            m = (cl == c) & (tt == t_) & (SN > lo) & (SN <= hi)
            n = m.sum()
            if n < 5:
                row.append(' -  '); continue
            rms = math.sqrt(np.mean(np.abs(V[0][m]) ** 2))
            row.append('%4.1f' % (abs(np.sum(V[0][m] * Gs[m] * psg[m])) / (math.sqrt(n) * rms)))
        row.append('|')
    print('     (%d,%d): %s' % (c // 4, c % 4, ' '.join(row)))

print('\n4. in which norm range does v follow the class-signed model f? (f = conj g~ N^-1/3 lam3 parsign, 12 fitted class coefficients)')
base, Xn = tu.class_signed_fit(A_, 1 / 3)
M = tu.compressed(F, Xn, 'src')
w, Vv = tu.top_eig(M, 1)
f = Xn @ Vv[:, 0]
print('   compressed top s^2/R = %.3f ; |<f, v0>| = %.3f ; energy of v0 in the 12-dim span %.3f' % (w[0], abs(np.vdot(f, V[0])), np.linalg.norm(Xn.conj().T @ V[0]) ** 2))
for lo, hi, n, _ in pb[0]:
    m = (SN > lo) & (SN <= hi)
    if m.sum() < 8:
        continue
    fm, vm = f[m], V[0][m]
    c = abs(np.vdot(fm, vm)) / (np.linalg.norm(fm) * np.linalg.norm(vm))
    cr = abs(np.vdot(fm, V[1][m])) / (np.linalg.norm(fm) * np.linalg.norm(V[1][m]))
    print('   N in (%6g, %6g]  n = %5d : cos(v0, f) = %.3f   cos(v1, f) = %.3f   (random level %.3f)   mass of v0 %.3f  mass of f %.3f' %
          (lo, hi, m.sum(), c, cr, 1 / math.sqrt(m.sum()), np.linalg.norm(vm) ** 2, np.linalg.norm(fm) ** 2))

print('\n5. omega(x) dependence: mean S|v|^2 for v0, the null, and the model f (normalised to unit norm), by omega(x) within three norm ranges')
fn_ = f / np.linalg.norm(f)
for lo, hi in ((0, 300), (300, 3000), (3000, 1e9)):
    parts = []
    for w_ in (1, 2, 3):
        m = (sd['nprime'] == w_) & (SN > lo) & (SN <= hi)
        if m.sum() >= 5:
            parts.append('omega=%d [%4d]: v0 %.2f null %.2f f %.2f' % (w_, m.sum(), np.mean(np.abs(V[0][m]) ** 2) * S, np.mean(np.abs(vr[m]) ** 2) * S, np.mean(np.abs(fn_[m]) ** 2) * S))
    print('   N in (%g, %g]: %s' % (lo, hi, ' ; '.join(parts)))
print('\ndone in %.0fs' % (time.time() - t0))
