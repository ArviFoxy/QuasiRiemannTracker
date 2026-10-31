"""Task B1: row side of the top singular pair of E (u = top left vector, E v = s u).

  1. energy of u_k (k = 0, 1, 2) in the block span {chi_z(m) chi_z(u): N(m) <= M, six units} for M = 30, 100, 300, 1000, against
     (a) Gaussian random subspaces of the same dimension (d/R) and (b) the top left vector of a masked-random matrix;
  2. which unit twists carry the weight (separate spans for each unit u, N(m) <= 100);
  3. the best-fit coefficients on the plain columns: R|<q_m, u0>|^2 with q_m = E[:,m]/|E[:,m]| (noise floor 1), binned in N(m), and a
     power-law regression of the excess;  c_m = s v0(m)/|E[:,m]| exactly, so this is the source profile seen from the rows;
  4. class functions of the rows: energy of u_k in the span of the indicators of the classes of z_* mod 4 (12), mod 3 (2 =
     parity of omega(z)), mod 9 (18), mod 36 (216), and in the span of the 6 unit classes (chi_z(-1), chi_z(w));
  5. omega(z) profile of |u|^2 (primes versus composites) against the null;
  6. the class-signed source theta f of theta_mech_corner.py (12 fitted class phases, alpha = 1/3) and its row image E f:
     overlap with u0 and the same block-span energies, i.e. how much of u0's low-frequency content E f reproduces.

usage: python3 -I theta_mech_rows.py B L          (set SCRATCH to a scratch directory; top singular triples are cached there)
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
F, sd, rd, sc, s, U, Vh, R, S = A_.F, A_.sd, A_.rd, A_.sc, A_.s, A_.U, A_.Vh, A_.R, A_.S
E = F.E
SN = F.SN.astype(float)
rng = np.random.default_rng(5)
print('top s^2/S: %s' % np.round(s[:6] ** 2 / S, 3), flush=True)
mask = np.abs(E) > 0.5
Er = mask * np.exp(2j * np.pi * rng.random(E.shape))
Ur, sr, _ = svds(Er, k=2, random_state=0)
o = np.argsort(-sr); ur = Ur[:, o[0]]
del Er
print('masked-random top s^2/S: %s' % np.round(np.sort(sr)[::-1] ** 2 / S, 3), flush=True)
order = np.argsort(SN)
u_ = [U[:, k] for k in range(3)]
ut = F.unit_tw


def blocks_for(M, units=range(6)):
    idx = order[SN[order] <= M]
    cols = [E[:, idx] * ut[:, k][:, None] for k in units]
    return np.concatenate(cols, axis=1), len(idx)


print('\n1. energy of u_k in the block span {chi_z(m) chi_z(u): N(m) <= M, 6 units}')
print('   M      #m  dim   u0     u1     u2    | masked-random top | random subspace d/R')
for M in (30, 100, 300, 1000):
    Bk, nm = blocks_for(M)
    Q, _ = np.linalg.qr(Bk)
    en = [tu.energy_in_span(Q, u_[k]) for k in range(3)]
    er = tu.energy_in_span(Q, ur)
    print('   %-5d %4d %5d  %.3f  %.3f  %.3f |      %.3f        | %.3f' % (M, nm, Q.shape[1], *en, er, Q.shape[1] / R))
    del Bk, Q

print('\n2. separate unit twists (N(m) <= 100): energy of u_k in span{chi_z(m) chi_z(u_j)}, u_j = 1, w, w^2, -1, -w, -w^2')
idx = order[SN[order] <= 100]
for k in range(3):
    row = []
    for j in range(6):
        Q, _ = np.linalg.qr(E[:, idx] * ut[:, j][:, None])
        row.append(tu.energy_in_span(Q, u_[k]))
    print('   u%d : %s   (random %.3f)' % (k, ' '.join('%.3f' % x for x in row), len(idx) / R))

print('\n3. plain columns: R |<q_m, u0>|^2 (noise floor 1) by N(m); power-law regression of the excess')
cn = np.linalg.norm(E, axis=0)
coef = (E.conj().T @ u_[0]) / cn
e_m = R * np.abs(coef) ** 2
edges = [1, 10, 30, 100, 300, 1000, 3000, 10 ** 9]
xs, ys, ns = [], [], []
for lo, hi in zip(edges[:-1], edges[1:]):
    m = (SN > lo) & (SN <= hi)
    if m.sum():
        pr = m & (sd['nprime'] == 1); co = m & (sd['nprime'] >= 2)
        print('   N(m) in (%5g, %6g]  [%4d]  mean R|c|^2 = %6.2f   primes %6.2f [%d]  composites %6.2f [%d]   null (masked random) %5.2f' %
              (lo, hi, m.sum(), e_m[m].mean(), e_m[pr].mean() if pr.any() else float('nan'), pr.sum(), e_m[co].mean() if co.any() else float('nan'), co.sum(),
               R * np.mean(np.abs((E.conj().T @ ur)[m] / cn[m]) ** 2)))
        xs.append(np.mean(SN[m])); ys.append(e_m[m].mean()); ns.append(m.sum())
xs, ys, ns = np.array(xs), np.array(ys), np.array(ns, float)
sel = xs < 1500
for fl in (1.0,):
    ex = np.maximum(ys[sel] - fl, 1e-3)
    pfit = np.polyfit(np.log(xs[sel]), np.log(ex), 1, w=np.sqrt(ns[sel]))
    print('   regression log(R|c|^2 - 1) on log N over N < 1500: exponent %.2f  (i.e. |c_m| ~ N^%.2f)' % (pfit[0], pfit[0] / 2))

print('   dependence of the excess on the class of m (N(m) in [30, 3000]): mean R|c|^2 by class mod 4 and by the cubic class t = n mod 3; mean over the 12 classes of |sum c_m phase|/..: see theta_mech_src.py')
mm = (SN > 30) & (SN <= 3000)
row = []
for c in sorted(set(sc['c4'].tolist())):
    m = mm & (sc['c4'] == c)
    row.append('(%d,%d): %.1f[%d]' % (c // 4, c % 4, e_m[m].mean(), m.sum()))
print('   by class mod 4: ' + '  '.join(row))
print('   by t: ' + '  '.join('t=%d: %.1f' % (t_, e_m[mm & (sc['t'] == t_)].mean()) for t_ in range(3)) + ' ; by chi_x(-1): +1: %.1f  -1: %.1f' % (e_m[mm & ~sc['odd']].mean(), e_m[mm & sc['odd']].mean()))

print('\n4. class functions of the rows: energy of u_k in the span of class indicators (random = dim/R), and of the null vector')
gen = rd['gen']
c4 = rd['cls4']; par = rd['par']
c9 = (gen[:, 0] % 9) * 9 + (gen[:, 1] % 9)
uc = rd['chim1'] * 3 + rd['chiw']
for name, cl in (('z_* mod 4', c4), ('parity omega(z)', par), ('z_* mod 9', c9), ('z_* mod 12', c4 * 2 + par), ('z_* mod 36', c4 * 100 + c9), ('unit class (chi(-1), chi(w))', uc),
                 ('omega(z) = 1,2,3,4', rd['nprime'])):
    X = tu.class_span(cl, np.ones(R, complex)); Xn = X / np.linalg.norm(X, axis=0, keepdims=True)
    en = [np.linalg.norm(Xn.conj().T @ u_[k]) ** 2 for k in range(3)]
    print('   %-30s dim %3d : u0 %.3f  u1 %.3f  u2 %.3f   null %.3f   random %.3f' % (name, Xn.shape[1], *en, np.linalg.norm(Xn.conj().T @ ur) ** 2, Xn.shape[1] / R))

print('\n5. omega(z) profile of R|u|^2 (primes = rows with one prime ideal)')
for w_ in (1, 2, 3, 4):
    m = rd['nprime'] == w_
    if m.sum() >= 5:
        print('   omega(z) = %d [%5d rows]: u0 %.2f  u1 %.2f  u2 %.2f   null %.2f' % (w_, m.sum(), np.mean(np.abs(u_[0][m]) ** 2) * R, np.mean(np.abs(u_[1][m]) ** 2) * R, np.mean(np.abs(u_[2][m]) ** 2) * R, np.mean(np.abs(ur[m]) ** 2) * R))

print('\n6. row image of the class-signed source theta')
base, Xn = tu.class_signed_fit(A_, 1 / 3)
M = tu.compressed(F, Xn, 'src')
w, Vv = tu.top_eig(M, 1)
f = Xn @ Vv[:, 0]
Ef = E @ f
w_ = Ef / np.linalg.norm(Ef)
print('   compressed top s^2/R %.3f ; |<f,v0>| %.3f ; |<Ef/|Ef|, u0>| %.3f' % (w[0], abs(np.vdot(f, Vh[0].conj())), abs(np.vdot(w_, u_[0]))))
print('   block-span energies (M: u0, Ef/|Ef|, random):')
for Mc in (30, 100, 300, 1000):
    Bk, nm = blocks_for(Mc)
    Q, _ = np.linalg.qr(Bk)
    print('     M=%-5d dim %4d : u0 %.3f   Ef %.3f   random %.3f' % (Mc, Q.shape[1], tu.energy_in_span(Q, u_[0]), tu.energy_in_span(Q, w_), Q.shape[1] / R))
    del Bk, Q
for name, cl in (('z_* mod 36', c4 * 100 + c9),):
    X = tu.class_span(cl, np.ones(R, complex)); Xn2 = X / np.linalg.norm(X, axis=0, keepdims=True)
    print('   class-function energy (mod 36): u0 %.3f  Ef %.3f  random %.3f' % (np.linalg.norm(Xn2.conj().T @ u_[0]) ** 2, np.linalg.norm(Xn2.conj().T @ w_) ** 2, Xn2.shape[1] / R))
for w2 in (1, 2, 3):
    m = rd['nprime'] == w2
    print('   omega(z) = %d: R|u0|^2 %.2f   R|Ef|^2/|Ef|^2 %.2f' % (w2, np.mean(np.abs(u_[0][m]) ** 2) * R, np.mean(np.abs(w_[m]) ** 2) * R))
print('\ndone in %.0fs' % (time.time() - t0))
