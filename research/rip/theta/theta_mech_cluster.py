"""Task B4: the cluster of weaker outliers.  Is the second tier (v1, v2, ...) made of copies of the class-signed source theta?

  1. twisted copies:  f_m(x) = chi_x(m)^s * f(x)  for the 12 smallest sources m (and m = 1), s = +1 / -1, f the class-signed conj g~
     of theta_mech_corner.py (12 class coefficients refitted for each twist).  Compressed top eigenvalue of Q^*(E^*E)Q/R against
     the random-phase span, and the energy of v_0..v_7 in the union of all twisted spans (random = dim/S).  The dual-atom picture
     predicts copies for h = m j^6 with multiplicity decreasing in N(m), and only for one sign of the twist.
  2. splitting the rows by the unit character of z (6 classes of (chi_z(-1), chi_z(w))) and by chi_z(-1) = +-1: top singular values of
     each submatrix against masked random, the refitted class-phase vector A^kappa (phases in units of 30 degrees, spread of |A|),
     overlaps between the vectors A^kappa and between the sub-spike vectors, and the energy of the full v_k in the span of the
     sub-spike vectors.  (Rows with chi_z(-1) = +1 are the rows with N(z) = 1 mod 4.)

usage: python3 -I theta_mech_cluster.py B L          (set SCRATCH to a scratch directory)
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
rng = np.random.default_rng(2)
Vk = np.array([Vh[k].conj() for k in range(8)])
print('top s^2/S: %s' % np.round(s[:8] ** 2 / S, 3), flush=True)
base0, Xn0 = tu.class_signed_fit(A_, 1 / 3)
order = np.argsort(SN)


def chi_m(m):
    out = np.zeros(S, complex)
    for j in range(S):
        v = 1 + 0j
        for gi in sd['primes'][j]:
            t = F.sym(gi['prime'], m)
            if t is None:
                v = 0; break
            v *= t
        out[j] = v
    return out


def span_of(base):
    X = tu.class_span(sc['c4'], base)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    return X / np.linalg.norm(X, axis=0, keepdims=True)


def comp_top(Xn, k=3):
    M = tu.compressed(F, Xn, 'src')
    w, V = np.linalg.eigh(M)
    o = np.argsort(-w)
    return w[o][:k], Xn @ V[:, o[0]]


print('\n1. twisted copies f * chi_x(m)^s  (12 smallest sources m; random-phase 12-dim span top ~ 1.05 at B = 1e4)')
rp = np.mean([comp_top(span_of(np.exp(2j * np.pi * rng.random(S)) * SN ** (-1 / 3)), 1)[0][0] for _ in range(4)])
w0, f0 = comp_top(Xn0)
print('   m = 1                       : top %s ; excess over random %.3f ; |<f,v0>| %.3f' % (np.round(w0, 3), w0[0] - rp, abs(np.vdot(f0, Vk[0]))))
cands = [(int(F.SA[j]), int(F.SB[j]), int(SN[j])) for j in order[:12]]
spans = [Xn0]
for a, b, n in cands:
    chm = chi_m((a, b))
    for sgn in (+1, -1):
        base = base0 * (chm if sgn == 1 else np.conj(chm))
        Xn = span_of(base)
        w, f = comp_top(Xn)
        ov = np.abs(Vk[:6].conj() @ f)
        print('   m = (%3d,%3d) N=%3d  s=%+d : top %s ; excess %.3f ; overlaps with v0..v5 %s' % (a, b, n, sgn, np.round(w, 3), w[0] - rp, np.round(ov, 2)))
        if sgn == 1:
            spans.append(Xn)
Q, _ = np.linalg.qr(np.concatenate(spans, axis=1))
en = [np.linalg.norm(Q.conj().T @ Vk[k]) ** 2 for k in range(8)]
print('   union of the s=+1 spans (m = 1 and the 12 smallest): dim %d, random %.3f ; energy of v0..v7: %s' % (Q.shape[1], Q.shape[1] / S, np.round(en, 3)))
wU = np.sort(np.linalg.eigvalsh(tu.compressed(F, Q, 'src')))[::-1]
Qr, _ = np.linalg.qr(rng.standard_normal((S, Q.shape[1])) + 1j * rng.standard_normal((S, Q.shape[1])))
wR = np.sort(np.linalg.eigvalsh(tu.compressed(F, Qr, 'src')))[::-1]
print('   compressed top-12 of the union: %s' % np.round(wU[:12], 3))
print('   random span, same dim         : %s' % np.round(wR[:12], 3))
print('   singular values s_k^2/R of E  : %s' % np.round(s ** 2 / R, 3))

print('\n2. row splits by the unit character of z: top singular values of the submatrices, refitted class phases, overlaps')
uc = rd['chim1'] * 3 + rd['chiw']
sets = [('chi_z(-1)=+1', np.nonzero(rd['chim1'] > 0)[0]), ('chi_z(-1)=-1', np.nonzero(rd['chim1'] < 0)[0])]
sets += [('unit class %d' % c, np.nonzero(uc == c)[0]) for c in sorted(set(uc.tolist()))]
nrm = np.linalg.norm(tu.class_span(sc['c4'], base0), axis=0)
phases = {}
subv = {}
for name, rows in sets:
    X = E[rows]
    u_, s_, vh_ = svds(X, k=3, random_state=0)
    o = np.argsort(-s_); s_ = s_[o]; vh_ = vh_[o]
    mk = np.abs(X) > 0.5
    edge = np.sort(svds(mk * np.exp(2j * np.pi * rng.random(X.shape)), k=1, return_singular_vectors=False))[-1] ** 2 / S
    XQ = X @ Xn0
    M = XQ.conj().T @ XQ / len(rows)
    wv, Vv = np.linalg.eigh((M + M.conj().T) / 2)
    o2 = np.argsort(-wv)
    a = Vv[:, o2[0]] / nrm
    a = a / np.abs(a).mean()
    phases[name] = a * np.conj(a[0]) / abs(a[0])
    subv[name] = vh_[0].conj()
    ph = np.angle(phases[name]) * 6 / np.pi
    print('   %-14s R\'=%4d: top s^2/S %s (masked random %.3f, excess %+.1f%%) ; class-signed span top %.3f ; |A| spread %.2f ; phases/30deg %s' %
          (name, len(rows), np.round(s_ ** 2 / S, 3), edge, 100 * (s_[0] ** 2 / S / edge - 1), wv[o2[0]], np.abs(a).std() / np.abs(a).mean(), np.round(ph, 1)))
names = [n for n, _ in sets]
Mo = np.array([[abs(np.vdot(phases[a], phases[b])) / (np.linalg.norm(phases[a]) * np.linalg.norm(phases[b])) for b in names] for a in names])
np.set_printoptions(linewidth=200, precision=2, suppress=True)
print('   overlaps |<A^a, A^b>| of the refitted class-phase vectors (order %s):' % names)
print(Mo)
Vs = np.array([subv[n] for n in names])
print('   overlaps |<v_a, v_b>| of the sub-spike (top right) vectors:')
print(np.abs(Vs.conj() @ Vs.T))
print('   |<full v_k, sub-spike vector>| (rows k = 0..5, columns = %s):' % names)
print(np.abs(Vk[:6].conj() @ Vs.T))
Qs, _ = np.linalg.qr(Vs.T)
print('   energy of v_0..v_7 in the span of the %d sub-spike vectors (random %.4f): %s' % (len(names), len(names) / S, np.round([np.linalg.norm(Qs.conj().T @ Vk[k]) ** 2 for k in range(8)], 3)))
print('\ndone in %.0fs' % (time.time() - t0))
