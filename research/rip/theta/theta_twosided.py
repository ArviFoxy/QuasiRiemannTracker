"""The sextic family with both thetas removed: a numerical test of TwoSidedSpikeFree (lean/arvi_kwall/SourceSpike.lean).

Row side V (the shapes of SexticSpikeFree.lean, times class functions of the row generator mod 4 and mod 9, which
contain every supplementary twist and the unit twists):
  m = 1:        G6(z), 1 (plain), each on every class, profiles (N z/B)^{-j/2}, j < J;
  twists m with N(m) <= M (the sources): G6 conj chi_z(m), chi_z(m), conj chi_z(m), on the 6 unit classes, j < J.
Source side P (the source thetas): conj g6(x) N(x)^{-beta} and g6(x) N(x)^{-beta} on each cell (x mod 4, x mod 9,
parity of omega(x)), beta in the list given (the source theta of the numerics has beta = 1/3).
The script prints the top s^2/S of E, of E off V (one-sided, the old conjecture), of E off V and P (two-sided), and
of the same with random spans of the same dimensions, with the energies of the top pairs in V and in P.

usage: python3 -I theta_twosided.py B L [M] [J] [beta,...]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds, LinearOperator

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_util as tu      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
M = int(sys.argv[3]) if len(sys.argv) > 3 else 30
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
betas = [float(t) for t in sys.argv[5].split(',')] if len(sys.argv) > 5 else [1.0 / 3]
A = tu.load_all(B, L, 8)
F, R, S, rd, sd = A.F, A.R, A.S, A.rd, A.sd
E, t0 = F.E, F.t0
gen = rd['gen']
c36 = ((gen[:, 0] % 4) * 4 + gen[:, 1] % 4) * 81 + (gen[:, 0] % 9) * 9 + gen[:, 1] % 9
unit = (rd['chim1'] > 0) * 3 + rd['chiw']
prof = [(F.rows['N'].astype(float) / B) ** (-j / 2) for j in range(J)]
G = F.Grow


def orth(X):
    Q, Rr = np.linalg.qr(X)
    d = np.abs(np.diag(Rr))
    return Q[:, d > 1e-8 * d.max()]


cols = [tu.class_span(c36, G * p) for p in prof] + [tu.class_span(c36, p.astype(complex)) for p in prof]
for j in tu.block_columns(F, M):
    for p in prof:
        cols += [tu.class_span(unit, G * np.conj(E[:, j]) * p), tu.class_span(unit, E[:, j] * p),
                 tu.class_span(unit, np.conj(E[:, j]) * p)]
QV = orth(np.concatenate(cols, axis=1))
dV = QV.shape[1]
SN = F.SN.astype(float)
cell = (((F.SA % 4) * 4 + F.SB % 4) * 81 + (F.SA % 9) * 9 + F.SB % 9) * 2 + sd['nprime'] % 2
g6 = sd['Gsrc']
pc_ = []
for be in betas:
    pc_ += [tu.class_span(cell, np.conj(g6) * SN ** (-be)), tu.class_span(cell, g6 * SN ** (-be))]
QP = orth(np.concatenate(pc_, axis=1))
dP = QP.shape[1]
print('B=%d: R=%d S=%d; row family V (M=%d, J=%d) dim %d (%.3f R); source family P (betas %s) dim %d (%.3f S)   (%.0fs)'
      % (B, R, S, M, J, dV, dV / R, betas, dP, dP / S, time.time() - t0), flush=True)
rng = np.random.default_rng(89)
QVr = orth(rng.standard_normal((R, dV)) + 1j * rng.standard_normal((R, dV)))
QPr = orth(rng.standard_normal((S, dP)) + 1j * rng.standard_normal((S, dP)))


def top(Qrow=None, Qsrc=None, k=4, vecs=False):
    def rp(u):
        return u if Qrow is None else u - Qrow @ (Qrow.conj().T @ u)

    def sp(v):
        return v if Qsrc is None else v - Qsrc @ (Qsrc.conj().T @ v)
    op = LinearOperator((R, S), dtype=complex, matvec=lambda v: rp(E @ sp(v)), rmatvec=lambda u: sp(E.conj().T @ rp(u)))
    U, s, Vh = svds(op, k=k, random_state=0)
    o = np.argsort(-s)
    return (s[o] ** 2 / S, U[:, o], Vh[o]) if vecs else s[o] ** 2 / S


def edge(dr, ds):
    return (math.sqrt((R - dr) / S) + math.sqrt((S - ds) / S)) ** 2


t, U0, V0 = top(vecs=True)
print('full top                        %s   MP edge %.3f' % (np.round(t, 3), edge(0, 0)), flush=True)
for i in range(2):
    cv = QV.conj().T @ U0[:, i]; cp = QP.conj().T @ V0[i].conj()
    print('  pair %d: left in V %.3f (random %.3f); right in P %.3f (random %.3f)'
          % (i, float(np.vdot(cv, cv).real), dV / R, float(np.vdot(cp, cp).real), dP / S), flush=True)
t1, U1, V1 = top(QV, None, vecs=True)
cp = QP.conj().T @ V1[0].conj()
print('one-sided, off V                %s   MP edge %.3f;  its top right vector in P %.3f'
      % (np.round(t1, 3), edge(dV, 0), float(np.vdot(cp, cp).real)), flush=True)
print('two-sided, off V and P          %s   MP edge %.3f' % (np.round(top(QV, QP), 3), edge(dV, dP)), flush=True)
print('off V, random source span       %s' % np.round(top(QV, QPr), 3), flush=True)
print('random spans, same dims         %s' % np.round(top(QVr, QPr), 3), flush=True)
print('done in %.0fs' % (time.time() - t0))
