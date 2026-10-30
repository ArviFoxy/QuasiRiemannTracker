"""ppsanity2.py -- (a) independent check of F: F = sum_z |sum_m c_m chi_z(m)|^2 with chi_z(m) computed for every ideal m of the support
(not through the product X1 X2 Q), versus the product formula used in ppgrid.py;
(b) the "random-sign" sanity check of the task: replace c_m by c_m * eps_m (random unimodular eps, same support) and compare
F_rs / D_cop with the structured F / D_cop;  (c) F/D ~ 1 when the total length is well below R.

    python3 -I ppsanity2.py B [m s]
"""
import os, sys, math
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ppcore import *

B = int(sys.argv[1]); m = float(sys.argv[2]) if len(sys.argv) > 2 else 0.35; s = float(sys.argv[3]) if len(sys.argv) > 3 else 0.4
ID = Ideals(2 * B); rows = enumerate_rows(B, ID); R = rows['R']
PID = rows['PID']; uid = np.unique(PID[PID >= 0]); LOC = local_index(PID, uid)
PA, PB, PN = primary_elements(B ** max(m, s))
pool = split_prime_sources(ID, B ** s, 2 * B ** s)
TA = np.array([P['a'] for P in pool], I64); TB = np.array([P['b'] for P in pool], I64)
rng = np.random.default_rng(11)
print('B=%d R=%d  m=%.2f s=%.2f  plain terms %d  pool %d' % (B, R, m, s, int((PN <= B ** m).sum()), len(pool)))
pmax = int(max(B ** max(m, s), 2 * B ** s + 1))
for kind in ('plain', 'smooth'):
    w = weight_vector(PN, B ** m, kind)
    aP = np.exp(2j * np.pi * rng.random(len(pool)))
    ka, kb, d = self_convolution(PA, PB, w)
    Am, ca, cb = conv_matrix(ka, kb, d, TA, TB)
    cvec = Am.T @ aP
    rho = rho_elements(ID, ca, cb, pmax)
    D = R * np.sum(np.abs(cvec) ** 2); Dcop = R * np.sum(rho * np.abs(cvec) ** 2)
    # product formula
    SA = np.concatenate([PA, TA]); SB = np.concatenate([PB, TB])
    T = symbol_table(ID, uid, SA, SB)
    chi = chi_chunk(LOC, T, 0, R)
    X = chi[:, :len(PA)] @ w; Q = chi[:, len(PA):] @ aP
    F_prod = np.sum(np.abs(X) ** 4 * np.abs(Q) ** 2)
    # direct expansion over ideals m of the support
    T2 = symbol_table(ID, uid, ca, cb)
    CH = max(50, 3_000_000 // len(ca))
    F_dir = 0.0
    Frs = []
    eps = np.exp(2j * np.pi * rng.random((60, len(ca))))
    sgn = rng.choice([-1.0, 1.0], size=(60, len(ca)))
    Frs_c = np.zeros(60); Frs_s = np.zeros(60)
    for r0 in range(0, R, CH):
        c2 = chi_chunk(LOC, T2, r0, min(R, r0 + CH))
        F_dir += np.sum(np.abs(c2 @ cvec) ** 2)
        Frs_c += np.sum(np.abs(c2 @ (cvec[:, None] * eps.T)) ** 2, axis=0)
        Frs_s += np.sum(np.abs(c2 @ (cvec[:, None] * sgn.T)) ** 2, axis=0)
    print('%-6s distinct ideals m: %7d (R=%d, ratio %.2f) | F_product=%.6g  F_direct=%.6g  rel.diff %.1e' % (
        kind, len(ca), R, len(ca) / R, F_prod, F_dir, abs(F_prod - F_dir) / F_dir))
    print('       D=%.5g  Dcop=%.5g | F/D=%.4f  F/Dcop=%.4f | random-phase same support: F/Dcop = %.4f +- %.4f (60 draws) ; random-sign: %.4f +- %.4f' % (
        D, Dcop, F_dir / D, F_dir / Dcop, Frs_c.mean() / Dcop, Frs_c.std() / Dcop, Frs_s.mean() / Dcop, Frs_s.std() / Dcop))
