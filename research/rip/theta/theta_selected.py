"""Does the low-frequency (reciprocity) outlier survive on slot-selected rows?

W = the top rho*R rows by |T(z)|, T(z) = sum over split slot primes pi with N(pi) in [P0, 2*P0] of chi_z(pi) (flat
weights), as in the fresh look's runs.  For the sextic matrix E and for RCHAR (each row prime's character conjugated
at random: rows are still characters, reciprocity is broken), each with its own slot sums, the script prints the top
eigenvalue of the unit-diagonal Gram on W and on random row sets of the same size (mean +- sd over draws), and the
Marchenko-Pastur edge (1 + sqrt(|W|/S))^2.  If the selection lines up with the reciprocity outlier, the sextic excess
on W over random W exceeds RCHAR's.

Two more diagnostics:
  * conc: the fraction of the energy of the top left singular vectors u_1..u_4 of the full matrix that sits on W,
    relative to the flat value |W|/R (random sets give 1).  This asks the same question for the full-family outlier
    directly (the sextic top vectors are the outlier, RCHAR's are bulk).
  * summary: the sextic-minus-RCHAR difference of (W - random), with a noise estimate from the spread of the random sets.

usage: python3 -I theta_selected.py B L P0[,P0,...] [rho,rho,...] [ndraw=12] [nrchar=2]
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np
import scipy.linalg as sla
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
P0s = [int(t) for t in sys.argv[3].split(',')]
rhos = [float(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else [0.1, 0.03, 0.01]
ndraw = int(sys.argv[5]) if len(sys.argv) > 5 else 12
nrchar = int(sys.argv[6]) if len(sys.argv) > 6 else 2
F = tc.build(B, L)
E, R, S, rows, SA, SB, SN, spf, ID, pc = F.E, F.R, F.S, F.rows, F.SA, F.SB, F.SN, F.spf, F.ID, F.pc
uid = np.unique(rows['PID'][rows['PID'] >= 0])
LOC = pc.local_index(rows['PID'], uid)
T = pc.symbol_table(ID, uid, SA, SB).astype(np.int16)
isprime = np.array([int(spf[int(n)]) == int(n) for n in SN])
slots = {P0: np.nonzero((SN >= P0) & (SN <= 2 * P0) & isprime)[0] for P0 in P0s}
print('slots: ' + ', '.join('P0=%d: %d split primes with norm in [%d, %d]' % (P0, len(s), P0, 2 * P0) for P0, s in slots.items()),
      flush=True)
rng = np.random.default_rng(41)


def top_unit(M, idx):
    A = M[idx]
    G = A @ A.conj().T
    d = np.sqrt(np.real(np.diag(G)))
    return float(sla.eigh(G / np.outer(d, d), eigvals_only=True, subset_by_index=[len(idx) - 1, len(idx) - 1])[0])


def left_vectors(M, k=4):
    U, s, Vh = svds(M, k=k, random_state=0)
    return U[:, np.argsort(-s)], np.sort(s)[::-1] ** 2 / S


out = {}                                    # (model, P0, rho) -> (W value, random mean, random sd)
for name, M in [('sextic', E)] + [('RCHAR%d' % (i + 1), None) for i in range(nrchar)]:
    if M is None:
        ec = np.random.default_rng(100 + len(out)).choice([1, 5], size=len(uid))
        Tc = np.where(T < 6, (T * ec[:, None]) % 6, T).astype(np.int8)
        M = pc.chi_chunk(LOC, Tc, 0, R).astype(np.complex128)
        del Tc
    U, lam = left_vectors(M)
    print('%s: top eigenvalues of E^H E / S %s' % (name, np.round(lam, 3)), flush=True)
    rand = {}
    for rho in rhos:
        n = max(2, int(rho * R))
        tr = [top_unit(M, rng.choice(R, n, replace=False)) for _ in range(ndraw)]
        rand[rho] = (np.mean(tr), np.std(tr, ddof=1))
    for P0, slot in slots.items():
        Tz = np.abs(M[:, slot].sum(1))
        order = np.argsort(-Tz)
        for rho in rhos:
            n = max(2, int(rho * R))
            W = order[:n]
            tw = top_unit(M, W)
            mp = (1 + math.sqrt(n / S)) ** 2
            conc = (np.abs(U[W]) ** 2).sum(0) * R / n
            concr = np.mean([(np.abs(U[rng.choice(R, n, replace=False)]) ** 2).sum(0) * R / n for _ in range(ndraw)], axis=0)
            m, sd = rand[rho]
            out[(name, P0, rho)] = (tw, m, sd)
            print('%-7s P0 %3d rho %.3f |W| %5d: slot-selected W %.3f   random W %.3f +- %.3f   MP %.3f   (W - random) %+.3f'
                  '   conc u1..u4 %s (random %s)' % (name, P0, rho, n, tw, m, sd, mp, tw - m, np.round(conc, 2), np.round(concr, 2)),
                  flush=True)
    del M

print('\nsummary: (W - random) for the sextic, for RCHAR (mean over draws), and their difference '
      '(+- the sd of the random sets, combined)')
for P0 in P0s:
    for rho in rhos:
        s_tw, s_m, s_sd = out[('sextic', P0, rho)]
        rc = [out[('RCHAR%d' % (i + 1), P0, rho)] for i in range(nrchar)]
        ds = s_tw - s_m
        dr = np.mean([t[0] - t[1] for t in rc])
        noise = math.sqrt(s_sd ** 2 * (1 + 1.0 / ndraw) + np.mean([t[2] ** 2 for t in rc]) * (1.0 / nrchar) * (1 + 1.0 / ndraw))
        print('P0 %3d rho %.3f: sextic %+.3f   RCHAR %+.3f (draws %s)   difference %+.3f   noise ~ %.3f' %
              (P0, rho, ds, dr, ' '.join('%+.3f' % (t[0] - t[1]) for t in rc), ds - dr, noise), flush=True)
