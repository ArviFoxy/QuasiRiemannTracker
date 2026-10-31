"""Does the low-frequency (reciprocity) outlier survive on slot-selected rows?  Matrix-free version of theta_selected.py.

Same test, for B = L up to 3e5: the symbol table and the compiled kernel (theta_ckernel) replace the dense matrix.  Only
the rows of W (and of the random comparison sets) are ever rebuilt: the top eigenvalue of the unit-diagonal Gram of a
row set is the top eigenvalue of E_W^H D^-1 E_W, found by Lanczos on the fused kernel restricted to those rows.

W = the top rho*R rows by |T(z)|, T(z) = sum over split slot primes pi with N(pi) in [P0, 2*P0] of chi_z(pi).  Models:
the sextic matrix, and RCHAR (each row prime's character conjugated at random: rows are still characters, reciprocity
is broken), each with its own slot sums.  Printed per model, P0 and rho:
  * the top eigenvalue on W, on random row sets of the same size (mean +- sd over draws), the Marchenko-Pastur value;
  * conc: the energy fraction of the top left singular vectors u_1..u_4 of the full matrix on W, relative to the flat
    value |W|/R (random sets give 1);
and at the end the sextic-minus-RCHAR difference of (W - random).  Positive control: 'oracle' rows W are the rows
carrying the most weight of the top-4 left singular subspace of the model's own matrix (for the sextic matrix that is
the outlier), so the sextic (W - random) must be large there and RCHAR's must not: this shows the test can see an
outlier that is concentrated on W.

Dilution check: random row sets at larger rho (default 0.2, 0.3, 0.5), sextic against RCHAR and against the rank-one
spike prediction.  A flat spike of strength theta on the full matrix has strength theta*sqrt(rho) on a random set of a
fraction rho of the rows, so it re-emerges from the edge of the set's spectrum only for rho > 1/theta^2.

usage: python3 -I theta_selected_free.py B L P0[,P0,...] [rho,rho,...] [ndraw=12] [nrchar=2] [threads=3] [scan_rho,...]
       (scan_rho: random-set rho values for the dilution check; '-' skips it)
"""
import os, sys, math, time
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')      # ARPACK on small vectors is slow under multithreaded BLAS
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402
import theta_ckernel as ck   # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
P0s = [int(t) for t in sys.argv[3].split(',')]
rhos = [float(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else [0.1, 0.03, 0.01]
ndraw = int(sys.argv[5]) if len(sys.argv) > 5 else 12
nrchar = int(sys.argv[6]) if len(sys.argv) > 6 else 2
threads = int(sys.argv[7]) if len(sys.argv) > 7 else 3
scan = [] if (len(sys.argv) > 8 and sys.argv[8] == '-') else [float(t) for t in (sys.argv[8] if len(sys.argv) > 8 else '0.2,0.3,0.5').split(',')]
t0 = time.time()
tb = tc.build_tables(B, L)
T, LOC, R, S, SN, spf = tb.T, tb.LOC, tb.R, tb.S, tb.SN, tb.spf
K = ck.Kernel(T, LOC, nthreads=threads)
isprime = np.array([int(spf[int(n)]) == int(n) for n in SN])
slots = {P0: np.nonzero((SN >= P0) & (SN <= 2 * P0) & isprime)[0] for P0 in P0s}
print('slots: ' + ', '.join('P0=%d: %d split primes with norm in [%d, %d]' % (P0, len(s), P0, 2 * P0) for P0, s in slots.items()),
      flush=True)
rng = np.random.default_rng(41)
ZE = np.exp(2j * np.pi * np.arange(6) / 6)


def slot_sums(slot):
    """|T(z)| for all rows: sum over the slot sources of chi_z(x), from the slot columns of the table only."""
    Ts = T[:, slot].astype(np.int16)
    acc = np.zeros((R, len(slot)), np.int16)
    for j in range(LOC.shape[1]):
        li = LOC[:, j]; sel = li >= 0
        acc[sel] += Ts[li[sel]]
    val = np.where(acc >= 100, 0, ZE[acc % 6])
    return np.abs(val.sum(1))


def top_unit(rows_):
    return float(K.top(k=1, rows=rows_, normalize=True, tol=1e-6)[0])


out = {}                                    # (model, P0, rho) -> (W value, random mean, random sd)
fullev = {}                                 # model -> top eigenvalue of the full matrix
scanv = {}                                  # (model, rho) -> random-set top eigenvalues
flip = np.zeros(len(tb.uid), bool)
for mi, name in enumerate(['sextic'] + ['RCHAR%d' % (i + 1) for i in range(nrchar)]):
    if mi >= 1:                              # conjugate the row-prime characters of the draw (an involution on T)
        want = np.random.default_rng(100 + mi).integers(0, 2, size=len(tb.uid)).astype(bool)
        for i in np.nonzero(want != flip)[0]:
            t = T[i]
            T[i] = np.where(t < 6, (6 - t) % 6, t)
        flip = want
    ev, vec = K.top(k=4, tol=1e-5, ncv=40, vectors=True)
    U = K.forward(vec) / np.sqrt(ev * S)
    print('%s: top eigenvalues of E^H E / S %s   (%.0fs)' % (name, np.round(ev, 3), time.time() - t0), flush=True)
    fullev[name] = ev
    for rho in scan:
        n = int(rho * R)
        scanv[(name, rho)] = [top_unit(np.sort(rng.choice(R, n, replace=False))) for _ in range(max(3, ndraw // 3))]
        print('%-7s random sets rho %.3f |W| %5d: top %.3f +- %.3f   (%.0fs)' % (name, rho, n, np.mean(scanv[(name, rho)]),
                                                                           np.std(scanv[(name, rho)], ddof=1), time.time() - t0), flush=True)
    rand = {}
    for rho in rhos:
        n = max(2, int(rho * R))
        tr = [top_unit(np.sort(rng.choice(R, n, replace=False))) for _ in range(ndraw)]
        rand[rho] = (np.mean(tr), np.std(tr, ddof=1))
    for P0, slot in slots.items():
        Tz = slot_sums(slot)
        order = np.argsort(-Tz)
        for rho in rhos:
            n = max(2, int(rho * R))
            W = np.sort(order[:n])
            tw = top_unit(W)
            mp = (1 + math.sqrt(n / S)) ** 2
            conc = (np.abs(U[W]) ** 2).sum(0) * R / n
            concr = np.mean([(np.abs(U[rng.choice(R, n, replace=False)]) ** 2).sum(0) * R / n for _ in range(ndraw)], axis=0)
            m, sd = rand[rho]
            out[(name, P0, rho)] = (tw, m, sd)
            print('%-7s P0 %3d rho %.3f |W| %5d: slot-selected W %.3f   random W %.3f +- %.3f   MP %.3f   (W - random) %+.3f'
                  '   conc u1..u4 %s (random %s)   (%.0fs)' % (name, P0, rho, n, tw, m, sd, mp, tw - m, np.round(conc, 2),
                                                               np.round(concr, 2), time.time() - t0), flush=True)
    sc = (np.abs(U) ** 2).sum(1)                          # weight of the top-4 left singular subspace on each row
    for rho in rhos:
        n = max(2, int(rho * R))
        W = np.sort(np.argsort(-sc)[:n])
        tw = top_unit(W)
        m, sd = rand[rho]
        out[(name, 'oracle', rho)] = (tw, m, sd)
        print('%-7s oracle (top-4 singular subspace) rho %.3f |W| %5d: W %.3f   random W %.3f +- %.3f   (W - random) %+.3f   '
              'subspace energy on W %.2f x flat   (%.0fs)' % (name, rho, n, tw, m, sd, tw - m, sc[W].sum() * R / (4.0 * n), time.time() - t0),
              flush=True)

print('\nsummary: (W - random) for the sextic, for RCHAR (mean over draws), and their difference '
      '(noise: sd of the random sets, combined)')
for P0 in P0s + ['oracle']:
    for rho in rhos:
        s_tw, s_m, s_sd = out[('sextic', P0, rho)]
        rc = [out[('RCHAR%d' % (i + 1), P0, rho)] for i in range(nrchar)]
        ds = s_tw - s_m
        dr = np.mean([t[0] - t[1] for t in rc])
        noise = math.sqrt(s_sd ** 2 * (1 + 1.0 / ndraw) + np.mean([t[2] ** 2 for t in rc]) * (1.0 / nrchar) * (1 + 1.0 / ndraw))
        print('P0 %5s rho %.3f: sextic %+.3f   RCHAR %+.3f (draws %s)   difference %+.3f   noise ~ %.3f' %
              (P0, rho, ds, dr, ' '.join('%+.3f' % (t[0] - t[1]) for t in rc), ds - dr, noise), flush=True)

if scan:
    edge = float(np.mean([fullev['RCHAR%d' % (i + 1)][0] for i in range(nrchar)]))
    r = fullev['sextic'][0] / edge
    theta = (math.sqrt(r) + math.sqrt(r - 1.0)) ** 2
    print('\ndilution check: full matrix sextic top %.3f, RCHAR edge %.3f, theta = %.3f' % (fullev['sextic'][0], edge, theta))
    for rho in scan:
        sx = np.mean(scanv[('sextic', rho)])
        rc = np.mean([np.mean(scanv[('RCHAR%d' % (i + 1), rho)]) for i in range(nrchar)])
        thW = theta * math.sqrt(rho)
        pred = rc * ((math.sqrt(thW) + 1.0 / math.sqrt(thW)) ** 2 / 4.0 if thW > 1 else 1.0)
        print('rho %.3f: random sets sextic %.4f   RCHAR %.4f   ratio %.4f   rank-one prediction theta*sqrt(rho) = %.2f -> ratio %.4f' %
              (rho, sx, rc, sx / rc, thW, pred / rc))
