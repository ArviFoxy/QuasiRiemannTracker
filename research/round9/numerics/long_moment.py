#!/usr/bin/env python3
"""
Empirical long Moebius moment for the actual sextic family over Z[w] (atom 2 numerics).

Rows u: primary, (conservatively) squarefree, N(u) in [U, 2U)  (round-7 builder).
M_u(D) = D^{-1/2} sum_n mu(n) (u/n)_6 W(N(n)/D),   n ideals coprime to 6, N(n) in [D, 2D).
Prints the row average of |M_u|^2 against the diagonal sum_n mu(n)^2 W^2 / D, for D = U^t.
Amplification (7/8 Lemma 17.6) allows the average to grow like U^{(1+5t)/6 - 1} for t > 1;
Lindelof on average predicts ratio ~ 1.
"""
import sys, os, time, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'round7', 'large-values'))
from sextic_gram import build, column_ideals, bump

def moebius_and_psi_rows(K, cols, rows_idx=None, chunk=4000):
    """return vector of M-type sums S_u = sum_n mu(n) w_n psi_u(n) (unnormalized), and diag"""
    nR = K.shape[0]
    S = np.zeros(nR, dtype=complex)
    diag = 0.0
    for c0 in range(0, len(cols), chunk):
        cc = cols[c0:c0+chunk]
        mu = np.array([0 if any(e > 1 for (_, e) in fac) else (-1)**len(fac) for (N, fac) in cc], dtype=float)
        sel = mu != 0
        if not sel.any(): continue
        cc = [c for c, s in zip(cc, sel) if s]; mu = mu[sel]
        Y = None
        E = np.zeros((nR, len(cc)), dtype=np.int16); Z = np.zeros((nR, len(cc)), dtype=bool)
        for j, (N, fac) in enumerate(cc):
            for (i, e) in fac:
                k = K[:, i].astype(np.int16)
                Z[:, j] |= (k < 0)
                E[:, j] += e*np.where(k < 0, 0, k)
        Psi = np.exp(1j*np.pi/3*(E % 6)); Psi[Z] = 0
        yield cc, mu, Psi

if __name__ == "__main__":
    U = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    ts = [float(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [0.6, 0.8, 1.0, 1.155, 1.25]
    Ds = [int(round(U**t)) for t in ts]
    t0 = time.time()
    rows, K, pid, pindex, P = build(U, Ds)
    nR = len(rows)
    print(f"U={U} rows={nR} build {time.time()-t0:.1f}s", flush=True)
    for t, D in zip(ts, Ds):
        t1 = time.time()
        cols = column_ideals(D, pid, pindex, P)
        S = np.zeros(nR, dtype=complex); diag = 0.0; ncol = 0
        for cc, mu, Psi in moebius_and_psi_rows(K, cols):
            w = bump(np.array([c[0] for c in cc], dtype=float)/D)
            S += Psi @ (mu*w)
            diag += np.sum((mu*w)**2); ncol += len(cc)
        avg = np.mean(np.abs(S)**2)/D
        dg = diag/D
        pred_amp = U**(max(0.0, (1+5*t)/6 - 1))
        print(f"t={t:.3f} D={D} sqfree cols={ncol}: mean|M|^2={avg:.4f} diag={dg:.4f} "
              f"ratio={avg/dg:.3f}  (amplification allowance {pred_amp:.2f}; max|M|^2/diag={np.max(np.abs(S)**2)/D/dg:.2f}) "
              f"[{time.time()-t1:.1f}s]", flush=True)
