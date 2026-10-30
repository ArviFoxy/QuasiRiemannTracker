"""Artificial mask on prime rows versus the genuine mask of composite rows (same surrogate on both sides).

  (P)  prime rows u = pi, sum over all sources                      surrogate: no mask
  (A)  prime rows u = pi, sources divisible by q removed (artificial mask; chi_pi * 1_{q not | n} is imprimitive)
  (G)  genuine composite rows u = q * pi' (exactly two factors, pi' prime with N(pi') > largest source norm)
  (A) and (G) have identical surrogates (random completely multiplicative f, mask {q}); q is a fixed prime ideal
  (default: the first ideal of norm 7).  The dual picture predicts that at m > 1/2 the artificially masked sums are LARGER
  than the genuine ones relative to the common surrogate (the imprimitive sum S(N) - chi(q) S(N/N(q)) has an unmasked dual),
  while a property intrinsic to prime moduli would make (A) smaller.
Surrogate moments by Monte Carlo with D independent draws per mask (the expectation is the same for every row of a class).
usage: python3 -I primerows_artmask.py --B 300000 --m 0.3 0.4 0.5 0.6 --q 7 --D 400000
"""
import sys, os, math, time, argparse, json
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sps
import probeB as PB
import primerows_core as PC

Z6 = PC.Z6


def surrogate_class(st, killed, D, rng, CH=4000):
    """E|S|^{2,4,6}/mass^k for f random completely multiplicative, sources in `killed` removed; returns means and sds."""
    Wl = (st.W * (~killed)[:, None]).astype(np.complex64)
    nIx = st.Ex.shape[1]
    s = np.zeros((3, len(st.lens))); s2 = np.zeros((3, len(st.lens))); mx = np.zeros(len(st.lens))
    n = 0
    while n < D:
        k = min(CH, D - n)
        J = rng.integers(0, 6, size=(nIx, k)).astype(np.float32)
        F = Z6[np.rint(np.asarray(st.ExS @ J)).astype(np.int64) % 6]          # nS x k
        a2 = np.abs(F.T @ Wl).astype(np.float64) ** 2 / st.mass                # k x nm
        for j in range(3):
            v = a2 ** (j + 1)
            s[j] += v.sum(0); s2[j] += (v ** 2).sum(0)
        mx = np.maximum(mx, a2.max(0))
        n += k
    mean = s / D
    sd = np.sqrt(np.maximum(s2 / D - mean ** 2, 0) / D)
    return mean, sd, mx


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, required=True)
    ap.add_argument('--m', type=float, nargs='+', required=True)
    ap.add_argument('--q', type=int, default=7, help='norm of the masking prime ideal (first ideal of that norm)')
    ap.add_argument('--D', type=int, default=200000)
    ap.add_argument('--seed', type=int, default=21)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    t0 = time.time()
    rng = np.random.default_rng(a.seed)
    st = PC.Setup(a.B, a.m, 'smooth')
    PI = st.PI
    jq = int(np.flatnonzero(PI['norm'] == a.q)[0])
    print(f'mask ideal: index {jq}, norm {a.q}, (a,b) = ({PI["a"][jq]},{PI["b"][jq]})', flush=True)
    S = st.actual()
    mass = st.mass
    prim = np.flatnonzero(st.nf == 1)
    gen = np.array([i for i in range(st.R) if st.nf[i] == 2 and st.rows[i][0] == jq and PI['norm'][st.rows[i][1]] > st.maxsrc])
    # artificial mask: recompute the prime rows' sums without the sources divisible by q
    killq = st.Ex[:, jq] > 0
    Wc = (st.W * (~killq)[:, None]).astype(np.complex64)
    SA = np.zeros((len(prim), len(st.lens)), dtype=np.complex128)
    for i0 in range(0, len(prim), 2000):
        idx = prim[i0:i0 + 2000]
        E, Z = PB.sextic_table(PC.subPI(PI, np.array([st.rows[i][0] for i in idx])), st.SA, st.SB)
        SA[i0:i0 + 2000] = (Z6[E.astype(np.int64)] * (~Z)) @ Wc
    print(f'prime rows {len(prim)}, genuine rows (q * pi\') {len(gen)}  ({time.time()-t0:.1f}s)', flush=True)
    mu0, sd0, mx0 = surrogate_class(st, np.zeros(st.nS, bool), a.D, rng)
    muq, sdq, mxq = surrogate_class(st, killq, a.D, rng)
    print(f'surrogates done ({time.time()-t0:.1f}s)', flush=True)
    a2P = np.abs(S[prim]) ** 2 / mass
    a2A = np.abs(SA) ** 2 / mass
    a2G = np.abs(S[gen]) ** 2 / mass
    cl = PC.pair_clusters(st.conj)
    out = []
    print('  m     | sur M6 (no mask)  sur M6 (mask q)  | P: M6, P/sur0 (se)     | A: M6, A/surq (se)     | G: M6, G/surq (se)     | log(A/G) (se)   | M2 P/A/G vs sur0/surq')
    rb = np.random.default_rng(3)
    for im, m in enumerate(st.ms):
        def bstat(v, clus):
            _, inv = np.unique(clus, return_inverse=True)
            nc = inv.max() + 1
            tot = np.bincount(inv, weights=v, minlength=nc); cnt = np.bincount(inv, minlength=nc).astype(float)
            bs = []
            for _ in range(400):
                w = np.bincount(rb.integers(0, nc, nc), minlength=nc).astype(float)
                bs.append((w @ tot) / (w @ cnt))
            return float(v.mean()), np.array(bs)
        mP, bP = bstat(a2P[:, im] ** 3, cl[prim])
        mA, bA = bstat(a2A[:, im] ** 3, np.arange(len(prim)))          # u and u-bar masked at the same q: no pairing
        mG, bG = bstat(a2G[:, im] ** 3, np.arange(len(gen)))           # q fixed: u-bar is not in the set
        lag = np.log(mA / mG); se_lag = np.std(np.log(bA) - np.log(bG))
        rec = dict(m=m, sur0=mu0[2, im], sur0_se=sd0[2, im], surq=muq[2, im], surq_se=sdq[2, im], P=mP, A=mA, G=mG,
                   P_se=float(np.std(bP)), A_se=float(np.std(bA)), G_se=float(np.std(bG)), logAG=lag, logAG_se=se_lag,
                   M2P=float(a2P[:, im].mean()), M2A=float(a2A[:, im].mean()), M2G=float(a2G[:, im].mean()),
                   sur0M2=mu0[0, im], surqM2=muq[0, im], nP=len(prim), nG=len(gen), maxP=float(a2P[:, im].max()),
                   maxA=float(a2A[:, im].max()), maxG=float(a2G[:, im].max()), surmax0=float(mx0[im]), surmaxq=float(mxq[im]))
        out.append(rec)
        print(f"  {m:.2f}  | {mu0[2,im]:7.3f} ({sd0[2,im]:.3f})  {muq[2,im]:7.3f} ({sdq[2,im]:.3f})  | {mP:6.3f} {mP/mu0[2,im]:.3f} ({np.std(bP)/mu0[2,im]:.3f}) "
              f"| {mA:6.3f} {mA/muq[2,im]:.3f} ({np.std(bA)/muq[2,im]:.3f}) | {mG:6.3f} {mG/muq[2,im]:.3f} ({np.std(bG)/muq[2,im]:.3f}) "
              f"| {lag:+.3f} ({se_lag:.3f}) | {rec['M2P']:.3f}/{rec['M2A']:.3f}/{rec['M2G']:.3f} vs {mu0[0,im]:.3f}/{muq[0,im]:.3f}", flush=True)
    if a.out:
        json.dump(dict(args=vars(a), results=out), open(a.out, 'w'), indent=1, default=float)
    print(f'done ({time.time()-t0:.1f}s)')


if __name__ == '__main__':
    main()
