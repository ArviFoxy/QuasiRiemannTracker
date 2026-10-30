"""Gap, transplant shift and residual split by the 3-part of the conductor (c = 0: k = 0, c = 1: k = 3, c = 2: else).
The dual picture predicts that the prime/composite gap and the transplant shift are largest where the dual is shortest
(c = 0) and small where it is longest (c = 2), at fixed m.
usage: python3 -I primerows_byc.py 4e5 8e5 1.6e6     (needs logsP/run_<B>.npz and logsP/transplant_rows_<B>.npz)
"""
import sys, os
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import primerows_core as PC

rng = np.random.default_rng(5)
acc = {}
for B in sys.argv[1:]:
    d = np.load(os.path.join(HERE, 'logsP', f'run_{B}.npz'))
    t = np.load(os.path.join(HERE, 'logsP', f'transplant_rows_{B}.npz'))
    K = int(d['K']); ms = [round(float(x), 3) for x in d['ms']]
    a6 = (np.abs(d['S']) ** 2 / d['mass']) ** 3; s6 = d['acc'][:, :, 2, :].sum(-1) / K
    nf = d['nf']; kres = d['kres']; cexp = np.where(kres == 0, 0, np.where(kres == 3, 1, 2))
    cl = PC.pair_clusters(d['conj'])
    prim = t['prim']; A6 = t['composite_A6']; SV = t['composite_sv']
    assert np.all(nf[prim] == 1)
    for im, m in enumerate(ms):
        for c in (0, 1, 2):
            sp = prim[cexp[prim] == c]; sc = np.flatnonzero((nf >= 2) & (cexp == c))
            ip = np.flatnonzero(cexp[prim] == c)
            # bootstrap over clusters: prime rows (actual, own surrogate, transplanted, its surrogate) and composite rows
            _, invp = np.unique(cl[sp], return_inverse=True); ncp = invp.max() + 1
            Tp = [np.bincount(invp, weights=x, minlength=ncp) for x in (a6[sp, im], s6[sp, im], A6[ip, im], SV[ip, im])]
            _, invc = np.unique(cl[sc], return_inverse=True); ncc = invc.max() + 1
            Tc = [np.bincount(invc, weights=x, minlength=ncc) for x in (a6[sc, im], s6[sc, im])]
            def stats(wp, wc):
                rp = (wp @ Tp[0]) / (wp @ Tp[1]); rt = (wp @ Tp[2]) / (wp @ Tp[3]); rc = (wc @ Tc[0]) / (wc @ Tc[1])
                return np.array([np.log(rp / rc), np.log(rt / rp), np.log(rt / rc), rp, rc])
            est = stats(np.ones(ncp), np.ones(ncc))
            bs = np.array([stats(np.bincount(rng.integers(0, ncp, ncp), minlength=ncp).astype(float),
                                 np.bincount(rng.integers(0, ncc, ncc), minlength=ncc).astype(float)) for _ in range(300)])
            acc.setdefault((m, c), []).append((B, est, bs.std(0)))
print('| m | c | B used | ratio prime | ratio composite | gap | transplant shift | residual |')
print('|---|---|---|---|---|---|---|---|')
for (m, c), L in sorted(acc.items()):
    est = np.array([x[1] for x in L]); se = np.array([x[2] for x in L])
    w = 1 / se[:, :3] ** 2
    pm = (w * est[:, :3]).sum(0) / w.sum(0); ps = 1 / np.sqrt(w.sum(0))
    print(f"| {m:.2f} | {c} | {','.join(x[0] for x in L)} | {est[:,3].mean():.3f} | {est[:,4].mean():.3f} | {pm[0]:+.3f} ± {ps[0]:.3f} | {pm[1]:+.3f} ± {ps[1]:.3f} | {pm[2]:+.3f} ± {ps[2]:.3f} |")
