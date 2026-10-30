"""Pooled tables for PRIMEROWS.md from the primerows_run.py / primerows_transplant.py outputs in logsP/.
  T1  prime vs composite gap, transplant shift, residual, per (B, m), and inverse-variance pooled over the disjoint
      row sets B in {1e5, 2e5, 4e5, 8e5, 1.6e6} (B = 3e5 overlaps 2e5 and 4e5: shown, not pooled);
  T2  ratio actual/surrogate by the 3-part of the conductor (c = 0, 1, 2), all rows;
  T3  min-7 composite rows vs prime rows, and the q=7-mask transplant.
usage: python3 -I primerows_summary.py
"""
import sys, os, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import primerows_core as PC

L = os.path.join(HERE, 'logsP')
BS = ['1e5', '2e5', '3e5', '4e5', '8e5', '1.6e6']
POOL = ['1e5', '2e5', '4e5', '8e5', '1.6e6']
rng = np.random.default_rng(2)


def ratio_boot(a6, s6, cl, sel, nb=300):
    r, se, bs = PC.boot_ratio(a6, s6, cl, nb=nb, rng=rng, sel=sel)
    return r, bs


rows = {}
for B in BS:
    f = os.path.join(L, f'run_{B}.npz')
    if not os.path.exists(f):
        continue
    d = np.load(f)
    K = int(d['K']); ms = [round(float(x), 3) for x in d['ms']]
    a2 = np.abs(d['S']) ** 2 / d['mass']; s6 = d['acc'][:, :, 2, :].sum(-1) / K
    nf = d['nf']; minn = d['minnorm']; kres = d['kres']
    cexp = np.where(kres == 0, 0, np.where(kres == 3, 1, 2))
    cl = PC.pair_clusters(d['conj'])
    tj = os.path.join(L, f'transplant_{B}.json')
    tr = json.load(open(tj))['results'] if os.path.exists(tj) else None
    for im, m in enumerate(ms):
        rp, bp = ratio_boot(a2[:, im] ** 3, s6[:, im], cl, nf == 1)
        rc, bc = ratio_boot(a2[:, im] ** 3, s6[:, im], cl, nf >= 2)
        r7, b7 = ratio_boot(a2[:, im] ** 3, s6[:, im], cl, (nf >= 2) & (minn == 7))
        rec = dict(B=B, m=m, nP=int((nf == 1).sum()), nC=int((nf >= 2).sum()), rp=rp, rc=rc, r7=r7,
                   gap=np.log(rp / rc), gap_se=float(np.std(np.log(bp) - np.log(bc))),
                   gap7=np.log(rp / r7), gap7_se=float(np.std(np.log(bp) - np.log(b7))),
                   sur_p=float(s6[nf == 1, im].mean()), act_p=float((a2[nf == 1, im] ** 3).mean()))
        for c in (0, 1, 2):
            rr, bb = ratio_boot(a2[:, im] ** 3, s6[:, im], cl, cexp == c, nb=200)
            rec[f'c{c}'] = rr; rec[f'c{c}_se'] = float(np.std(bb))
        if tr is not None:
            for pool in ('composite', 'min7'):
                t = [x for x in tr[pool] if abs(x['m'] - m) < 1e-9][0]
                rec[f'{pool}_shift'] = t['log_tp']; rec[f'{pool}_shift_se'] = t['log_tp_se']
                rec[f'{pool}_resid'] = t['logdiff']; rec[f'{pool}_resid_se'] = t['logdiff_se']
                rec[f'{pool}_rt'] = t['transplant']
        rows[(B, m)] = rec
    print(f'loaded {B}', flush=True)


def pooled(keys, field):
    v = np.array([rows[k][field] for k in keys]); s = np.array([rows[k][field + '_se'] for k in keys])
    w = 1 / s ** 2
    return float((w * v).sum() / w.sum()), float(1 / np.sqrt(w.sum()))


allm = sorted({m for (_, m) in rows})
print('\nT1  gap = log(ratio_prime / ratio_composite); shift = log(transplanted prime / prime) (same rows); resid = log(transplanted / composite)')
print('| B | m | prime rows | ratio prime | ratio composite | gap | shift (composite masks) | resid |')
print('|---|---|---|---|---|---|---|---|')
for (B, m), r in sorted(rows.items(), key=lambda x: (BS.index(x[0][0]), x[0][1])):
    sh = f"{r['composite_shift']:+.3f} ± {r['composite_shift_se']:.3f}" if 'composite_shift' in r else '–'
    rs = f"{r['composite_resid']:+.3f} ± {r['composite_resid_se']:.3f}" if 'composite_resid' in r else '–'
    print(f"| {B} | {m:.2f} | {r['nP']} | {r['rp']:.3f} | {r['rc']:.3f} | {r['gap']:+.3f} ± {r['gap_se']:.3f} | {sh} | {rs} |")
print('\nT1 pooled over disjoint B sets ' + ', '.join(POOL))
print('| m | B used | gap | shift | resid | gap vs min-7 | shift (q=7 masks) | resid vs min-7 |')
print('|---|---|---|---|---|---|---|---|')
for m in allm:
    keys = [(B, m) for B in POOL if (B, m) in rows and 'composite_shift' in rows[(B, m)]]
    if not keys:
        continue
    g = pooled(keys, 'gap'); s = pooled(keys, 'composite_shift'); rr = pooled(keys, 'composite_resid')
    g7 = pooled(keys, 'gap7'); s7 = pooled(keys, 'min7_shift'); r7 = pooled(keys, 'min7_resid')
    print(f"| {m:.2f} | {','.join(k[0] for k in keys)} | {g[0]:+.3f} ± {g[1]:.3f} | {s[0]:+.3f} ± {s[1]:.3f} | {rr[0]:+.3f} ± {rr[1]:.3f} "
          f"| {g7[0]:+.3f} ± {g7[1]:.3f} | {s7[0]:+.3f} ± {s7[1]:.3f} | {r7[0]:+.3f} ± {r7[1]:.3f} |")
print('\nT2  ratio actual/surrogate by the 3-part of the conductor (all rows): c = 0 (k = 0, conductor u), c = 1 (k = 3, (1-w)u), c = 2 (3u)')
print('| B | m | c = 0 | c = 1 | c = 2 |')
print('|---|---|---|---|---|')
for (B, m), r in sorted(rows.items(), key=lambda x: (BS.index(x[0][0]), x[0][1])):
    print(f"| {B} | {m:.2f} | {r['c0']:.3f} ± {r['c0_se']:.3f} | {r['c1']:.3f} ± {r['c1_se']:.3f} | {r['c2']:.3f} ± {r['c2_se']:.3f} |")
json.dump({f'{k[0]}_{k[1]}': v for k, v in rows.items()}, open(os.path.join(L, 'summary_rows.json'), 'w'), indent=1, default=float)
