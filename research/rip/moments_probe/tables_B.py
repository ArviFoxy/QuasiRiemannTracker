"""Tables and fits for probe B from the JSON files written by probeB.py.

usage: python3 -I tables_B.py results/B_main.json [results/B_mext.json ...]
Prints (markdown) the M4 / M6 tables of the actual family against the comparators, the B-scaling fits at fixed m, and the
fitted coefficient c of the N-term, M6 = M6(mult) + c * N^3/R   (c = 1 * 0.064/0.28-ish in the full family, see README).
"""
import sys, json, math
sys.dont_write_bytecode = True
import numpy as np


def load(files):
    recs = []
    for fn in files:
        d = json.load(open(fn))
        nrep = d['args']['nrep']
        for r in d['results']:
            r['nrep'] = nrep
            r['file'] = fn
            recs.append(r)
    return recs


def mean_sd(r, prefix, key):
    v = np.array([r[f'{prefix}{i}'][key] for i in range(r['nrep'])])
    return v.mean(), (v.std(ddof=1) if len(v) > 1 else float('nan'))


def fmt(x, w=7, p=3):
    return f'{x:{w}.{p}f}' if x is not None and not (isinstance(x, float) and math.isnan(x)) else ' ' * (w - 3) + 'n/a'


def md_table(recs, mom):
    ex = 2 if mom == 'M4' else 3
    tk = 'T4N2' if mom == 'M4' else 'T6N3'
    fk = 'full_M4' if mom == 'M4' else 'full_M6'
    se = 'se4' if mom == 'M4' else 'se6'
    print(f'| B | m | N | #n | R | N^{ex}/R | {mom} actual (se) | {mom} mult (sd) | {mom} iid | T/N^{ex} | {mom} full mod q | actual/mult | z |')
    print('|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for r in recs:
        a = r['actual']
        mm, ms = mean_sd(r, 'mult', mom); im, _ = mean_sd(r, 'iid', mom)
        sep = math.sqrt(a[se] ** 2 + ms ** 2 / r['nrep'])
        t = r[tk]
        print(f"| {r['B']} | {r['m']:.2f} | {r['N']:.1f} | {r['C']} | {r['R']} | {r['N']**ex/r['R']:.2f} | {a[mom]:.3f} ({a[se]:.3f}) | "
              f"{mm:.3f} ({ms:.3f}) | {im:.3f} | {fmt(t, 5, 3) if t is not None else 'n/a'} | {fmt(r[fk], 5, 2)} | {a[mom]/mm:.3f} | {(a[mom]-mm)/sep:+.1f} |")


def wls(x, y, s):
    w = 1.0 / np.asarray(s) ** 2
    X = np.vstack([np.ones_like(x), x]).T
    A = X.T @ (X * w[:, None])
    b = X.T @ (w * y)
    cov = np.linalg.inv(A)
    beta = cov @ b
    return beta, np.sqrt(np.diag(cov))


def scaling(recs, mom='M6', bmin=12000):
    print(f'\nB-scaling at fixed m (B >= {bmin}): slope of log {mom}(actual), of log {mom}(mult), of log ratio actual/mult in log B; '
          f'the N-term would give slope 3m-1 (M6) or 2m-1 (M4) at least once it dominates')
    print('| m | #B | slope log M(actual) | slope log M(mult) | slope log(actual/mult) | 3m-1 | ratio actual/mult at largest B |')
    print('|---:|---:|---:|---:|---:|---:|---:|')
    se = 'se4' if mom == 'M4' else 'se6'
    for m in sorted({r['m'] for r in recs}):
        rr = sorted([r for r in recs if r['m'] == m and r['B'] >= bmin], key=lambda r: r['B'])
        if len(rr) < 3:
            continue
        lb = np.log([r['B'] for r in rr])
        ya = np.log([r['actual'][mom] for r in rr]); sa = np.array([r['actual'][se] / r['actual'][mom] for r in rr])
        ym = np.log([mean_sd(r, 'mult', mom)[0] for r in rr]); sm = np.array([mean_sd(r, 'mult', mom)[1] / math.sqrt(r['nrep']) / mean_sd(r, 'mult', mom)[0] for r in rr])
        yr = ya - ym; sr = np.sqrt(sa ** 2 + sm ** 2)
        (ba, sla), (bm, slm), (br, slr) = [(wls(lb, y, s)[0][1], wls(lb, y, s)[1][1]) for y, s in ((ya, sa), (ym, sm), (yr, sr))]
        print(f'| {m:.2f} | {len(rr)} | {ba:+.3f} +- {sla:.3f} | {bm:+.3f} +- {slm:.3f} | {br:+.3f} +- {slr:.3f} | {3*m-1:+.2f} | {math.exp(yr[-1]):.3f} |')


def nterm(recs, mom='M6', nmin=30.0):
    ex = 2 if mom == 'M4' else 3
    se = 'se4' if mom == 'M4' else 'se6'
    pts = [r for r in recs if r['N'] ** ex / r['R'] >= nmin]
    x = np.array([r['N'] ** ex / r['R'] for r in pts])
    y = np.array([r['actual'][mom] - mean_sd(r, 'mult', mom)[0] for r in pts])
    s = np.array([math.sqrt(r['actual'][se] ** 2 + mean_sd(r, 'mult', mom)[1] ** 2 / r['nrep']) for r in pts])
    w = 1 / s ** 2
    c = np.sum(w * x * y) / np.sum(w * x * x)
    sc = 1 / math.sqrt(np.sum(w * x * x))
    print(f'\nN-term coefficient: {mom}(actual) - {mom}(mult) = c * N^{ex}/R through the origin, {len(pts)} points with N^{ex}/R >= {nmin}: '
          f'c = {c:+.2e} +- {sc:.1e}   (the full Dirichlet family has c = 1: positive control column "full")')
    xs = {}
    for r in pts:
        xs.setdefault(r['m'], []).append(r)
    for m in sorted(xs):
        rr = xs[m]
        xx = np.array([r['N'] ** ex / r['R'] for r in rr]); yy = np.array([r['actual'][mom] - mean_sd(r, 'mult', mom)[0] for r in rr])
        ss = np.array([math.sqrt(r['actual'][se] ** 2 + mean_sd(r, 'mult', mom)[1] ** 2 / r['nrep']) for r in rr]); ww = 1 / ss ** 2
        print(f'   m={m:.2f}: c = {np.sum(ww*xx*yy)/np.sum(ww*xx*xx):+.2e} +- {1/math.sqrt(np.sum(ww*xx*xx)):.1e}   ({len(rr)} points, N^{ex}/R up to {xx.max():.0f})')


if __name__ == '__main__':
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    recs = load(files)
    recs.sort(key=lambda r: (r['m'], r['B']))
    byB = sorted(recs, key=lambda r: (r['B'], r['m']))
    for mom in ('M6', 'M4'):
        print(f'\n### {mom}\n')
        md_table(byB, mom)
    scaling(recs, 'M6'); scaling(recs, 'M4')
    nterm(recs, 'M6'); nterm(recs, 'M4', nmin=3.0)
    print('\nlargest |S_u|^2/N over rows (actual vs multiplicative surrogate, mean over replicas):')
    for r in byB:
        if r['B'] >= 96000:
            mx = np.mean([r[f'mult{i}']['maxS2'] for i in range(r['nrep'])])
            print(f"   B={r['B']:7d} m={r['m']:.2f}  max|S|^2/N actual {r['actual']['maxS2']:.2f}  mult {mx:.2f}   (C={r['C']}, N={r['N']:.0f})")
