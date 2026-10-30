"""Tables for the prime/composite study from a primerows_run.py .npz.
  (1) classes prime / composite / comp_small / comp_large: M2, M6 actual and surrogate (K-replica mean), ratio with
      bootstrap se over conjugate-pair clusters (surrogate per-row means resampled with their rows), spread over
      replica groups, and z of the prime-minus-composite log-ratio;
  (2) split by the 3-part of the conductor (kres = ((N(u)-1)/6) mod 6: c = 0 for k = 0, c = 1 for k = 3, c = 2 else);
  (3) split by the smallest factor of composite rows;
  (4) shape: M6/M2^3 per class (actual and surrogate), and the per-row-normalised M6 (|S_u|^2 divided by the
      surrogate's per-row E|S_u|^2, i.e. the mask-dependent diagonal);
  (5) null: the ratio computed with a surrogate replica in place of the actual (rows u and u-bar given identical values).
usage: python3 -I primerows_analyze.py logsP/run_3e5.npz [--sections 1 2 3 4 5]
"""
import sys, os, argparse
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import primerows_core as PC

ap = argparse.ArgumentParser()
ap.add_argument('npz')
ap.add_argument('--sections', type=int, nargs='+', default=[1, 2, 3, 4, 5])
ap.add_argument('--nb', type=int, default=1000)
a = ap.parse_args()
d = np.load(a.npz)
ms = d['ms']; K = int(d['K']); mass = d['mass']
S = d['S']; a2 = (np.abs(S) ** 2 / mass).astype(np.float64)
acc = d['acc']                      # R x nm x 3 x groups (sums over replicas)
G = acc.shape[-1]
s2 = acc[:, :, 0, :].sum(-1) / K; s4 = acc[:, :, 1, :].sum(-1) / K; s6 = acc[:, :, 2, :].sum(-1) / K
nf = d['nf']; kres = d['kres']; minn = d['minnorm']; conj = d['conj']
cl = PC.pair_clusters(conj)
R = len(nf)
rng = np.random.default_rng(1)
print(f"file {a.npz}: B={int(d['B'])} R={R} K={K} weight={d['weight']} rough={int(d['rough'])} maxsrc={int(d['maxsrc'])} nS={int(d['nS'])}")
cls = dict(prime=nf == 1, composite=nf >= 2, comp_small=(nf >= 2) & (minn <= 200), comp_large=(nf >= 2) & (minn > 200))


def ratio_line(sel, im, label):
    a6 = a2[sel, im] ** 3; t6 = s6[sel, im]
    r, se, bs = PC.boot_ratio(a2[:, im] ** 3, s6[:, im], cl, nb=a.nb, rng=rng, sel=sel)
    grp = [acc[sel, im, 2, g].mean() / (K / G) for g in range(G)]
    gsd = np.std(grp, ddof=1) / np.sqrt(G) / np.mean(grp) if G > 1 else np.nan
    return dict(label=label, n=int(sel.sum()), M2a=a2[sel, im].mean(), M2s=s2[sel, im].mean(), M6a=a6.mean(), M6s=t6.mean(),
                r=r, se=se, gsd=gsd, bs=bs)


def show(rows):
    print('   class                 n   M2 act/sur     M6 act   M6 sur   ratio  (boot se, grp rel-sd of sur)')
    for x in rows:
        print(f"   {x['label']:18s} {x['n']:6d}  {x['M2a']:.3f}/{x['M2s']:.3f}   {x['M6a']:7.3f}  {x['M6s']:7.3f}   {x['r']:.3f}  ({x['se']:.3f}, {x['gsd']:.3f})")


def zdiff(x, y):
    lx = np.log(x['bs']); ly = np.log(y['bs'])
    D = np.log(x['r']) - np.log(y['r'])
    return D, np.sqrt(np.var(lx) + np.var(ly))


if 1 in a.sections:
    print('\n(1) classes')
    for im, m in enumerate(ms):
        print(f' m={m}')
        L = [ratio_line(cls[c], im, c) for c in cls]
        show(L)
        D, sd = zdiff(L[0], L[1])
        print(f'   log(ratio_prime) - log(ratio_comp) = {D:+.3f} +- {sd:.3f}  (z = {D/sd:+.2f})')

if 2 in a.sections:
    print('\n(2) split by the 3-part of the conductor: c = 0 (k=0), c = 1 (k=3), c = 2 (k=1,2,4,5)')
    cexp = np.where(kres == 0, 0, np.where(kres == 3, 1, 2))
    for im, m in enumerate(ms):
        print(f' m={m}')
        L = []
        for c in (0, 1, 2):
            for nm in ('prime', 'composite'):
                L.append(ratio_line(cls[nm] & (cexp == c), im, f'c={c} {nm}'))
            L.append(ratio_line(cexp == c, im, f'c={c} all'))
        show(L)
        for c in (0, 1, 2):
            D, sd = zdiff(L[3 * c], L[3 * c + 1])
            print(f'   c={c}: log ratio prime - comp = {D:+.3f} +- {sd:.3f}')

if 3 in a.sections:
    print('\n(3) by smallest factor norm (composite rows) vs prime rows')
    bins = [(7, 7), (13, 13), (19, 19), (25, 25), (31, 43), (49, 100), (101, 200), (201, 10 ** 9)]
    for im, m in enumerate(ms):
        print(f' m={m}')
        L = [ratio_line(cls['prime'], im, 'prime')]
        for lo, hi in bins:
            sel = (nf >= 2) & (minn >= lo) & (minn <= hi)
            if sel.sum() >= 200:
                L.append(ratio_line(sel, im, f'min N in [{lo},{hi}]'))
        show(L)

if 4 in a.sections:
    # per-row normalisation: the exact masked diagonal 'diag' if the run file has it; otherwise the K-replica estimate of
    # E|S_u|^2, which is noisy and biases 'M6(norm)' upward (Jensen) -- only the exact version is meaningful.
    dn = d['diag'] if 'diag' in d.files else s2
    print('\n(4) shape: M6/M2^3 per class, and M6 of |S_u|^2 / E|S_u|^2 (per-row diagonal normalisation; '
          + ('exact diagonal)' if 'diag' in d.files else 'K-replica estimate: BIASED, see primerows_normcheck.py)'))
    print('   m     class        act M6/M2^3  sur M6/M2^3   act M6(norm)  sur M6(norm)  ratio(norm)')
    for im, m in enumerate(ms):
        for c in ('prime', 'composite', 'comp_small', 'comp_large'):
            sel = cls[c]
            sa = (a2[sel, im] ** 3).mean() / a2[sel, im].mean() ** 3
            ss = s6[sel, im].mean() / s2[sel, im].mean() ** 3
            an = a2[sel, im] / dn[sel, im]
            sn = s6[sel, im] / dn[sel, im] ** 3
            print(f'   {m:.2f}  {c:11s}  {sa:8.3f}     {ss:8.3f}      {(an**3).mean():8.3f}     {sn.mean():8.3f}     {(an**3).mean()/sn.mean():.3f}')

if 5 in a.sections and d['kept'].size:
    print('\n(5) null: a surrogate replica (u-bar given u\'s value) in place of the actual, divided by the K-replica mean')
    kept = d['kept'].astype(np.float64)
    rep = np.minimum(np.arange(R), conj)          # representative row of each pair
    for im, m in enumerate(ms):
        out = []
        for q in range(kept.shape[0]):
            v = kept[q, rep, im] ** 3
            rp = v[cls['prime']].mean() / s6[cls['prime'], im].mean()
            rc = v[cls['composite']].mean() / s6[cls['composite'], im].mean()
            out.append((rp, rc, np.log(rp) - np.log(rc)))
        out = np.array(out)
        print(f'   m={m}: null ratios prime {np.round(out[:,0],3)}  comp {np.round(out[:,1],3)}  log-diff {np.round(out[:,2],3)}')
