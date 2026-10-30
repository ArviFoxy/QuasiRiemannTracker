"""Analysis of probe A results (output of probeA.py).

usage: python3 -I analyzeA.py FILE.npz [FILE2.npz ...] [--kfit=700] [--boot=400] [--pairs]
       python3 -I analyzeA.py --null 'results/A_randphase_lin_K20000_np10_r*.npz' [--kfit=700]
For each file: diagonal ratios, rho_{PP'}(K) by pair class, fitted eta (rho ~ K^-eta), checks.
Pair classes:  'conj'  = (P, Pbar) the two primes above one rational prime;
               'diff'  = primes above different rational primes (both relative orientations are included;
                         G_{Pbar Pbar'} = conj G_{PP'}, so |rho| is invariant under simultaneous conjugation);
               'all'   = every pair P != P'.
rho = |G_{PP'}| / sqrt(G_PP G_P'P') with G the cumulative sum over rows N(k) <= K.  Random behaviour: E rho^2 = 1/R(K),
i.e. zeta = rho sqrt(R) = O(1) and eta = 1/2.  No decay: eta = 0.
--null aggregates the fits over the replicas of a surrogate (null calibration of the fitted eta and of zeta).
"""
import sys, os, math, glob
sys.dont_write_bytecode = True
import numpy as np

rng = np.random.default_rng(12345)


def ols(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    xm, ym = x.mean(), y.mean()
    sxx = np.sum((x - xm) ** 2)
    b = np.sum((x - xm) * (y - ym)) / sxx
    a = ym - b * xm
    res = y - (a + b * x)
    se = math.sqrt(np.sum(res ** 2) / max(1, len(x) - 2) / sxx) if len(x) > 2 else float('nan')
    return b, a, se


def load(fn):
    d = np.load(fn, allow_pickle=True)
    return {k: d[k] for k in d.files}


def pair_lists(PN):
    n = len(PN)
    conj, diff = [], []
    for i in range(n):
        for j in range(i + 1, n):
            (conj if PN[i] == PN[j] else diff).append((i, j))
    return conj, diff


def rho_matrix(G):
    d = np.real(np.diagonal(G, axis1=-2, axis2=-1))
    return np.abs(G) / np.sqrt(d[..., :, None] * d[..., None, :])


def class_series(d):
    """rho series per class: dict name -> array (nK x npairs); also the dyadic-block version."""
    G, Gh, PN = d['G'], d['Ghalf'], d['PN']
    conj, diff = pair_lists(PN)
    rho, rhh = rho_matrix(G), rho_matrix(Gh)
    out = {}
    for name, pl in (('conj', conj), ('diff', diff), ('all', conj + diff)):
        if pl:
            out[name] = (np.array([[rho[i, a, b] for (a, b) in pl] for i in range(len(G))]),
                         np.array([[rhh[i, a, b] for (a, b) in pl] for i in range(len(G))]), pl)
    return out


def fits(d, kfit, nboot=0):
    K = d['K'].astype(float); R = d['R'].astype(float)
    m = K >= kfit
    lk = np.log(K[m]); lR = np.log(R[m])
    res = {}
    for name, (r, rh, pl) in class_series(d).items():
        e_mean = -ols(lk, np.log(r[m].mean(1)))[0]
        e_rms = -ols(lk, np.log(np.sqrt((r[m] ** 2).mean(1))))[0]
        e_R = -ols(lR, np.log(r[m].mean(1)))[0]
        e_h = -ols(lk, np.log(rh[m].mean(1)))[0]
        zeta = np.sqrt((r ** 2).mean(1)) * np.sqrt(R)                 # rms over pairs of rho*sqrt(R), per K
        single = np.array([-ols(lk, np.log(r[m][:, j]))[0] for j in range(len(pl))])
        rec = dict(eta_mean=e_mean, eta_rms=e_rms, eta_R=e_R, eta_half=e_h, zeta=zeta, zeta_mean_fit=float(zeta[m].mean()),
                   single_med=float(np.median(single)), n=len(pl))
        if nboot:
            bs = []
            for _ in range(nboot):
                idx = rng.integers(0, len(pl), len(pl))
                bs.append(-ols(lk, np.log(r[m][:, idx].mean(1)))[0])
            rec['lo'], rec['hi'] = np.percentile(bs, [2.5, 97.5])
        res[name] = rec
    return res


def analyze(fn, kfit, nboot, showpairs):
    d = load(fn)
    K = d['K'].astype(float); R = d['R'].astype(float); G = d['G']; Dc = d['Dcross']
    PN = d['PN']; nP = len(PN); nK = len(K)
    print('=' * 100)
    print(fn, '|', str(d['meta']))
    print(f'primes P (norms): {[int(x) for x in PN]}   K grid: {[int(x) for x in K]}')
    conj, diff = pair_lists(PN)
    allp = conj + diff
    dg = np.real(np.einsum('kii->ki', G))
    dd = R[:, None] * np.real(np.einsum('kii->ki', Dc))
    ratio = dg / dd
    print('\n[diagonal]  G_PP(K) / (R(K) D_P(K)),  D_P = sum_n W_P(n)^2 [P not| n]   and   G_PP/(K^2 N(P))')
    print('   K      R    cols(max)  ratio mean [min,max]    G_PP/(K^2 N(P)) mean')
    for i in range(nK):
        print(f'{int(K[i]):6d} {int(R[i]):6d} {int(d["ncol"][i]):9d}   {ratio[i].mean():.3f} [{ratio[i].min():.3f},{ratio[i].max():.3f}]'
              f'      {np.mean(dg[i]/(K[i]**2*PN)):.4f}')
    m = K >= kfit
    s_diag = ols(np.log(K[m]), np.log(dg[m].mean(1)))[0]
    s_ratio = ols(np.log(K[m]), np.log(ratio[m].mean(1)))[0]
    print(f'   fit (K>={kfit:.0f}): mean_P G_PP ~ K^{s_diag:.3f} (prediction ~K^2 up to R(K)/K drift);  G_PP/(R D_P) ~ K^{s_ratio:+.3f}')
    rho = rho_matrix(G)
    print('\n[rho_{PP\'}(K)]  class mean of |rho|, and zeta = rms(rho)*sqrt(R)  (random: zeta ~ 1)')
    print('   K      R  |  conj: mean   zeta |  diff: mean   zeta |  all: mean   zeta  |  offdiag-only(all) mean  zeta  |  |Gdiag|/|G| (all, median)')
    for i in range(nK):
        row = []
        for name, pl in (('conj', conj), ('diff', diff), ('all', allp)):
            if pl:
                r = np.array([rho[i, a, b] for a, b in pl])
                row += [r.mean(), math.sqrt(np.mean(r ** 2)) * math.sqrt(R[i])]
            else:
                row += [float('nan')] * 2
        Goff = G[i] - R[i] * Dc[i]
        roff = np.array([abs(Goff[a, b]) / math.sqrt(dg[i][a] * dg[i][b]) for a, b in allp])
        rdiag = np.array([abs(R[i] * Dc[i][a, b]) / abs(G[i][a, b]) for a, b in allp])
        print(f'{int(K[i]):6d} {int(R[i]):6d} |  {row[0]:.4f} {row[1]:6.3f} |  {row[2]:.4f} {row[3]:6.3f} |  {row[4]:.4f} {row[5]:6.3f}  |'
              f'  {roff.mean():.4f} {math.sqrt(np.mean(roff**2))*math.sqrt(R[i]):6.3f}  |  {np.median(rdiag):.3f}')
    print(f'\n[fit]  rho ~ K^-eta  over K >= {kfit:.0f} ({int(m.sum())} grid points); [lo,hi]: pair bootstrap 95% interval')
    print('   class   n_pairs   eta(mean rho)   eta(rms rho)   eta vs R(K)   median single-pair eta   eta(dyadic-block G)   mean zeta (fit range)')
    fr = fits(d, kfit, nboot)
    for name in ('conj', 'diff', 'all'):
        if name in fr:
            f = fr[name]
            print(f'   {name:6s} {f["n"]:5d}      {f["eta_mean"]:6.3f} [{f["lo"]:5.3f},{f["hi"]:5.3f}]   {f["eta_rms"]:6.3f}       {f["eta_R"]:6.3f}        '
                  f'{f["single_med"]:6.3f}                  {f["eta_half"]:6.3f}               {f["zeta_mean_fit"]:.3f}')
    print('\n[normalised Gram matrix  Gn = D^-1/2 G D^-1/2]  lambda_max(Gn) - 1 vs random prediction 2 sqrt(nP/R) + nP/R')
    for i in range(nK):
        Dm = np.real(np.diag(G[i])) ** -0.5
        Gn = Dm[:, None] * G[i] * Dm[None, :]
        lam = np.linalg.eigvalsh((Gn + Gn.conj().T) / 2)
        rp = 2 * math.sqrt(nP / R[i]) + nP / R[i]
        if i % 2 == 1 or i == nK - 1:
            print(f'   K={int(K[i]):6d} R={int(R[i]):5d}  lambda_max-1 = {lam[-1]-1:.4f}   random ~ {rp:.4f}   ratio {(lam[-1]-1)/rp:.2f}'
                  f'   lambda_min = {lam[0]:.4f}')
    if showpairs:
        i = nK - 1
        print(f'\n[pairs at K={int(K[i])}]   (P,P\')  norms   rho   zeta=rho sqrt(R)   phase(G)/pi   R*Dcross/G')
        for (a, b) in allp:
            print(f'   ({a},{b})  ({PN[a]},{PN[b]})  {rho[i,a,b]:.4f}  {rho[i,a,b]*math.sqrt(R[i]):.3f}  '
                  f'{np.angle(G[i][a,b])/math.pi:+.3f}  {abs(R[i]*Dc[i][a,b]/G[i][a,b]):.3f}')
    return fr


def null_summary(pattern, kfit):
    files = sorted(glob.glob(pattern))
    print('=' * 100)
    print(f'null calibration: {len(files)} replicas of {pattern}')
    store = {}
    diag = []
    for fn in files:
        d = load(fn)
        fr = fits(d, kfit)
        for name, f in fr.items():
            store.setdefault(name, []).append(f)
        K = d['K'].astype(float); R = d['R'].astype(float)
        dg = np.real(np.einsum('kii->ki', d['G'])); dd = R[:, None] * np.real(np.einsum('kii->ki', d['Dcross']))
        diag.append((dg / dd).mean(1))
    K = d['K'].astype(float); m = K >= kfit
    print(f'   (K>={kfit:.0f}); each entry: mean +- sd over replicas')
    print('   class  n_pairs  eta(mean rho)    eta(rms rho)     eta vs R      mean zeta (fit range)    zeta at K_max')
    for name in ('conj', 'diff', 'all'):
        if name in store:
            L = store[name]
            def ms(key):
                v = np.array([x[key] for x in L]); return f'{v.mean():6.3f} +- {v.std(ddof=1):.3f}'
            zk = np.array([x['zeta'][-1] for x in L])
            print(f'   {name:6s} {L[0]["n"]:5d}   {ms("eta_mean")}   {ms("eta_rms")}   {ms("eta_R")}   {ms("zeta_mean_fit")}     {zk.mean():.3f} +- {zk.std(ddof=1):.3f}')
    dm = np.array(diag)
    print('   diagonal ratio G_PP/(R D_P) at K_max: %.3f +- %.3f;  slope in log K over fit range: %.3f' %
          (dm[:, -1].mean(), dm[:, -1].std(ddof=1), np.mean([ols(np.log(K[m]), np.log(x[m]))[0] for x in dm])))
    return store


def normdep(fn, kfit):
    """dependence of the cross-correlation and of the diagonal ratio on the norms N(P), N(P')."""
    d = load(fn)
    K = d['K'].astype(float); R = d['R'].astype(float); G = d['G']; Dc = d['Dcross']; PN = d['PN']
    m = K >= kfit
    rho = rho_matrix(G)
    conj, diff = pair_lists(PN)
    pl = conj + diff
    prod = np.array([PN[a] * PN[b] for a, b in pl], float)
    z2 = np.array([np.mean([(rho[i, a, b] ** 2) * R[i] for i in np.flatnonzero(m)]) for a, b in pl])      # mean zeta^2 over fit range
    order = np.argsort(prod)
    print('=' * 100)
    print(fn, f': dependence on N(P) N(P\'), pairs sorted by the product; mean zeta^2 over K >= {kfit:.0f} (random: 1)')
    for chunk in np.array_split(order, 5):
        print(f'   N(P)N(P\') in [{prod[chunk].min():.0f}, {prod[chunk].max():.0f}]  ({len(chunk)} pairs)   mean zeta^2 = {z2[chunk].mean():.3f}   '
              f'(conj pairs among them: {sum(1 for j in chunk if j < len(conj))})')
    cc = np.corrcoef(np.log(prod), np.log(z2))[0, 1]
    print(f'   corr(log N(P)N(P\'), log zeta^2) = {cc:+.3f};  slope of log zeta^2 vs log(N(P)N(P\')) = {np.polyfit(np.log(prod), np.log(z2), 1)[0]:+.3f}')
    dg = np.real(np.einsum('kii->ki', G)); dd = R[:, None] * np.real(np.einsum('kii->ki', Dc))
    ratio = (dg / dd)[m].mean(0)
    print('   diagonal ratio G_PP/(R D_P) averaged over the fit range, per P (norm):', ' '.join(f'{int(n)}:{r:.3f}' for n, r in zip(PN, ratio)))
    print(f'   slope of log(diag ratio) vs log N(P): {np.polyfit(np.log(PN.astype(float)), np.log(ratio), 1)[0]:+.3f}')


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opts = {a.split('=')[0]: (a.split('=')[1] if '=' in a else True) for a in sys.argv[1:] if a.startswith('--')}
    kfit = float(opts.get('--kfit', 700)); nboot = int(opts.get('--boot', 400))
    if '--normdep' in opts:
        for fn in args:
            normdep(fn, kfit)
    elif '--null' in opts:
        for pat in args:
            null_summary(pat, kfit)
    else:
        for fn in args:
            analyze(fn, kfit, nboot, '--pairs' in opts)
