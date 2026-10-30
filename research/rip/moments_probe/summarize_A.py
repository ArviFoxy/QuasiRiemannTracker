"""Compact markdown summary of the probe A runs (fitted eta per pair class, zeta, diagonal ratio) incl. surrogate nulls.

usage: python3 -I summarize_A.py [--kfit=700]
"""
import sys, os, glob, math
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import analyzeA as A

kfit = 700.0
for a in sys.argv[1:]:
    if a.startswith('--kfit='):
        kfit = float(a.split('=')[1])
RES = os.path.join(HERE, 'results')

runs = [
    ('exact g~, W=(1-u)+, c=1, 10 primes (norms 7,7,13,13,19,19,31,31,37,37)', 'A_true_lin_K20000_np10.npz'),
    ('exact g~, W=(1-u)+, c=1, 20 primes (norms up to 79)', 'A_true_lin_K20000_np20.npz'),
    ('exact g~, W=(1-u)+^2, c=1, 10 primes', 'A_true_sq_K20000_np10.npz'),
    ('exact g~, W=smooth bump, c=1, 10 primes', 'A_true_bump_K20000_np10.npz'),
    ('exact g~, W=(1-u)+, c=1/4 (window N=K N(P)/4)', 'A_true_lin_c025_K20000_np10.npz'),
    ('exact g~, W=(1-u)+, c=4 (window N=4 K N(P))', 'A_true_lin_c4_K20000_np10.npz'),
    ('exact g~, W=(1-u)+, c=1, 10 primes, K up to 5e4 (fit K>=1000)', 'A_true_lin_K50000_np10.npz'),
]
print(f'### fitted eta (rho ~ K^-eta, K >= {kfit:.0f}); zeta = rms(rho) sqrt(R) over the fit range; [lo,hi] = pair-bootstrap 95%\n')
print('| run | Kmax | R(Kmax) | G_PP/(R D_P) at Kmax | eta all | eta diff | eta conj | zeta diff | zeta conj |')
print('|---|---:|---:|---:|---:|---:|---:|---:|---:|')
for name, fn in runs:
    path = os.path.join(RES, fn)
    if not os.path.exists(path):
        continue
    d = A.load(path)
    kf = 1000.0 if 'K50000' in fn else kfit
    f = A.fits(d, kf, nboot=300)
    R = d['R']; K = d['K']
    dg = np.real(np.einsum('kii->ki', d['G'])); dd = R[:, None] * np.real(np.einsum('kii->ki', d['Dcross']))
    def e(c):
        return f'{f[c]["eta_mean"]:.3f} [{f[c]["lo"]:.2f},{f[c]["hi"]:.2f}]' if c in f else 'n/a'
    def z(c):
        return f'{f[c]["zeta_mean_fit"]:.2f}' if c in f else 'n/a'
    print(f'| {name} | {int(K[-1])} | {int(R[-1])} | {np.mean(dg[-1]/dd[-1]):.3f} | {e("all")} | {e("diff")} | {e("conj")} | {z("diff")} | {z("conj")} |')

print('\n### surrogate nulls (10 replicas each, same rows/columns/K-grid, 10 primes; mean +- sd over replicas)\n')
print('| surrogate | eta all | eta diff | eta conj | zeta diff | zeta conj | G_PP/(R D_P) at Kmax |')
print('|---|---:|---:|---:|---:|---:|---:|')
for name, pat in [('i.i.d. random phases', 'A_randphase_lin_K20000_np10_r*.npz'),
                  ('random cube roots at primes (twisted mult. kept)', 'A_randcube_lin_K20000_np10_r*.npz'),
                  ('i.i.d. phases with g~(conj n)=conj g~(n)', 'A_randphasesym_lin_K20000_np10_r*.npz'),
                  ('random cube roots with g~(conj pi)=conj g~(pi)', 'A_randcubesym_lin_K20000_np10_r*.npz')]:
    files = sorted(glob.glob(os.path.join(RES, pat)))
    if not files:
        continue
    st = {}
    dr = []
    for fn in files:
        d = A.load(fn)
        for c, v in A.fits(d, kfit).items():
            st.setdefault(c, []).append(v)
        R = d['R']; dg = np.real(np.einsum('kii->ki', d['G'])); dd = R[:, None] * np.real(np.einsum('kii->ki', d['Dcross']))
        dr.append(np.mean(dg[-1] / dd[-1]))
    def ms(c, key):
        v = np.array([x[key] for x in st[c]]); return f'{v.mean():.3f} +- {v.std(ddof=1):.3f}'
    print(f'| {name} ({len(files)}) | {ms("all","eta_mean")} | {ms("diff","eta_mean")} | {ms("conj","eta_mean")} | {ms("diff","zeta_mean_fit")} | {ms("conj","zeta_mean_fit")} | {np.mean(dr):.3f} +- {np.std(dr, ddof=1):.3f} |')
