"""Figure: three face systems for the energy region.
(a) dual plane (Lam, B): chain faces, continuum face curve, outer limit B = 1, pursuit targets (kappa, kappa);
(b) primal plane (s, m1+m2): envelopes and the ideal line, scaled ideal lines;
(c) E_inf(s) - E_chain(s)."""
import os, sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from faces import load_faces

INK, INK2, GRID, SURF = '#0b0b0b', '#52514e', '#e4e3df', '#fcfcfb'
C_CHAIN, C_CONT, C_TGT = '#2a78d6', '#eb6834', '#1baf7a'

def q_of(B, L): return min(0.999*L/(6*B - L), 0.75)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
steps, F = load_faces()
FB = np.array([[float(f[1]), float(f[0]), float(f[2])] for f in F])      # Lam, B, cap
sol = solve_ivp(lambda L, y: [(y[0] - kappa(q_of(y[0], L)))/(L - kappa(q_of(y[0], L)))], [2.5715, 1.926072],
                [0.99999], method='DOP853', rtol=1e-12, atol=1e-14, dense_output=True)
Lc = np.linspace(2.5715, 1.926072, 2000); Bc = sol.sol(Lc)[0]

plt.rcParams.update({'font.size': 10, 'axes.edgecolor': INK2, 'axes.labelcolor': INK, 'xtick.color': INK2,
                     'ytick.color': INK2, 'axes.facecolor': SURF, 'figure.facecolor': SURF})
fig, ax = plt.subplots(1, 3, figsize=(15, 4.9), gridspec_kw={'width_ratios': [1.25, 1.1, 0.9]})

# (a) dual plane
a = ax[0]
a.axhline(1.0, color=INK2, lw=1.2, ls='--')
a.text(1.02, 1.0035, 'outer limit B = 1 (the ideal faces)', color=INK2, fontsize=9)
a.plot([0.86, 1.0], [0.86, 1.0], color=GRID, lw=1)
qs = np.linspace(0.75, 0.5, 50); ks = kappa(qs)
a.plot(ks, ks, color=C_TGT, lw=4, solid_capstyle='round')
a.text(0.93, 0.885, 'targets (κ, κ)\nq = 3/4 → 1/2', color=INK, fontsize=9)
a.plot(FB[::3, 0], FB[::3, 1], 'o', ms=5, mfc='none', mec=C_CHAIN, mew=1, label='chain faces (every 3rd of 130)')
a.plot(Lc, Bc, color=C_CONT, lw=2, label='continuum face curve B∞ (exact)')
for L in [2.55, 2.25, 1.95]:
    B = float(sol.sol(L)[0]); k = kappa(q_of(B, L))
    a.annotate('', xy=(k, k), xytext=(L, B), arrowprops=dict(arrowstyle='->', color=INK2, lw=0.8, alpha=0.7))
a.set_xlim(0.85, 2.65); a.set_ylim(0.86, 1.016)
a.set_xlabel('Λ  (price of slot length)'); a.set_ylabel('B')
a.set_title('(a) face body: each step heads for (κ(q), κ(q))', color=INK, fontsize=10.5, loc='left')
a.grid(color=GRID, lw=0.6); a.legend(loc='lower right', frameon=False, fontsize=9)

# (b) primal plane
b = ax[1]
s = np.linspace(0, 0.1, 801)
Ech = np.max(FB[None, :, 1] - FB[None, :, 0]*s[:, None], axis=1)
Einf = np.max(Bc[None, :] - Lc[None, :]*s[:, None], axis=1)
b.plot(s, 1 - s, color=INK2, lw=1.2, ls='--')
b.text(0.052, 0.958, 'ideal: m₁+m₂+s ≤ 1', color=INK2, fontsize=9)
for kk, lab in [(22/23, '(22/23)(1−s)'), (7/8, '(7/8)(1−s)')]:
    b.plot(s, kk*(1 - s), color=C_TGT, lw=1, ls=':')
    b.text(0.072, kk*(1 - 0.072) + 0.004, lab, color=INK, fontsize=8.5)
b.plot(s, Einf, color=C_CONT, lw=2, label='E∞(s) = κ(q(s))·(1−s)')
b.plot(s, Ech, color=C_CHAIN, lw=1, label='E_chain(s) (130 faces)')
b.axvspan(0.02775, 0.0834, color=GRID, alpha=0.5, lw=0)
b.text(0.0295, 0.99, 'contact range of the chain', color=INK2, fontsize=8.5)
b.set_xlim(0, 0.1); b.set_ylim(0.78, 1.01)
b.set_xlabel('s  (slot length)'); b.set_ylabel('m₁ + m₂  (plain length)')
b.set_title('(b) certified region: below the envelope', color=INK, fontsize=10.5, loc='left')
b.grid(color=GRID, lw=0.6); b.legend(loc='lower left', frameon=False, fontsize=9)

# (c) gap
c = ax[2]
c.plot(s, (Einf - Ech)*1e4, color=C_CHAIN, lw=1.5)
c.set_xlim(0, 0.1); c.set_ylim(bottom=0)
c.set_xlabel('s'); c.set_ylabel('E∞(s) − E_chain(s)   [×10⁻⁴]')
c.set_title('(c) what the discretisation costs', color=INK, fontsize=10.5, loc='left')
c.grid(color=GRID, lw=0.6)
fig.tight_layout()
out = os.path.join(HERE, 'fig', 'face_systems.png')
fig.savefig(out, dpi=150)
print(out)
