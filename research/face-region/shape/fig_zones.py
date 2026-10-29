"""Figure: the energy region estimates of the marked chain (130 faces) and of the continuous ODE path.

(a) primal plane at M = 1: slot share s (x) against plain mass a = m1 + m2 (y). A face is the half-plane
    a + Lam s <= B; a shape is the region under its boundary.  Chain shape = union of the 130 faces;
    ODE shape = union of the faces along the exact curve; eta-shape = the curve with kappa - eta (margin).
(b) the gaps between the boundaries (1e-5 units).
(c) dual plane (Lam, B): each face is a point; the chain is 130 points, the ODE is a curve.
(d) B of the ODE minus B of the chain / eta-curve at the same Lam (1e-5 units).
Usage: python3 fig_zones.py  ->  fig/zones.png
"""
import json, os, sys
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '..', '..', 'return-tuning'))
from model import P, witness

INK, INK2, GRID, SURF = '#0b0b0b', '#52514e', '#e4e3df', '#fcfcfb'
BLUE, ORANGE, AQUA = '#2a78d6', '#eb6834', '#1baf7a'     # ODE, chain, eta-curve (reference palette slots 1-3)
GRAY = '#8a8984'

steps = json.load(open(os.path.join(here, '..', '..', 'chain', 'steps_f050_dL200.json')))
faces = [(float(Fr(steps[0]['B0'])), float(Fr(steps[0]['L0'])))] + [(float(Fr(s['B'])), float(Fr(s['L']))) for s in steps]
CB = np.array([f[0] for f in faces]); CL = np.array([f[1] for f in faces])

d = 0.999
rf = (0.5 + d) / 3
def q_of(B, L): return min(d * L / (6 * B - L), 0.75)
def kappa(q): return 4 * (5 - 3 * q) / (25 - 18 * q)
def curve(eta):
    f = lambda L, y: [(y[0] - (kappa(q_of(y[0], L)) - eta)) / (L - (kappa(q_of(y[0], L)) - eta))]
    sol = solve_ivp(f, [CL[0], 1.90], [CB[0]], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True)
    Lf = brentq(lambda L: float(sol.sol(L)[0]) / L - rf, 1.90, 2.0)
    Ls = np.linspace(CL[0], Lf, 40001)
    return Ls, sol.sol(Ls)[0], Lf
ode = curve(0.0); e4 = curve(1e-4)

S = np.linspace(0.0, 0.1, 2001)
def envelope(Bs, Ls):
    out = np.full_like(S, -np.inf)
    for i in range(0, len(Bs), 1):
        out = np.maximum(out, Bs[i] - Ls[i] * S)
    return out
a_chain = envelope(CB, CL)
a_ode = envelope(ode[1][::4], ode[0][::4])
a_e4 = envelope(e4[1][::4], e4[0][::4])

# queries of the return (merged constants): count witness at the binding point, physical query at newTop
Pm = P()
_, _, m = witness(Pm, 'C', 0.44879, 0.5)
a_cnt = 2 * m; s_cnt = (Pm.cB - a_cnt) / Pm.cL
a_phy = 2 * (Pm.dp - Pm.y) / Pm.dp; s_phy = Pm.new_capacity(Pm.dp) / Pm.dp

plt.rcParams.update({'font.size': 10, 'axes.edgecolor': INK2, 'axes.labelcolor': INK, 'xtick.color': INK2,
                     'ytick.color': INK2, 'axes.titlesize': 11, 'axes.titleweight': 'bold', 'text.color': INK,
                     'figure.facecolor': SURF, 'axes.facecolor': SURF, 'legend.frameon': False})
fig, ax = plt.subplots(2, 2, figsize=(13.5, 10.5))
for a_ in ax.flat:
    a_.grid(True, color=GRID, lw=0.6); a_.set_axisbelow(True)
    for sp in ('top', 'right'):
        a_.spines[sp].set_visible(False)

# (a) primal plane
A = ax[0, 0]
for i in range(len(CB)):
    A.plot(S, CB[i] - CL[i] * S, color=GRAY, lw=0.35, alpha=0.35, zorder=1)
A.fill_between(S, 0.70, a_ode, color=BLUE, alpha=0.07, lw=0, zorder=0)
A.plot(S, a_chain, color=ORANGE, lw=2, label='chain shape: union of the 130 certified faces', zorder=3)
A.plot(S, a_ode, color=BLUE, lw=2, ls=(0, (5, 3)), label='ODE shape: union of the faces on the exact curve', zorder=4)
A.plot(S, 1 - S, color=GRAY, lw=1.2, ls=':', label='ideal face a + s = 1 (reference only, not a proven bound)', zorder=2)
A.plot([s_cnt], [a_cnt], 'o', color=INK, ms=7, zorder=5)
A.annotate('count query (binding row)\ns = %.4f, a = %.4f' % (s_cnt, a_cnt), (s_cnt, a_cnt), xytext=(0.052, 0.765),
           arrowprops=dict(arrowstyle='-', color=INK2, lw=0.8), fontsize=9, color=INK)
A.plot([s_phy], [a_phy], 's', color=INK, ms=7, zorder=5)
A.plot([0.06], [a_phy], 's', mfc='none', mec=INK, ms=7, zorder=5)
A.annotate('physical query: reaches s = %.4f\nof its cap s = 0.06 (hollow square)' % s_phy, (s_phy, a_phy), xytext=(0.012, 0.80),
           arrowprops=dict(arrowstyle='-', color=INK2, lw=0.8), fontsize=9, color=INK)
A.set_xlim(0, 0.1); A.set_ylim(0.74, 1.0)
A.set_xlabel('slot share s'); A.set_ylabel('plain mass a = m₁ + m₂')
A.set_title('(a) Energy region estimates (M = 1): proven region lies below each curve')
A.legend(loc='upper right', fontsize=8.5)
A.text(0.002, 0.745, 'gray: the 130 face lines a + Λs = B', color=INK2, fontsize=8.5)

# (b) gaps
Bx = ax[0, 1]
Bx.plot(S, (a_ode - a_chain) * 1e5, color=ORANGE, lw=2, label='ODE − chain')
Bx.plot(S, (a_ode - a_e4) * 1e5, color=AQUA, lw=2, label='ODE − η-curve (η = 10⁻⁴, provable with margin)')
Bx.axhline(0, color=INK2, lw=0.8)
for sv, lab in ((s_cnt, 'count query'), (s_phy, 'physical query')):
    Bx.axvline(sv, color=INK2, lw=0.8, ls='--'); Bx.text(sv - 0.0012, Bx.get_ylim()[1] * 0.0 + 0.5, lab, rotation=90,
                                                         color=INK2, fontsize=8.5, ha='right', va='bottom')
Bx.set_xlim(0, 0.1); Bx.set_ylim(bottom=0)
Bx.set_xlabel('slot share s'); Bx.set_ylabel('boundary gap in a (×10⁻⁵)')
Bx.set_title('(b) How far each shape is below the ODE shape')
Bx.legend(loc='upper left', fontsize=8.5)

# (c) dual plane
Cx = ax[1, 0]
Cx.plot(ode[0], ode[1], color=BLUE, lw=1.6, zorder=4, label='exact ODE curve: 1/(Λ−B) − G(B/Λ) = const')
Cx.plot(CL, CB, 'o', color=ORANGE, ms=4.5, zorder=3, label='chain: 130 faces (boot + 129 steps)')
LL = np.linspace(1.9, 2.6, 10)
Cx.plot(LL, rf * LL, color=GRAY, lw=1.2, ls=':', label='density floor ray q = 1/2 (chain and ODE stop here)')
Cx.plot([CL[-1]], [CB[-1]], 'o', mfc='none', mec=INK, ms=11)
Cx.annotate('count face (chain end)', (CL[-1], CB[-1]), xytext=(1.99, 0.957), fontsize=9,
            arrowprops=dict(arrowstyle='-', color=INK2, lw=0.8))
Cx.plot([CL[64]], [CB[64]], 's', mfc='none', mec=INK, ms=11)
Cx.annotate('physical face (step 64)', (CL[64], CB[64]), xytext=(2.30, 0.975), fontsize=9,
            arrowprops=dict(arrowstyle='-', color=INK2, lw=0.8))
Cx.annotate('boot face', (CL[0], CB[0]), xytext=(2.45, 0.992), fontsize=9,
            arrowprops=dict(arrowstyle='-', color=INK2, lw=0.8))
Cx.set_xlim(1.9, 2.6); Cx.set_ylim(0.955, 1.002)
Cx.set_xlabel('slope Λ'); Cx.set_ylabel('budget B')
Cx.set_title('(c) Dual plane: a face a + Λs ≤ B is a point (Λ, B)')
Cx.legend(loc='lower right', fontsize=8.5)

# (d) dual residual
Dx = ax[1, 1]
Bode_at = np.interp(CL[::-1], ode[0][::-1], ode[1][::-1])[::-1]
Dx.plot(CL, (Bode_at - CB) * 1e5, 'o', color=ORANGE, ms=3.2, label='ODE − chain face, at the chain\'s Λ')
Be4_at = np.interp(ode[0][::-1], e4[0][::-1], e4[1][::-1])[::-1]
mask = ode[0] >= e4[2]
Dx.plot(ode[0][mask], (ode[1][mask] - Be4_at[mask]) * 1e5, color=AQUA, lw=2, label='ODE − η-curve (η = 10⁻⁴)')
Dx.axhline(0, color=INK2, lw=0.8)
Dx.set_xlim(1.9, 2.6); Dx.set_ylim(bottom=-0.5)
Dx.invert_xaxis()
Dx.set_xlabel('slope Λ (the path runs right to left)'); Dx.set_ylabel('B gap (×10⁻⁵)')
Dx.set_title('(d) The chain lags the ODE by O(step): up to %.1f×10⁻⁵ at its end' % ((Bode_at[-1] - CB[-1]) * 1e5))
Dx.legend(loc='upper left', fontsize=8.5)

fig.suptitle('Energy region estimates: the 130-step chain vs the continuous ODE path (θ: chain 0.87387234, ODE limit 0.87387100)',
             fontsize=12.5, fontweight='bold', color=INK)
fig.tight_layout(rect=(0, 0, 1, 0.965))
out = os.path.join(here, 'fig', 'zones.png')
fig.savefig(out, dpi=150, facecolor=SURF)
print('wrote', out)
print('count query s=%.5f a=%.5f; physical query s=%.5f a=%.5f; ODE end (%.8f, %.8f); chain end (%.8f, %.8f)'
      % (s_cnt, a_cnt, s_phy, a_phy, ode[0][-1], ode[1][-1], CL[-1], CB[-1]))
print('max gaps (1e-5): ODE-chain %.2f, ODE-eta %.2f' % (np.max(a_ode - a_chain) * 1e5, np.max(a_ode - a_e4) * 1e5))
