"""Figure: what the return can use from a bigger energy region (fig/value.png).

(a) the slot profile at M = 1 (plain mass a against slot share s) of four continuous shapes: today's density
    curve, the same curve with kappa + 0.02, and the curves with a stronger HIGH count (zero-density exponent
    A = 2.2 on sigma in [3/4, 7/8], and A = 2 = density hypothesis); the count witnesses of the return.
(b) zoom on the count query.
(c) theta gain of each scenario (global check: whole (edge, delta, p) grid, all 15 guards), against the bar.
Usage: python3 fig_value.py   [the theta table below is copied from logs/*.log]
"""
import os
import numpy as np
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from levers import curve as kcurve, d
from zerodensity import curve as zcurve, make_rho

HERE = os.path.dirname(os.path.abspath(__file__))
INK, INK2, GRID, SURF = '#0b0b0b', '#52514e', '#e4e3df', '#fcfcfb'
C1, C2, C3, C4 = '#2a78d6', '#eb6834', '#1baf7a', '#eda100'      # reference palette slots 1-4, fixed order
GRAY = '#8a8984'

shapes = [('today: density curve (limit of the chain)', kcurve(2.5715, 0.99999), C1),
          ('density curve, kappa + 0.02', kcurve(2.5715, 0.99999, 0.02), C2),
          ('HIGH count with zero-density exponent A = 2.2', zcurve(make_rho('A2.2')), C3),
          ('HIGH count with A = 2 (density hypothesis)', zcurve(make_rho('A2.0')), C4)]
S = np.linspace(0.0, 0.13, 1301)


def profile(Bc, cap=0.1):
    Lq = brentq(lambda L: d * L / (6 * Bc(L) - L) - 0.5, 1.75, 2.5)
    Ls = np.linspace(2.5715, Lq, 3000)
    Bs = np.array([Bc(L) for L in Ls])
    a = np.max(Bs[:, None] - Ls[:, None] * S[None, :], axis=0)
    return np.where(S <= cap, a, np.nan)


# global theta* gains (1e-5 units), from logs/lg_*.log, logs/zd_*.log, logs/zone_value.log
TABLE = [('today: exact density curve (no step loss)', 0.136, None),
         ('past the floor q = 1/2', 0.31, None),
         ('kappa + 0.005', 2.14, None), ('kappa + 0.01', 3.94, None), ('kappa + 0.02', 6.30, None),
         ('boot face at Lam = 2.4', 4.49, None), ('boot face at Lam = 2.3', 6.30, 8.16),
         ('zero density A = 2.25', 2.64, 2.64), ('zero density A = 2.23', 4.59, 4.59),
         ('zero density A = 2.22', 5.82, 5.82), ('zero density A = 2.2', 6.30, 8.22),
         ('zero density A = 2.15', 6.30, 13.8), ('zero density A = 2 (DH)', 6.30, 18.0),
         ('Huxley-type exponent', 6.30, 10.7), ('DH from sigma = 11/14', 6.30, 14.4),
         ('whole window (B = 1, phys. saturated)', None, 18.0)]

plt.rcParams.update({'font.size': 9.5, 'axes.edgecolor': INK2, 'axes.labelcolor': INK, 'xtick.color': INK2,
                     'ytick.color': INK2, 'axes.facecolor': SURF, 'figure.facecolor': SURF, 'text.color': INK})
fig = plt.figure(figsize=(13.5, 11.0))
gs = fig.add_gridspec(2, 2, height_ratios=[1, 1.45], hspace=0.28, wspace=0.22)
axa, axb, axc = fig.add_subplot(gs[0, 0]), fig.add_subplot(gs[0, 1]), fig.add_subplot(gs[1, :])

profs = [(name, profile(Bc), col) for name, Bc, col in shapes]
for ax, (s0, s1, a0, a1) in ((axa, (0, 0.13, 0.70, 1.005)), (axb, (0.080, 0.125, 0.745, 0.815))):
    for name, a, col in profs:
        ax.plot(S, a, color=col, lw=2, label=name)
    ax.plot(S, 1 - S, color=GRAY, lw=1, ls='--', label='ideal face a + s = 1')
    ax.axvline(0.1, color=INK2, lw=0.8, ls=':')
    ax.text(0.1005, a0 + 0.04 * (a1 - a0), 'slot cap 1/10', color=INK2, fontsize=8, rotation=90, va='bottom')
    # count witnesses of the return (binding point newTop, p = 1/2)
    ax.plot([0.0928], [0.7834], 'o', ms=8, mfc=SURF, mec=INK, mew=1.6, zorder=5)
    ax.plot([0.1, 0.12], [0.7738, 0.7572], 's', ms=7, mfc=INK, mec=SURF, mew=1.2, zorder=5)
    ax.set_xlim(s0, s1); ax.set_ylim(a0, a1)
    ax.grid(color=GRID, lw=0.6); ax.set_axisbelow(True)
    ax.set_xlabel('slot share s'); ax.set_ylabel('plain mass a = m1 + m2')
axa.set_title('(a) slot profiles of the continuous shapes (M = 1)', loc='left', fontsize=10)
axb.set_title('(b) zoom on the count query', loc='left', fontsize=10)
axb.annotate("today's count witness", (0.0928, 0.7834), (0.0815, 0.7925), fontsize=8.5, color=INK,
             arrowprops=dict(arrowstyle='-', color=INK2, lw=0.8))
axb.annotate('capped witnesses\n(cap 0.10, 0.12)', (0.1, 0.7738), (0.1035, 0.7505), fontsize=8.5, color=INK,
             arrowprops=dict(arrowstyle='-', color=INK2, lw=0.8))
axa.legend(loc='lower left', frameon=False, fontsize=8.5)

names = [t[0] for t in TABLE][::-1]
g10 = [t[1] if t[1] is not None else np.nan for t in TABLE][::-1]
g12 = [t[2] if t[2] is not None else np.nan for t in TABLE][::-1]
y = np.arange(len(names))
axc.barh(y + 0.19, g10, height=0.36, color=C1, label='faces with slot cap 1/10 (today)')
axc.barh(y - 0.19, g12, height=0.36, color=C2, label='faces with slot cap 0.12')
for yi, v in zip(y, g10):
    if not np.isnan(v):
        axc.text(v + 0.12, yi + 0.19, '%.3g' % v, va='center', fontsize=8, color=INK2)
for yi, v, w in zip(y, g12, g10):
    if not np.isnan(v) and (np.isnan(w) or abs(v - w) > 1e-9):
        axc.text(v + 0.12, yi - 0.19, '%.3g' % v, va='center', fontsize=8, color=INK2)
axc.axvline(5.0, color=INK, lw=1.2, ls='--')
axc.text(4.95, -1.05, 'submission bar 5e-5', fontsize=8.5, color=INK, ha='right')
axc.axvline(6.30, color=INK2, lw=0.9, ls=':')
axc.text(6.35, -1.05, 'ceiling with cap 1/10 (6.3e-5)', fontsize=8.5, color=INK2)
axc.set_yticks(y); axc.set_yticklabels(names)
axc.set_xlabel('theta gain over the merged 0.87387234   (units of 1e-5)')
axc.set_xlim(0, 19.8); axc.set_ylim(-1.4, len(names) - 0.4)
axc.grid(axis='x', color=GRID, lw=0.6); axc.set_axisbelow(True)
axc.legend(loc='upper right', frameon=False)
axc.set_title('(c) what each scenario is worth to the current return (global check, all guards)', loc='left', fontsize=10)
os.makedirs(os.path.join(HERE, 'fig'), exist_ok=True)
fig.savefig(os.path.join(HERE, 'fig', 'value.png'), dpi=150, bbox_inches='tight')
print('wrote fig/value.png')
