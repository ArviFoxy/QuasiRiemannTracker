"""Figure for the arvi-selected-leaf PR: the faces behind the bound, #94 against this PR.

#94 listed its faces: the 31 native steps of #86 (NativeK15.lean) to the boot face, then 129 density steps
(research/chain/steps_f050_dL200.json). This PR proves two lines of faces by induction (NativeStart.lean, Curve.lean).
Run from the repository root: python3 research/selected-leaf/plot_faces.py
"""
import json
import re
from fractions import Fraction as Fr
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
NATIVE = Path('/home/user/lean-env/qrh/Submissions/density_split_fine_chain/Source/NativeK15.lean')
STEPS = ROOT / 'research/chain/steps_f050_dL200.json'
OUT = ROOT / 'research/selected-leaf/faces.png'

# colours: reference palette (validated: blue/orange pass all checks on the light surface)
NEW, OLD = '#2a78d6', '#eb6834'
INK, INK2, MUTED, GRID, AXIS, SURFACE = '#0b0b0b', '#52514e', '#898781', '#e1e0d9', '#c3c2b7', '#fcfcfb'

# --- #94: the listed faces ---
num = r'\(?\s*(\d+)\s*/\s*(\d+)\s*(?::\s*ℝ)?\s*\)?'
native = [(1.0 * Fr(99999, 100000), 3.72, 0.06)]  # nface00 = face0
for m in re.finditer(r'def (?:nface\d+|bootFace) : Face := ⟨' + num + r',\s*' + num + r',\s*' + num + '⟩', NATIVE.read_text()):
    a = [int(x) for x in m.groups()]
    native.append((a[0] / a[1], a[2] / a[3], a[4] / a[5]))
steps = json.loads(STEPS.read_text())
chain = [(float(Fr(s['B'])), float(Fr(s['L'])), float(Fr(s['c']))) for s in steps]
old_count = chain[-1]
old_phys = chain[63]  # step 64

# --- this PR: two lines ---
B = 0.99999
nat_L = [3.72 - i * (3.72 - 2.5715) / 200 for i in range(201)]
nat_c = [3 / 50 + 80 / 2297 * (3.72 - L) for L in nat_L]
sel_L = [2.5715 - i * (2.5715 - 2.005) / 200 for i in range(201)]
sel_c = [1 / 10 + 3 / 50 * (2.5715 - L) for L in sel_L]
end = (B, 2.005, 0.13399)

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10.5, 'axes.edgecolor': AXIS,
                     'axes.labelcolor': INK2, 'xtick.color': INK2, 'ytick.color': INK2,
                     'figure.facecolor': SURFACE, 'axes.facecolor': SURFACE})
fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 6.6), sharex=True, gridspec_kw={'hspace': 0.12})

for ax in (ax1, ax2):
    ax.grid(True, color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    for s in ('top', 'right'):
        ax.spines[s].set_visible(False)

# top: budget B
ax1.plot([L for _, L, _ in native], [b for b, _, _ in native], 'o', ms=4.5, mfc='none', mec=OLD, mew=1.2,
         label='#94: listed faces (30 native steps of #86, then 129 density steps)')
ax1.plot([L for _, L, _ in chain], [b for b, _, _ in chain], 'o', ms=4.5, mfc='none', mec=OLD, mew=1.2)
ax1.plot(nat_L + sel_L, [B] * (len(nat_L) + len(sel_L)), '-', color=NEW, lw=2.2,
         label='this PR: two lines, each proved by one induction')
ax1.plot([old_count[1], old_phys[1]], [old_count[0], old_phys[0]], 'o', ms=9, color=OLD, mec=SURFACE, mew=1.5, zorder=5)
ax1.plot([end[1]], [end[0]], '*', ms=16, color=NEW, mec=SURFACE, mew=1.2, zorder=6)
ax1.annotate('#94 count face', (old_count[1], old_count[0]), xytext=(-12, -4), textcoords='offset points',
             ha='right', va='top', color=INK2, fontsize=9.5)
ax1.annotate('#94 physical face', (old_phys[1], old_phys[0]), xytext=(-12, -6), textcoords='offset points',
             ha='right', va='top', color=INK2, fontsize=9.5)
ax1.annotate('this PR: end face, used as\ncount and physical face', (end[1], end[0]), xytext=(0, -12),
             textcoords='offset points', ha='center', va='top', color=INK2, fontsize=9.5)
ax1.set_ylabel('budget B')
ax1.set_ylim(0.955, 1.008)
ax1.legend(loc='lower left', frameon=False, fontsize=9.5, labelcolor=INK2)

# bottom: slot cap c
ax2.plot([L for _, L, _ in native], [c for _, _, c in native], 'o', ms=4.5, mfc='none', mec=OLD, mew=1.2)
ax2.plot([L for _, L, _ in chain], [c for _, _, c in chain], 'o', ms=4.5, mfc='none', mec=OLD, mew=1.2)
ax2.plot(nat_L, nat_c, '-', color=NEW, lw=2.2)
ax2.plot(sel_L, sel_c, '-', color=NEW, lw=2.2)
ax2.plot([end[1]], [end[2]], '*', ms=16, color=NEW, mec=SURFACE, mew=1.2, zorder=6)
ax2.plot([old_count[1], old_phys[1]], [old_count[2], old_phys[2]], 'o', ms=9, color=OLD, mec=SURFACE, mew=1.5, zorder=5)
ax2.axvline(2.5715, color=MUTED, lw=0.8, ls=':')
ax2.text(3.15, 0.123, 'native line', color=INK2, fontsize=9.5, ha='center')
ax2.text(2.29, 0.139, 'selected-leaf line', color=INK2, fontsize=9.5, ha='center')
ax2.set_ylabel('slot cap c')
ax2.set_ylim(0.05, 0.15)
ax2.set_xlim(3.8, 1.88)
ax2.set_xlabel('Λ (cost per unit of slot width); the proof runs left to right')

fig.suptitle('#94 used 159 listed steps of faces; this PR proves two lines of faces by induction',
             x=0.065, y=0.995, ha='left', fontsize=12, color=INK)
fig.text(0.065, 0.945, 'A face G(B, Λ, c) is a proven source bound: plain length + Λ·(slot width) ≤ B for slot width ≤ c.',
         ha='left', fontsize=9.5, color=INK2)
fig.savefig(OUT, dpi=160, bbox_inches='tight', facecolor=SURFACE)
print('wrote', OUT, 'native faces', len(native), 'chain faces', len(chain))
