"""Grid search + rejection over the probed plane M = 1,  a = m1 + m2 in [0.30, 1.50],  s in [0, 0.30].

For every grid point (a, s) and every split (m1, m2) with m1 + m2 = a  (symmetric m1 = m2, 3:1, and (a, 0)) every mechanism of mechanisms.py is
evaluated; the point is coloured by the FIRST mechanism (in the order M1..M5) that rejects the symmetric slice.
Outputs: logs/grid.log, logs/outer_table.csv, fig/outer.png (and the counterfactual positive control fig/control_nokeep.png).

   python3 grid.py
"""
import csv
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

import mechanisms as mech

HERE = os.path.dirname(os.path.abspath(__file__))
S_GRID = np.round(np.arange(0.0, 0.3001, 0.025), 4)
A_GRID = np.round(np.arange(0.30, 1.5001, 0.05), 4)
SPLITS = {"sym": lambda a: (a / 2, a / 2), "3:1": lambda a: (0.75 * a, 0.25 * a), "(a,0)": lambda a: (a, 0.0)}

# validated categorical slots (dataviz reference palette, light mode; validate_palette.js: all hard checks pass), neutral for 'not rejected'
COLORS = {"M1": "#2a78d6", "M2": "#eb6834", "M3": "#1baf7a", "M4": "#eda100", "M5": "#e87ba4"}
NEUTRAL = "#dfe6ee"
INK = "#0b0b0b"
INK2 = "#52514e"
SURFACE = "#fcfcfb"

out = open(os.path.join(HERE, "logs", "grid.log"), "w")


def log(s=""):
    print(s)
    out.write(s + "\n")


def evaluate(mechs):
    """returns dict[(s, a)] -> dict(first=name|None, per_split={split: [names]}, notes)"""
    res = {}
    for s in S_GRID:
        for a in A_GRID:
            per_split = {}
            notes = {}
            for sp, f in SPLITS.items():
                m1, m2 = f(a)
                rej = []
                for name, fn in mechs:
                    r, why = fn(float(a), float(s), m1, m2)
                    if r:
                        rej.append(name)
                    notes[(sp, name)] = why
                per_split[sp] = rej
            first = per_split["sym"][0] if per_split["sym"] else None
            any_split = sorted({n for v in per_split.values() for n in v})
            res[(float(s), float(a))] = dict(first=first, per_split=per_split, any_split=any_split, notes=notes)
    return res


def draw(res, title, path, sampled=None, note=None, mechs_for_legend=None):
    fig, ax = plt.subplots(figsize=(8.6, 6.4), dpi=160)
    fig.patch.set_facecolor(SURFACE)
    ax.set_facecolor(SURFACE)
    ds, da = 0.0125, 0.025
    counts = {}
    from matplotlib.colors import to_rgb
    img = np.zeros((len(A_GRID), len(S_GRID), 3))
    for i, a in enumerate(A_GRID):
        for j, s_ in enumerate(S_GRID):
            r = res[(float(s_), float(a))]
            key = r["first"][:2] if r["first"] else None
            counts[key] = counts.get(key, 0) + 1
            img[i, j] = to_rgb(COLORS[key] if key else NEUTRAL)
    ax.imshow(img, origin="lower", extent=[S_GRID[0] - ds, S_GRID[-1] + ds, A_GRID[0] - da, A_GRID[-1] + da], aspect="auto",
              interpolation="nearest")
    if sampled:
        xs = [s for (s, a) in sampled]
        ys = [a for (s, a) in sampled]
        ax.scatter(xs, ys, s=9, color=INK2, zorder=5)
    ax.set_xlim(S_GRID[0] - ds, S_GRID[-1] + ds)
    ax.set_ylim(A_GRID[0] - da, A_GRID[-1] + da)
    ax.set_xticks(S_GRID[::2])
    ax.set_yticks(np.round(np.arange(0.3, 1.51, 0.1), 2))
    ax.set_xlabel("s  (total slot length, exponent of Z)", color=INK, fontsize=10)
    ax.set_ylabel("a = m1 + m2  (total plain length, exponent of Z)", color=INK, fontsize=10)
    ax.tick_params(colors=INK2, labelsize=9, length=3)
    for sp in ax.spines.values():
        sp.set_color("#c9c8c2")
    ax.set_title(title, color=INK, fontsize=11, loc="left", pad=10)
    handles = []
    labels = {"M1": "M1 degenerate rows", "M2": "M2 alignment / duality", "M3": "M3 diagonal term", "M4": "M4 small-scale numerics",
              "M5": "M5 frame / Welch"}
    for k in ["M1", "M2", "M3", "M4", "M5"]:
        handles.append(Patch(facecolor=COLORS[k], edgecolor="none", label=f"{labels[k]}: rejects {counts.get(k, 0)} points"))
    handles.append(Patch(facecolor=NEUTRAL, edgecolor="none", label=f"not rejected (outer bound): {counts.get(None, 0)} points"))
    if sampled:
        handles.append(Line2D([0], [0], marker="o", color="none", markerfacecolor=INK2, markersize=4, label="toy-model numerics run at this point (M4)"))
    leg = ax.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.5, -0.12), ncol=2, frameon=False, fontsize=8.5)
    for t in leg.get_texts():
        t.set_color(INK2)
    if note:
        ax.text(0.5, 0.5, note, transform=ax.transAxes, ha="center", va="center", fontsize=10, color=INK,
                bbox=dict(boxstyle="round,pad=0.5", facecolor=SURFACE, edgecolor="#c9c8c2", alpha=0.92), zorder=6)
    fig.subplots_adjust(left=0.09, right=0.97, top=0.93, bottom=0.27)
    fig.savefig(path, facecolor=SURFACE)
    plt.close(fig)
    return counts


def a_out_table(res):
    rows = []
    for s in S_GRID:
        ok = [a for a in A_GRID if res[(float(s), float(a))]["first"] is None]
        # largest a such that every grid point at or below it (at this s) is not rejected
        a_out = None
        for a in A_GRID:
            if res[(float(s), float(a))]["first"] is None:
                a_out = float(a)
            else:
                break
        any_ok = None
        for a in A_GRID:
            if not res[(float(s), float(a))]["any_split"]:
                any_ok = float(a)
            else:
                break
        rows.append((float(s), a_out, any_ok))
    return rows


def main():
    log("# grid.py: M = 1, a in [0.30, 1.50] step 0.05 (25 values), s in [0, 0.30] step 0.025 (13 values) -> 325 points x 3 splits x 5 mechanisms")
    res = evaluate(mech.MECHANISMS)
    nrej = sum(1 for r in res.values() if r["first"])
    nany = sum(1 for r in res.values() if r["any_split"])
    log(f"points rejected on the symmetric slice (m1 = m2): {nrej}")
    log(f"points rejected on ANY of the 3 splits:            {nany}")
    for name, _ in mech.MECHANISMS:
        c = sum(1 for r in res.values() if name in r["per_split"]["sym"])
        log(f"  {name:28s} rejects {c} grid points (symmetric slice)")
    sampled = set()
    for (s, a) in res:
        if mech.numerics_near(a, s):
            sampled.add((s, a))
    log(f"grid points with toy-model numerics nearby (M4 evidence): {len(sampled)}")
    log("")
    log("per-s outer boundary a_out(s) = largest a such that all grid points up to it are NOT rejected (cap = 1.50 = edge of the window):")
    rows = a_out_table(res)
    with open(os.path.join(HERE, "logs", "outer_table.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["s", "a_out_symmetric_slice", "a_out_any_split", "note"])
        for s, a_out, any_ok in rows:
            note = "no rejection: boundary is the window edge (a >= 1.50)" if a_out == float(A_GRID[-1]) else "rejected beyond"
            w.writerow([f"{s:.3f}", f"{a_out:.2f}", f"{any_ok:.2f}", note])
            log(f"  s = {s:.3f}:  a_out(sym) = {a_out:.2f}{'+' if a_out == float(A_GRID[-1]) else ''}   a_out(any split) = {any_ok:.2f}{'+' if any_ok == float(A_GRID[-1]) else ''}")
    log("")
    log("evidence notes at three sample points (mechanism -> reason):")
    for (s, a) in [(0.0, 1.0), (0.3, 0.3), (0.3, 1.5)]:
        r = res[(s, a)]
        log(f"  (s={s}, a={a})")
        for name, _ in mech.MECHANISMS:
            log(f"     {name:26s} sym: {r['notes'][('sym', name)]}")
    log("")
    counts = draw(res, "Arvi Zone, outer bound at M = 1: first mechanism that rejects each grid point", os.path.join(HERE, "fig", "outer.png"),
                  sampled=sampled, note="no grid point is rejected by M1-M5\n(outer bound = the whole probed window)")
    log(f"figure fig/outer.png written; counts {counts}")

    # counterfactual positive control (NOT the Lean statement): initialKeep without removal of the principal rows
    ctrl = evaluate([("M1 degenerate rows (principal rows NOT removed)", mech.reject_M1_unmasked)])
    counts2 = draw(ctrl, "Counterfactual control (not the Lean statement): principal rows z = w^6 left in the family",
                   os.path.join(HERE, "fig", "control_nokeep.png"), note=None)
    log(f"control figure written; counts {counts2}; its boundary is  a + s = 1 - 1/6 = 5/6")
    rows2 = a_out_table(ctrl)
    for s, a_out, _ in rows2:
        log(f"  control s = {s:.3f}: a_out = {a_out:.2f}")


if __name__ == "__main__":
    main()
