"""Collect the M4 sweep results into one table (logs/evidence_table.md).   python3 summarize.py"""
import json
import os
import re

import mechanisms as mech

HERE = os.path.dirname(os.path.abspath(__file__))
LOGDIR = os.path.join(HERE, "logs")


def load(fn):
    p = os.path.join(LOGDIR, fn)
    if not os.path.exists(p):
        return {}
    with open(p) as f:
        return json.load(f)


def main():
    sets = [("S1 plain only", "m4_S1_plain_only.json"), ("S2 slots, Z<=3e6", "m4_S2_with_slots.json"),
            ("S3 slots, Z<=1e12", "m4_S3_high_Z.json"), ("S5 eta=(c0/.)_6, c0=3+w", "m4_S5_eta_twist.json")]
    rnd = {}
    for fn in ("m4_S4_random_model.json", "m4_S4b_random_model_high_Z.json"):
        for k, v in load(fn).items():
            rnd.setdefault(k, []).extend(v["rows"])
    lines = []
    lines.append("| exp | config (m1,m2 ; slots w_i) | a | s | fit Z range | mean row energy first -> last | kappa (E ~ K Z^kappa) | ln-fit beta | actual / random-model (largest Z) |")
    lines.append("|---|---|---|---|---|---|---|---|---|")
    entries = []
    for label, fn in sets:
        data = load(fn)
        for cname, s in data.items():
            if "kappa" not in s:
                continue
            m1, m2, slots = mech.parse_config(cname)
            entries.append((sum(slots), m1 + m2, label, cname, s))
    entries.sort(key=lambda e: (e[0], e[1], e[3]))
    for sv, av, label, cname, s in entries:
        rows = [r for r in s["rows"] if r.get("min_pool", 10 ** 9) >= 6]
        ratio = ""
        if cname in rnd:
            zmax = rows[-1]["Z"]
            rr = [r for r in rnd[cname] if r["Z"] == zmax]
            if rr and rows[-1]["mean_row"] > 0:
                ratio = f"{rows[-1]['mean_row'] / rr[0]['mean_row']:.2f}"
        lines.append(f"| {label} | {cname} | {av:.2f} | {sv:.2f} | {rows[0]['Z']:.0e}-{rows[-1]['Z']:.0e} | {rows[0]['mean_row']:.4f} -> {rows[-1]['mean_row']:.4f} | "
                     f"{s['kappa']:+.3f} +- {s['kappa_se']:.3f} | {s['polylog_beta']:+.2f} +- {s['polylog_beta_se']:.2f} | {ratio} |")
    with open(os.path.join(LOGDIR, "evidence_table.md"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))
    ks = [e[4]["kappa"] for e in entries]
    zs = [(e[4]["kappa"] - 2 * e[4]["kappa_se"]) for e in entries]
    print(f"\nconfigurations with a fit: {len(entries)};  max kappa = {max(ks):+.3f};  max (kappa - 2 se) = {max(zs):+.3f};  min kappa = {min(ks):+.3f}")


if __name__ == "__main__":
    main()
