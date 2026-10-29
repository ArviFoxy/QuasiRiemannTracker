"""Post-process the M4 json files: drop duplicate (config, Z) rows, refit kappa / ln-beta, write logs/m4_summary.txt.   python3 postprocess.py"""
import json
import os

import sweep

HERE = os.path.dirname(os.path.abspath(__file__))
LOGDIR = os.path.join(HERE, "logs")


def main():
    lines = []
    for fn in sorted(os.listdir(LOGDIR)):
        if not (fn.startswith("m4_") and fn.endswith(".json")) or "adversary" in fn:
            continue
        p = os.path.join(LOGDIR, fn)
        with open(p) as f:
            data = json.load(f)
        new = {}
        for cname, s in data.items():
            rows = []
            seenZ = set()
            for r in s["rows"]:
                if r["Z"] in seenZ:
                    continue
                seenZ.add(r["Z"])
                rows.append(r)
            fit_rows = [r for r in rows if r.get("min_pool", 10 ** 9) >= 6]
            entry = {"rows": rows, "fit_rows": len(fit_rows)}
            if len(fit_rows) >= 3:
                Zs = [r["Z"] for r in fit_rows]
                ys = [r["mean_row"] for r in fit_rows]
                ses = [r["se_mean_row"] for r in fit_rows]
                k, kse, chi = sweep.fit_power(Zs, ys, ses)
                b, bse, chib = sweep.fit_polylog(Zs, ys, ses)
                entry.update({"fit_Zmin": Zs[0], "fit_Zmax": Zs[-1], "kappa": k, "kappa_se": kse, "kappa_chi2dof": chi,
                              "polylog_beta": b, "polylog_beta_se": bse, "polylog_chi2dof": chib})
            new[cname] = entry
        with open(p, "w") as f:
            json.dump(new, f, indent=1)
        lines.append(f"## {fn}")
        import io
        buf = []
        sweep.print_summary(new, buf.append)
        lines.extend(buf)
        lines.append("")
    with open(os.path.join(LOGDIR, "m4_summary.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
