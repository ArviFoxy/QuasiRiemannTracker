"""Integer certificates (UTreeI) for the faceless family. Mirrors Lean `certI`.
usage: python3 gen_faceless_I.py SIG M OUTDIR [pieces] [only-tag]"""
import sys, os, json, time
from fractions import Fraction as Fr
import polyq as P
import family2 as F2
import cert2 as C2
import ipoly as I
import gen_faceless as G

def leaf_I(c, ka, m, kb, n, maxint=48):
    BB = I.ib33(c, ka, m, kb, n)
    out = []
    for a in range(4):
        for b in range(4):
            cov = I.dyadic_cover(BB[a][b], 0, 0, maxe=10)
            if cov is None or len(cov) > maxint: return None
            out.append(cov)
    return out

def find_I(c, ka, m, kb, n, depth=0, maxdepth=10):
    r = leaf_I(c, ka, m, kb, n)
    if r is not None: return ('leaf', r)
    if depth >= maxdepth: return None
    # u-length 2^-m, p-length 2^-n (p in [0, 1/2] starts at n = 1)
    for dim in (('u', 'p') if m <= n - 1 else ('p', 'u')):
        if dim == 'u':
            L_ = find_I(c, 2*ka, m + 1, kb, n, depth + 1, maxdepth); R_ = L_ and find_I(c, 2*ka + 1, m + 1, kb, n, depth + 1, maxdepth)
        else:
            L_ = find_I(c, ka, m, 2*kb, n + 1, depth + 1, maxdepth); R_ = L_ and find_I(c, ka, m, 2*kb + 1, n + 1, depth + 1, maxdepth)
        if L_ and R_: return (dim, L_, R_)
    return None

def tree_lean_I(T):
    if T[0] == 'leaf':
        return "(.leaf [" + ", ".join("[" + ", ".join(f"({k}, {e})" for (k, e) in cov) + "]" for cov in T[1]) + "])"
    return f"(.{T[0]} {tree_lean_I(T[1])} {tree_lean_I(T[2])})"

def stats_I(T):
    if T[0] == 'leaf': return 1, sum(len(c) for c in T[1])
    a = stats_I(T[1]); b = stats_I(T[2]); return a[0] + b[0], a[1] + b[1]

if __name__ == "__main__":
    sig = [float(x) for x in sys.argv[1].split(',')]
    m_ = int(sys.argv[2]); out = sys.argv[3]
    pieces = [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 and sys.argv[4] else None
    only = sys.argv[5] if len(sys.argv) > 5 else None
    fam, _ = F2.build2(sig, m=m_)
    os.makedirs(out, exist_ok=True)
    stats = {}
    for j in (pieces if pieces is not None else range(len(fam.H))):
        for bk in ('cross', 'cap'):
            for k in [(i, jj) for i in range(2) for jj in range(3)]:
                tag = f"{j}_{bk}_{k[0]}{k[1]}"
                if only and only != tag: continue
                t0 = time.time()
                U = C2.high_polys2(fam, j, bk, k)
                U = [[P.trim(U[a][b]) for b in range(4)] for a in range(4)]
                D, c = I.to_int16(U)
                T = find_I(c, 0, 0, 0, 1)
                assert T is not None, tag
                nl, ni = stats_I(T); stats[tag] = (nl, ni)
                bP = f"piece{j}.sp" if bk == 'cross' else "[capF]"
                body = ["import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.Data", "",
                        "set_option autoImplicit false", "set_option maxRecDepth 100000", "",
                        "namespace QRH.RepeatedMarks.Faceless", "",
                        f"def treeI_{tag} : IPoly.UTreeI :=", "  " + tree_lean_I(T), "",
                        f"theorem certI_{tag} : certI (piece{j}.highU {bP} ({k[0]}, {k[1]})) treeI_{tag} = true := by",
                        "  decide +kernel", "", "end QRH.RepeatedMarks.Faceless", ""]
                open(os.path.join(out, f"CertI_{tag}.lean"), 'w').write("\n".join(body))
                print(f"{tag}: leaves {nl} intervals {ni} ({time.time()-t0:.1f}s)", flush=True)
    json.dump(stats, open(os.path.join(out, 'statsI.json'), 'w'))
