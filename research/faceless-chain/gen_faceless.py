"""Generate the Lean data and certificates of the faceless family (Submissions/.../Faceless/).

Mirrors exactly the Lean computations of Faceless/Family.lean and Faceless/HighCert.lean:
  piece polynomials, valP samples, bicubicP, cuP (highU), bern33P leaves, Poly.posOn breakpoints.

usage: python3 gen_faceless.py SIG(comma list) M OUTDIR [pieces] [what]
"""
import sys, os, json, time
from fractions import Fraction as Fr
import polyq as P
import family2 as F2
import cert_proto as CP
import cert2 as C2

PKG = 'Submissions.arvi_repeated_marks_20261024'


def q(x):
    x = Fr(x)
    return f"({x.numerator}/{x.denominator})" if x.denominator != 1 else f"({x.numerator})"


def poly_lean(p):
    return "[" + ", ".join(q(c) for c in p) + "]"


def dyadic_split(p, lo, hi, depth=0, maxdepth=14):
    if P.tm1(p, lo, hi - lo):
        return [hi]
    if depth >= maxdepth:
        return None
    m = (lo + hi)/2
    l = dyadic_split(p, lo, m, depth + 1, maxdepth)
    if l is None:
        return None
    r = dyadic_split(p, m, hi, depth + 1, maxdepth)
    return None if r is None else l + r


def leaf_cert(U, a, s, b, t, maxint=64):
    BB = CP.bern33(U, a, s, b, t)
    out = []
    for I in range(4):
        for J in range(4):
            x = dyadic_split(BB[I][J], Fr(0), Fr(1), maxdepth=9)
            if x is None or len(x) > maxint:
                return None
            out.append(x)
    return out


def find_tree(U, a, s, b, t, depth=0, maxdepth=10):
    r = leaf_cert(U, a, s, b, t)
    if r is not None:
        return ('leaf', r)
    if depth >= maxdepth:
        return None
    for dim in (('u', 'p') if s >= 2*t else ('p', 'u')):
        if dim == 'u':
            L_ = find_tree(U, a, s/2, b, t, depth + 1, maxdepth)
            R_ = L_ and find_tree(U, a + s/2, s/2, b, t, depth + 1, maxdepth)
        else:
            L_ = find_tree(U, a, s, b, t/2, depth + 1, maxdepth)
            R_ = L_ and find_tree(U, a, s, b + t/2, t/2, depth + 1, maxdepth)
        if L_ and R_:
            return (dim, L_, R_)
    return None


def tree_lean(T):
    if T[0] == 'leaf':
        return "(.leaf [" + ", ".join("[" + ", ".join(q(x) for x in bs) + "]" for bs in T[1]) + "])"
    return f"(.{T[0]} {tree_lean(T[1])} {tree_lean(T[2])})"


def tree_stats(T):
    if T[0] == 'leaf':
        return 1, sum(len(bs) for bs in T[1])
    a = tree_stats(T[1]); b = tree_stats(T[2])
    return a[0] + b[0], a[1] + b[1]


def piece_lean(fam, j):
    return f"⟨{q(fam.sig[j])}, {q(fam.H[j])}, {q(fam.Dy)}, {poly_lean(fam.Ey[j])}⟩"


if __name__ == "__main__":
    sig = [float(x) for x in sys.argv[1].split(',')]
    m = int(sys.argv[2]); out = sys.argv[3]
    pieces = [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else None
    only = sys.argv[5] if len(sys.argv) > 5 else None
    fam, _ = F2.build2(sig, m=m)
    os.makedirs(out, exist_ok=True)
    # data file
    L = ["import " + PKG + ".Faceless.HighCert", "", "set_option autoImplicit false", "",
         "namespace QRH.RepeatedMarks.Faceless", ""]
    for j in range(len(fam.H)):
        L.append(f"def piece{j} : Piece := {piece_lean(fam, j)}")
    L += ["", "end QRH.RepeatedMarks.Faceless", ""]
    open(os.path.join(out, 'Data.lean'), 'w').write("\n".join(L))
    stats = {}
    for j in (pieces if pieces is not None else range(len(fam.H))):
        for bk in ('cross', 'cap'):
            for k in [(i, jj) for i in range(2) for jj in range(3)]:
                tag = f"{j}_{bk}_{k[0]}{k[1]}"
                if only and only != tag:
                    continue
                t0 = time.time()
                U = C2.high_polys2(fam, j, bk, k)
                T = find_tree(U, Fr(0), Fr(1), Fr(0), Fr(1, 2))
                assert T is not None, tag
                nl, ni = tree_stats(T)
                stats[tag] = (nl, ni)
                bP = f"piece{j}.sp" if bk == 'cross' else "[capF]"
                body = ["import " + PKG + ".Faceless.Data", "", "set_option autoImplicit false",
                        "set_option maxRecDepth 100000", "", "namespace QRH.RepeatedMarks.Faceless", "",
                        f"def tree_{tag} : UTree :=", "  " + tree_lean(T), "",
                        f"theorem cert_{tag} : uCheck (piece{j}.highU {bP} ({k[0]}, {k[1]})) tree_{tag} 0 1 0 (1/2) = true := by",
                        "  decide +kernel", "", "end QRH.RepeatedMarks.Faceless", ""]
                open(os.path.join(out, f"Cert_{tag}.lean"), 'w').write("\n".join(body))
                print(f"{tag}: leaves {nl} breakpoints {ni} ({time.time()-t0:.1f}s)", flush=True)
    json.dump(stats, open(os.path.join(out, 'stats.json'), 'w'))
