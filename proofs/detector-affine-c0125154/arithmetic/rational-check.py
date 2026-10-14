"""Exact rational checks for the detector affine-capacity refinement.

Standard library only. No network, no proof assistant, no imported project code.

The script:
  1. re-runs the Cycle61 scalar design checks at the new endpoint
     theta = 437423/500000, h = 15903/20000 (every margin must stay positive);
  2. rebuilds every Bernstein certificate used by the Lean proof
     (newRow, oldHalf, oldJunction in Bundles/B021.lean and the region
     certificates in Affine/Certificates.lean), checks that all coefficients
     are positive, and checks that the row boxes cover [0,3/4] x [0,1/2] with
     disjoint interiors;
  3. if the submission source is present, parses those two Lean files and
     checks that every power polynomial and every coefficient matrix written
     there is exactly the one computed here.

It writes rational-receipt.json beside itself.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
SRC = HERE.parent.parent.parent / "submissions" / "detector-affine-c0125154" / "src" / "Candidate"
CHECKS = {}


def bind(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def eq(name, actual, expected):
    expected = Q(expected)
    assert actual == expected, (name, actual, expected)
    CHECKS[name] = str(actual)
    return actual


def pos(name, actual):
    assert actual > 0, (name, actual)
    CHECKS[name] = str(actual)
    return actual


def rec(name, actual):
    CHECKS[name] = str(actual)
    return actual


class Poly:
    def __init__(self, value=0):
        if isinstance(value, dict):
            self.c = {k: Q(v) for k, v in value.items() if v}
        else:
            self.c = {(0, 0): Q(value)} if value else {}

    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = dict(self.c)
        for k, v in other.c.items():
            out[k] = out.get(k, Q(0)) + v
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.c.items()})

    def __sub__(self, other):
        return self + (-(other if isinstance(other, Poly) else Poly(other)))

    def __rsub__(self, other):
        return (-self) + other

    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = {}
        for (i, j), a in self.c.items():
            for (k, l), b in other.c.items():
                out[(i + k, j + l)] = out.get((i + k, j + l), Q(0)) + a * b
        return Poly(out)

    __rmul__ = __mul__

    def __truediv__(self, other):
        return self * (1 / Q(other))

    def at(self, a, b):
        return sum(v * Q(a) ** i * Q(b) ** j for (i, j), v in self.c.items())


def bernstein(poly, box, m, n):
    a, b, c, d = map(Q, box)
    f = {}
    for (i, j), value in poly.c.items():
        assert i <= m and j <= n, (i, j, m, n)
        for r in range(i + 1):
            for s in range(j + 1):
                f[(r, s)] = f.get((r, s), Q(0)) + value * comb(i, r) * a ** (i - r) * (b - a) ** r \
                    * comb(j, s) * c ** (j - s) * (d - c) ** s
    return [[sum(f.get((r, s), Q(0)) * Q(comb(i, r), comb(m, r)) * Q(comb(j, s), comb(n, s))
                 for r in range(i + 1) for s in range(j + 1)) for j in range(n + 1)]
            for i in range(m + 1)]


delta = Poly({(1, 0): 1})
p = Poly({(0, 1): 1})

# ---------------------------------------------------------------- constants
theta = Q(437423, 500000)
h = Q(15903, 20000)
ell = Q(11, 3) - 4 * theta
x, y = 1 + ell - h, h - 2 * ell
ks = 2 * theta - 1
Lam = Q(19312, 4787)
B0, epscell = Q(14200, 14361), Q(1, 100000)
B = B0 - epscell
dm, dp, d0, t0 = h - Q(1, 1000), h + Q(1, 10 ** 10), Q(1, 200), Q(1, 1000)

eq("theta", theta, "437423/500000")
eq("c", 1 - theta, "62577/500000")
eq("h", h, "15903/20000")
eq("ell", ell, "62731/375000")
eq("x", x, "558199/1500000")
eq("y", y, "690877/1500000")
eq("kappa_star", ks, "187423/250000")
eq("lower_d", dm, "15883/20000")
eq("upper_d", dp, "7951500001/10000000000")
eq("B", B, "1419985639/1436100000")

# ------------------------------------------- Cycle61 scalar design checks
nmin, nmax = 1 - y / dm, 1 - y / dp + t0
zmin, zmax = (B - 2 * nmax) / Lam, (B - 2 * nmin) / Lam
rec("nmin", nmin)
rec("nmax", nmax)
rec("zmin", zmin)
rec("zmax", zmax)
pos("plain_upper_gap", Q(264, 625) - nmax)
pos("slot_upper_gap", Q(37, 1000) - zmax)
pos("slot_lower_gap", zmin - Q(17, 500))
pos("actual_supply", ell - dp * zmax)
pos("detector_supply", ell / dp - Q(4, 21))
pos("lower_supply", 2 * ell - Q(1, 3))
pos("four_ell_y", 4 * ell - y)
bmax = 2 * y / dm - 1
rec("bmax", bmax)
pos("bmax_below_4_25", Q(4, 25) - bmax)
oldz = lambda b, t: max(Q(0), (b - 2 * t) / Q(9, 2))
shift = lambda b, t: t / 2 - ((b - (1 - B)) / Lam - oldz(b, t)) / 4
eq("shift_coarse", shift(Q(4, 25), t0), "4035883/69523200000")
pos("shift_exact", shift(bmax, t0))
capacity = lambda d, new: (2 * y - (2 - B) * d) / Lam if new else (2 * y - d) / (6 * ks)
pos("junction", capacity(dm, True) - capacity(dm, False))
pos("extension", Q(1, 10 ** 6) - 2 * (dp - h))
pos("floor", theta - (Q(51, 100) + h / 3 + Q(51, 100) * ell))
pos("lower_row", theta - (Q(7, 8) - 49 * h / 150 + 7 * ell / 8 + 33 * d0 / 50))
pos("small_row", -(13 * h / 75 - y / 2 + 63 * d0 / 50))
pos("principal_w", y / 20 - (1 + h) / 1000 - Q(1, 4000))
pos("principal_z", h / 600 - Q(1, 1000) - Q(1, 4000))
assert rec("probe_first", y - 2 * x + ell) < 0
assert rec("probe_second", 1 + 3 * ell - 2 * (x + y)) < 0
eq("probe_boundary", (5 * x + y) / 12 - (theta - (Q(5, 6) - x / 3 - ell / 6)), 0)
rec("local_feedback", 5 * dp / 288)

# ------------------------------------------------ row polynomials
D = 3 - p - 2 * p / (3 * ks)
P = 2 * (1 - p) * (1 - p / (3 * ks))
V = Q(5, 6) - delta
J = V * D + delta * P
pos("J_positive_lower_bound", D.at(Q(0), Q(1, 2)) / 12)
pos("J_actual_corner", J.at(Q(3, 4), Q(1, 2)))


def row_old(d, v, new):
    C = capacity(d, new)
    return J * (theta - v - (1 + delta) / 2 - 13 * h / 75 + y / 2 + ell / 2 - ell * delta * p
                - d * (Q(1, 4) - Q(17, 50)) + delta * p * C / 2) \
        - 3 * d * ((1 - delta) * J + delta * P * V / 2) / 4


# new count (affine plain capacity (B - 2m)/Lam on the window [mLo, mHi])
mLo = (B - Lam / 25) / 2
mHi = Q(847, 2000)
gam0 = Q(1, 10000)
DN = 3 - p - 4 * p / Lam
aN = 2 - 4 * p / Lam
cN = 1 - 2 * p * B / Lam
JN = V * DN + delta * (1 - p) * aN
NumT = V * DN + delta * (1 - p) * (aN + cN)


def row_new(d, v, new):
    C = capacity(d, new)
    return JN * (theta - v - (1 + delta) / 2 - 13 * h / 75 + y / 2 + ell / 2 - ell * delta * p
                 - d * (Q(1, 4) - Q(17, 50)) + delta * p * C / 2) \
        - 3 * d * ((1 - delta) * JN + V * delta * (1 - p) * cN) / 4


rNnum = aN * NumT + (2 * p * B / Lam - p) * JN
numc = 2 * (1 - p) * (3 * ks - p)
denc = 3 * ks * (3 - p) - 2 * p
VALIDITY = {
    # rN >= 23/37
    "regionCrossLo": rNnum - Q(23, 37) * DN * JN,
    # rN <= 1
    "regionCrossHi": DN * JN - rNnum,
    # tN - rN(tN) >= mLo + 1/10000
    "regionPlain": (1 - p) * NumT + (p - 2 * p * B / Lam) * JN - (mLo + gam0) * DN * JN,
    # shortNew(tN) >= old marked exponent at m = mHi, kappa = 3/4 (divided by delta)
    "regionTail": JN * (-1 + 2 * mHi + 2 * p * (1 - 2 * mHi) / (6 * Q(3, 4))) + V * (1 - p) * cN,
    # tN <= 3/2
    "regionCutoff": Q(3, 2) * JN - NumT,
    # RNew <= countingR at kappa_star
    "regionCompare": numc * JN - 2 * (1 - p) * cN * (V * denc + delta * numc),
}
pos("mLo_window", mLo - Q(41, 100))
pos("mHi_window", Q(44, 100) - mHi)
eq("affine_weight_at_mLo", (B - 2 * mLo) / Lam, Q(1, 25))
# mHi is exactly the old-cap endpoint for weight 17/500 at kappa = 3/4; the branch uses weight < 17/500
eq("small_weight_old_branch", (1 - 6 * Q(3, 4) * Q(17, 500)) / 2 - mHi, 0)

# ------------------------------------------------ certificates
ra, rb, rc, rd = Q(89, 200), Q(97, 200), Q(99, 200), Q(1, 2)
SIX = [(Q(0), Q(3, 8), Q(0), Q(1, 2)), (Q(3, 8), Q(3, 4), Q(0), Q(1, 4)), (Q(3, 8), Q(9, 16), Q(1, 4), Q(3, 8)),
       (Q(3, 8), Q(15, 32), Q(3, 8), Q(1, 2)), (Q(15, 32), Q(9, 16), Q(3, 8), Q(1, 2)),
       (Q(9, 16), Q(3, 4), Q(1, 4), Q(1, 2))]
COMP = [(Q(0), ra, Q(0), Q(1, 2)), (rb, Q(3, 4), Q(0), Q(1, 2)), (ra, rb, Q(0), rc)]
REGB = [(ra, Q(93, 200), rc, rd), (Q(93, 200), Q(95, 200), rc, rd), (Q(95, 200), rb, rc, rd)]
REG = [(ra, rb, rc, rd)]

CERTS = [
    ("newRow", row_old(h, Q(1, 10 ** 6), True), COMP, (2, 3)),
    ("oldHalf", row_old(Q(1, 2), Q(1, 1000), False), [(Q(0), Q(3, 4), Q(0), Q(1, 2))], (2, 3)),
    ("oldJunction", row_old(dm, Q(1, 10 ** 5), False), SIX, (2, 3)),
    ("regionRow", row_new(h, Q(1, 10 ** 6), True), REGB, (2, 3)),
] + [(k, v, REG, (2, 4) if k == "regionCompare" else (2, 3)) for k, v in VALIDITY.items()]


def cover(boxes, name):
    assert sum((b - a) * (d - c) for a, b, c, d in boxes) == Q(3, 8), name
    for i, (a, b, c, d) in enumerate(boxes):
        assert 0 <= a < b <= Q(3, 4) and 0 <= c < d <= Q(1, 2), name
        for a2, b2, c2, d2 in boxes[i + 1:]:
            assert max(a, a2) >= min(b, b2) or max(c, c2) >= min(d, d2), name


def inside(boxes, outer, name):
    A, Bx, C, Dx = outer
    assert sum((b - a) * (d - c) for a, b, c, d in boxes) == (Bx - A) * (Dx - C), name
    for i, (a, b, c, d) in enumerate(boxes):
        assert A <= a < b <= Bx and C <= c < d <= Dx, name
        for a2, b2, c2, d2 in boxes[i + 1:]:
            assert max(a, a2) >= min(b, b2) or max(c, c2) >= min(d, d2), name


cover(SIX, "six")
cover([(Q(0), Q(3, 4), Q(0), Q(1, 2))], "half")
cover(COMP + REGB, "new row: complement plus region")
inside(REGB, REG[0], "region split")

computed = {}
results = []
for name, poly, boxes, (m, n) in CERTS:
    allco = []
    computed[name] = {"poly": poly.c, "boxes": boxes, "coeffs": []}
    for bx in boxes:
        co = bernstein(poly, bx, m, n)
        computed[name]["coeffs"].append(co)
        allco += [c for row in co for c in row]
    assert min(allco) > 0, (name, float(min(allco)))
    results.append({"name": name, "degree": [m, n], "boxes": [[str(t) for t in b] for b in boxes],
                    "coefficients": len(allco), "minimum": str(min(allco))})

# ------------------------------------------------ cross-check against the Lean source
lean_checked = []
if SRC.is_dir():
    text = (SRC / "Bundles" / "B021.lean").read_text(encoding="utf-8") + \
        (SRC / "Affine" / "Certificates.lean").read_text(encoding="utf-8")

    def frac(s):
        s = s.replace(" ", "")
        return Q(s)

    for name, data in computed.items():
        mpow = re.search(r"noncomputable def %sPower \(δ p : ℝ\) : ℝ :=\n(.*?)\n\n" % name, text, re.S)
        assert mpow, ("missing power", name)
        terms = {}
        for t in mpow.group(1).split("+\n"):
            t = t.strip()
            mt = re.fullmatch(r"\(([-0-9/]+)\)((?:\*δ\^\d+)?)((?:\*p\^\d+)?)", t)
            assert mt, (name, t)
            i = int(mt.group(2)[3:]) if mt.group(2) else 0
            j = int(mt.group(3)[3:]) if mt.group(3) else 0
            terms[(i, j)] = frac(mt.group(1))
        assert terms == data["poly"], ("power polynomial", name)
        for k, (bx, co) in enumerate(zip(data["boxes"], data["coeffs"])):
            mc = re.search(r"noncomputable def %sCoefficients%d : Fin \d → Fin \d → ℝ :=\n  !\[(.*?)\]\n\n"
                           % (name, k), text, re.S)
            assert mc, ("missing coefficients", name, k)
            rows = re.findall(r"!\[(.*?)\]", mc.group(1) + "]", re.S)
            lean_co = [[frac(v) for v in re.findall(r"\(([-0-9/ ]+) : ℝ\)", r)] for r in rows]
            assert lean_co == co, ("coefficients", name, k)
            mi = re.search(r"theorem %sIdentity%d \(δ p : ℝ\) :\n.*?\(\(δ-\(([-0-9/]+)\)\)/\(\(([-0-9/]+)\)-"
                           r"\(([-0-9/]+)\)\)\) \(\(p-\(([-0-9/]+)\)\)/\(\(([-0-9/]+)\)-\(([-0-9/]+)\)\)\)"
                           % (name, k), text, re.S)
            assert mi, ("missing identity box", name, k)
            a, b, a2, c, d, c2 = map(frac, mi.groups())
            assert (a, b, c, d) == bx and a2 == a and c2 == c, ("box", name, k)
        lean_checked.append(name)
    assert len(lean_checked) == len(CERTS)

out = {
    "status": "PASS exact rational reconstruction; not formalization",
    "endpoint": {"theta": str(theta), "h": str(h)},
    "scalar_checks": CHECKS,
    "certificates": results,
    "certificate_coefficients": sum(r["coefficients"] for r in results),
    "lean_source_cross_checked": lean_checked,
    "helper": bind(Path(__file__)),
}
(HERE / "rational-receipt.json").write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"status": out["status"], "scalar_count": len(CHECKS),
                  "certificates": len(results), "coefficients": out["certificate_coefficients"],
                  "lean_cross_checked": len(lean_checked)}))
