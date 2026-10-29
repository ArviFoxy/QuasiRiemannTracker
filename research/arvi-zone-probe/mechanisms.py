"""Rejection mechanisms for the Arvi-Zone outer bound.  Each mechanism is a function
        reject_Mk(a, s, m1, m2, ctx) -> (bool rejected, str reason)
for a configuration (m1, m2, s, M = 1)  (a = m1 + m2).

Status labels:  [rigorous]  proved from the Lean definitions / standard theorems,
                [heuristic] relies on a standard conjecture (GRH / Lindelof for the Hecke L-functions of Q(omega)),
                [numerical] finite-size evidence from the toy model (toy.py, sweep.py).

A configuration is rejected by a mechanism only if that mechanism PRODUCES admissible data whose energy provably (or convincingly,
under a standard conjecture) exceeds Z^{M+eps} by a power of Z.  Upper bounds on the energy never reject anything.
"""
from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass

HERE = os.path.dirname(os.path.abspath(__file__))
LOGDIR = os.path.join(HERE, "logs")
M = 1.0  # family exponent of the probed plane (UnitRegionSource: Mmin = Mmax = 1)

# ----------------------------------------------------------------------------------------------------------
# Mechanism 1: degenerate rows
# ----------------------------------------------------------------------------------------------------------
# Rows are z in O = Z[omega], K = Z^M of them.  The row character is n -> eta(n) (m^6 z / n)_6 ; the sums A_j, S_i see it.
# class: number of rows ~ K^count_exp ; kept = survives initialKeep ; full_size = the plain AND slot sums reach their trivial size
# (a pole of the Dirichlet series, i.e. a PRINCIPAL character) ; if not, they cancel (functional equation: dead beyond X ~ q;
# GRH/GLH: |A|^2 <~ X, |S|^2 <~ D otherwise).
DEGENERATE_CLASSES = [
    dict(name="principal rows z = w^6 (row character trivial off its support)", count_exp=1 / 6, kept=False, full_size=True,
         why="FixedInducingRow with psi = trivial character (modulus (1), vacuously primitive, Q <= (1)); removed by initialKeep",
         status="rigorous (definition of initialKeep; Lean: FixedInducingRow / InducedBy)"),
    dict(name="units, 2^a lambda^b times sixth powers (bounded conductor | 72)", count_exp=1 / 6, kept=False, full_size=False,
         why="primitive character has conductor | 72 | Q0 = internalQ: removed; (nonprincipal anyway: no pole)",
         status="rigorous"),
    dict(name="c w^6 with c a fixed element whose conductor does not divide Q0 (e.g. a prime of norm 7)", count_exp=1 / 6, kept=True,
         full_size=False,
         why="kept, but the row character is a FIXED nonprincipal character of conductor N(c): smooth sums over ideals are O(X^-A) once X > N(c)^(1+delta) (functional equation)",
         status="rigorous for m_j > 0 (needs one plain length X_j -> infinity)"),
    dict(name="rows with conductor norm q = K^u, 0 < u < 1  (count K^((1+5u)/6))", count_exp=None, kept=True, full_size=False,
         why="nonprincipal: |A|^2 <~ X q^eps (GLH), dead for X > q^(1+delta); |S|^2 <~ D polylog (GRH)", status="heuristic (GRH/GLH)"),
    dict(name="generic rows (q ~ K)", count_exp=1.0, kept=True, full_size=False,
         why="nonprincipal, square-root cancellation on average and (GRH) pointwise", status="heuristic (GRH/GLH)"),
]


def m1_count_exp(cls, u=1.0):
    return (1 + 5 * u) / 6 if cls["count_exp"] is None else cls["count_exp"]


def reject_M1(a, s, m1, m2, ctx=None):
    """reject iff a class that SURVIVES initialKeep has FULL-SIZE sums and  count + (a + s) > M."""
    for cls in DEGENERATE_CLASSES:
        if cls["kept"] and cls["full_size"]:
            if m1_count_exp(cls) + a + s > M:
                return True, cls["name"]
    return False, "no kept row has a pole: principal rows are removed by initialKeep, kept low-conductor rows cancel"


def reject_M1_unmasked(a, s, m1, m2, ctx=None):
    """COUNTERFACTUAL (positive control): if initialKeep did NOT remove the principal rows w^6."""
    for cls in DEGENERATE_CLASSES:
        if cls["full_size"]:
            if m1_count_exp(cls) + a + s > M:
                return True, cls["name"]
    return False, ""


# ----------------------------------------------------------------------------------------------------------
# Mechanism 2: large-sieve sharpness / duality / alignment
# ----------------------------------------------------------------------------------------------------------
KNOBS = {
    "t, height, v_i": "smooth phases N(.)^{it}, (N/D)^{iv} (polynomially penalised): cannot imitate a finite-order character",
    "theta_i": "ray-class characters of the FIXED finite group, trivial on the pool (identity class): inert",
    "profiles, Phi": "smooth in N(I)/X ; Phi weights rows by norm value only (monotone: the full sum is the worst)",
    "eta, eta0, Q, rayModulus, H": "fixed finite-conductor twists; they align only with rows whose primitive character has conductor | Q0: exactly the removed rows",
}


def reject_M2(a, s, m1, m2, ctx=None):
    """reject iff some admissible datum aligns with a KEPT row (or a power-sized set of kept rows) so that the classical barrier a + s > M applies.
    Alignment needs a coefficient vector correlated with a row; the admissible vectors are smooth in N(.) and the only fixed-conductor twists
    correlate with rows removed by initialKeep.  Numerics (m2_alignment.log, m5_welch.log): best-aligned single-row energy / K << 1."""
    return False, "no admissible alignment with a kept row (see KNOBS)"


# ----------------------------------------------------------------------------------------------------------
# Mechanism 3: the diagonal term
# ----------------------------------------------------------------------------------------------------------
def diagonal_exponent(a, s):
    """exponent x with  E_diag = K_eff * (sum_n a_n^2 / T)  <~  Z^{M + x}:  a_n <= B d_{k+2}(n) with the divisor bound d_k(n) << n^eps,
    sum a_n <= B * #tuples <= B*C*T  =>  sum a_n^2 / T <= C B^2 d_max = O(Z^eps):  x = 0 for every (a, s)  [rigorous]."""
    return 0.0


def reject_M3(a, s, m1, m2, ctx=None):
    x = diagonal_exponent(a, s)
    return (x > 0.0), f"diagonal exponent {x} (E_diag = K * O(Z^eps))"


# ----------------------------------------------------------------------------------------------------------
# Mechanism 4: numerics
# ----------------------------------------------------------------------------------------------------------
KAPPA_THRESHOLD = 0.08  # a power law Z^kappa with kappa - 2 se above this is called a rejection (detection limit of the toy ~ 0.05-0.1)


def parse_config(name):
    mm = re.match(r"m=\(([\d.eE+-]+),([\d.eE+-]+)\)(?: w=\(([\d.,eE+-]+)\))?", name)
    m1, m2 = float(mm.group(1)), float(mm.group(2))
    slots = [float(x) for x in mm.group(3).split(",")] if mm.group(3) else []
    return m1, m2, slots


def load_numerics():
    out = []
    for fn in sorted(os.listdir(LOGDIR)):
        if not (fn.startswith("m4_") and fn.endswith(".json")):
            continue
        with open(os.path.join(LOGDIR, fn)) as f:
            data = json.load(f)
        for cname, s in data.items():
            if "kappa" not in s:
                continue
            m1, m2, slots = parse_config(cname)
            out.append(dict(file=fn, name=cname, m1=m1, m2=m2, slots=slots, a=m1 + m2, s=sum(slots), kappa=s["kappa"],
                            kse=s["kappa_se"], Zmin=s.get("fit_Zmin"), Zmax=s.get("fit_Zmax"), n=s.get("fit_rows")))
    return out


_NUM_CACHE = None


def numerics_near(a, s, da=0.026, ds=0.0126, only_nonrandom=True):
    global _NUM_CACHE
    if _NUM_CACHE is None:
        _NUM_CACHE = load_numerics()
    res = [r for r in _NUM_CACHE if abs(r["a"] - a) <= da and abs(r["s"] - s) <= ds]
    if only_nonrandom:
        res = [r for r in res if "random" not in r["file"]]  # the random-model runs are comparisons, not evidence about the Lean energy
    return res


def reject_M4(a, s, m1, m2, ctx=None):
    res = numerics_near(a, s)
    if not res:
        return False, "not sampled"
    worst = max(res, key=lambda r: r["kappa"] - 2 * r["kse"])
    bad = worst["kappa"] - 2 * worst["kse"] > KAPPA_THRESHOLD
    return bad, f"worst fitted kappa {worst['kappa']:+.3f}+-{worst['kse']:.3f} ({worst['name']}, Z {worst['Zmin']:.0e}-{worst['Zmax']:.0e})"


# ----------------------------------------------------------------------------------------------------------
# Mechanism 5: frame / Welch bounds
# ----------------------------------------------------------------------------------------------------------
def welch_lower_bound_exponent(a, s, M=M):
    """lambda_max >= max(K, N) for FREE unimodular coefficients (rigorous): exponent of  sup_a E / T-normalised  is  max(M, a + s)."""
    return max(M, a + s)


def reject_M5(a, s, m1, m2, ctx=None):
    """Welch gives  sup over FREE coefficient vectors of  E >= Z^{max(M, a+s)} ; this rejects (a,s) iff the Lean data can realise a (near-)extremal vector.
    The admissible vectors are rigid (smooth in N(.)): numerically their Rayleigh quotient is ~ K, not max(K, N)  (m5_welch.log)."""
    return False, "Welch-extremal vectors are not admissible (rigid, smooth coefficients); best admissible Rayleigh quotient ~ K"


MECHANISMS = [
    ("M1 degenerate rows", reject_M1),
    ("M2 alignment / duality", reject_M2),
    ("M3 diagonal term", reject_M3),
    ("M4 small-scale numerics", reject_M4),
    ("M5 frame / Welch", reject_M5),
]
