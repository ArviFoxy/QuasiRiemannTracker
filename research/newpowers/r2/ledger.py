"""ledger.py -- amplifier ledger calculus for the source steps (R2).

Everything here is bookkeeping in log-scale exponents (units of log U).  Status of each rule is stated in
the report R2_ledger.md; short key used in comments:
  [Lean]  the identity is a theorem in a built Lean tree (file cited)
  [der]   my own derivation from the Lean-checked Gauss-sum identities + the Lean coordinates
  [hyp]   hypothesis that needs an analytic lemma that is NOT in the library

Amplifier of type (m, k) acting on a selected block of VOLUME d  (d = sum of slot widths, i.e. log_U of the
number of block products D):
    m  = multiplicity of the block in the column (column contains D^m;  m = 0 = outside pool prime p)
    k  = dilation exponent (frequency h -> D^k h)
    twist-free  <=>  k = -2m (mod 6)   for a block in the column  (Gauss multiplicativity + sextic reciprocity)
                     k = 0 (mod 6)     for an outside pool prime
Per unit of volume d:
    e  = RAW saving         (= 1 from the volume of the residual, +1 more if the Cauchy-Schwarz over the block runs over a
                              divisor-bounded set, which happens exactly when m >= 2: g(D^m,h) is supported on D^(m-1) || h)
    c  = scale cost         (= 2*m  [columns shrink by m*d, enters x2 twice]  +  k  [MAIN radius shift];  pool: k)
    r  = width removed from the parent's slot width  (1 for a block, 0 for a pool)
LOW payment of a mixture  sum_T x_T (e_T + q r_T - c_T q beta),  beta = B0/L0.
"""
from dataclasses import dataclass
from fractions import Fraction as Fr


@dataclass(frozen=True)
class Amp:
    name: str
    m: int          # block multiplicity in the column (0 = pool prime outside the column)
    k: int          # dilation exponent
    e: float        # RAW saving per unit volume
    c: float        # scale cost per unit volume
    r: float        # parent slot width removed per unit volume
    twist: int      # order of the leftover twist after dilation (1 = none)
    status: str     # what is known


def twist_free_k(m):
    """minimal dilation exponent (applied to h) making the leftover twist trivial.  [Lean for m=0,1 (CA3, GaussTransfer);
    m=2: square_twist (Collision/SquareGauss.lean) + [der]]"""
    if m == 0:
        return 6
    return (-2 * m) % 6


def twist_free_j(m):
    """exponent j of D on H' (h = D^(m-1) H') in the twist-free residual, reduced mod 6 by the coprime pool identity
    g(n, D^6 x) = g(n, x) ((n,D)=1):  j = ((4m mod 6) + m - 1) mod 6   (m=1..5 -> 4,3,2,1,0).  Then c = m + 1 + j = 6 for m=1..5."""
    return (((4 * m) % 6) + m - 1) % 6


def leftover_twist_order(m, k):
    """order of chi_n(D)^(2m+k) (chi has order 6); 1 = twist free.  Pool (m=0): chi_u(p)^k."""
    j = (2 * m + k) % 6 if m > 0 else k % 6
    from math import gcd
    return 6 // gcd(j, 6) if j else 1


def block_amp(m, k=None, cs_gain=None):
    """ledger of a block of multiplicity m with dilation k (twist-free default)."""
    if k is None:
        k = twist_free_k(m)
    if cs_gain is None:
        cs_gain = 1 if m >= 2 else 0       # support D^(m-1)||h  => C-S over a divisor-bounded set  [der]
    e = 1 + cs_gain
    c = 2 * m + k
    if m >= 1 and k == twist_free_k(m):
        c = m + 1 + twist_free_j(m)          # reduced residual exponent (m=4,5: c = 6, not 12)
    return Amp(f"block m={m} k={k}", m, k, e, c, 1.0, leftover_twist_order(m, k), "")


POOL = Amp("pool p^6 (Collet)", 0, 6, 1.0, 6.0, 0.0, 1, "Lean: CA3/CA5, Collet tree")
SIMPLE = Amp("D^4 transfer (Sil)", 1, 4, 1.0, 6.0, 1.0, 1, "Lean: PR83 selected_row_fourth_one, fourth_scale, envelope_identity")
DOUBLED = Amp("D^2 transfer, squared block", 2, 2, 2.0, 6.0, 1.0, 1, "identity Lean (square_twist); ledger [der]; needs doubled input")
CUBED = Amp("D^0 transfer, cubed block", 3, 0, 2.0, 6.0, 1.0, 1, "[der]; columns not cube-free")


def unit_payment(a: Amp, q, beta):
    """LOW payment per unit volume: e + q r - c q beta     (>=0 needed;  PR83: 1 + q - 6 q beta)"""
    return a.e + q * a.r - a.c * q * beta


def barrier_Lambda(a: Amp, q, B0):
    """smallest Lambda_0 = L0 with non-negative unit payment:  c q B0 / (e + q r)   [PR83 native barrier: 6 q B/(1+q)]"""
    return a.c * q * B0 / (a.e + q * a.r)


def qinf(L, B, types, f=0.999, qmax=0.75):
    """largest LOW threshold q for which some mixture of the given types has non-negative payment in the limit v->0:
         q <= f e L / (c B - r L)    (PR83: dens -> f L/(6B-L)).  capped at qmax = 3/4 (HIGH range)."""
    best = 0.0
    for a in types:
        den = a.c * B - a.r * L
        if den <= 0:
            return qmax
        best = max(best, f * a.e * L / den)
    return min(qmax, best)


def blend(a1: Amp, a2: Amp, phi: float) -> Amp:
    """effective type when a fraction phi of the transferred width is of type a2 (same scale cost required)."""
    return Amp(f"{1-phi:.3f}*{a1.name}+{phi:.3f}*{a2.name}", a1.m, a1.k,
               (1 - phi) * a1.e + phi * a2.e, (1 - phi) * a1.c + phi * a2.c,
               (1 - phi) * a1.r + phi * a2.r, 1, "blend")


def classification_table():
    """Gauss-multiplicativity classification: twist-free (m,k), their (e,c,r) and the dominated twisted variants."""
    rows = []
    for m in (0, 1, 2, 3, 4, 5):
        k = twist_free_k(m)
        if m == 0:
            a = POOL
        else:
            a = block_amp(m, k)
        rows.append((m, k, a.e, a.c, a.r))
    return rows


if __name__ == "__main__":
    print("twist-free (m,k) and (e,c,r) per unit volume:")
    for row in classification_table():
        print("  m=%d  k=%d  e=%g c=%g r=%g" % row)
    print("native barrier at q=3/4 (B0=1):",
          {a.name: round(barrier_Lambda(a, 0.75, 1.0), 4) for a in (POOL, SIMPLE, DOUBLED, CUBED)},
          " 18/7 =", round(18 / 7, 4))
    for a in (POOL, SIMPLE, DOUBLED):
        print("unit payment at q=0.6, L=2.2, B=0.978 :", a.name, round(unit_payment(a, 0.6, 0.978 / 2.2), 4))
    # check: PR83 step LOW identity from the Lean ds_defect_aux / ds_low_aux algebra
    import sympy as sp
    B0, L0, L, v, u, q, S, s0 = sp.symbols("B0 L0 L v u q S s0")
    # F := P_C + L0 s - B0 H, with P_C <= B - L S, s <= S - u, H = 1 - 6 u, B = B0 - dL s0, dL = L0 - L  (StepGates.lean:122-132)
    dL = L0 - L
    B = B0 - dL * s0
    F = (B - L * S) + L0 * (S - u) - B0 * (1 - 6 * u)
    target = dL * (S - s0) + (6 * B0 - L0) * u
    print("PR83 defect identity  F - [dL v + (6B0-L0)u] =", sp.simplify(F - target))
    # generalisation: amplifier (e,c,r):   H = 1 - c u,   s <= S - r u
    e, c, r = sp.symbols("e c r")
    Fg = (B - L * S) + L0 * (S - r * u) - B0 * (1 - c * u)
    tg = dL * (S - s0) + (c * B0 - r * L0) * u
    print("generalised defect identity   F - [dL v + (c B0 - r L0)u] =", sp.simplify(Fg - tg))
    # envelope identity (Side.lean:36) generalised to block multiplicity m and dilation k:  2 a - kk + qC with a = A-c0-m*u, kk = K0 - t + k*u
    A, c0, d0, q0, t, m, kk = sp.symbols("A c0 d0 q0 t m kk")
    K0 = 2 * A - c0 - d0 + q0 - 1
    env = 2 * (A - c0 - m * u) - ((K0 - t) + kk * u) + (q0 + c0 - d0)
    print("envelope 2a-k+qC = ", sp.simplify(env), "  (m=1,k=4 ->", sp.simplify(env.subs({m: 1, kk: 4})), ")")
