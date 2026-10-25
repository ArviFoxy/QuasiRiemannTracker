"""Float (numpy) mirror of the Lean source-step gates of the repeated-mark graph.

Exactly the formulas of `Finite/SourceValid2.lean` (Collet's scalar gates, weak guard and the three
special sectors) and `Finite/HighGate.lean` (the repeated-mark HIGH gate `gateG`, six branches,
amplitude classes p in [0, 1/2]), as transcribed in `../repeated-marks/lean_certs.py`.

A node is a tuple (B, L, cap, q, e, r, f). `margins(n, low, h, b)` returns the smallest normalized
margin of every gate family at width b:
  scalar  : min of the 16 scalar gates and the weak guard,
  sector  : min over nu in [q, 3/4] of the three special-sector gates (densityGate j = 6, 7, 8),
  high    : min over nu in [q, 3/4], p in [0, 1/2] and the six branches of
            gateG / (gateM (15 - 6 nu)) = 1 - base + facetVal - fee   (the uncleared HIGH margin).
"""
import numpy as np

KN = 11243277/2500000
FINE = (1e-17, 1e-12, 1e-10)
COLLET = (1e-12, 1e-8, 1e-7)
CAPMAX = 549989/10000000


def node(B, L, cap, q, fees=FINE):
    return (B, L, cap, q) + tuple(fees)


def basics(n, low, b):
    B, L, cap, q, e, r, f = n
    B0, L0 = low[0], low[1]
    t = B - L*(b - e)
    den = 1 - 6*q*B0/L0
    a = (q*(b + (t - B0)/L0) + r)/den
    F = 1 - 6*a
    return t, den, a, F


def scalar_gates(n, low, b):
    B, L, cap, q, e, r, f = n
    B0, L0, cap0 = low[0], low[1], low[2]
    t, den, a, F = basics(n, low, b)
    T = t + b
    Lref = 49/100 - KN*b
    g = [den, b - 2*e, a, 1/75 - a, F - T/2 - 4*e,
         B0*F - t - b - 4*e, 1 - q*cap0,
         r - (q*B0/L0 + q*cap0 + 4)*e - 10*e,
         a - 20*e, Lref, 1 - Lref - 1/2 - KN*b - 10*e,
         5/6 + (499/1000)*Lref - T - 9*a - f,
         1 - T - 5*a - f, 1 - 1/50 - T - 4*a - f,
         1 - 1/50 - T - (9/2)*a - f, Lref - 7*a - f]
    weak = cap0*F - (B0*F - t)/L0
    return np.array(g), weak


def sector_gates(n, low, b, nu):
    """densityGate j = 6, 7, 8 (fixed, core, tiny) on an array of nu, divided by t = 15 - 6 nu."""
    B, L, cap, q, e, r, f = n
    t_, den, a, F0 = basics(n, low, b)
    T = t_ + b
    F = F0 - e
    t = 15 - 6*nu
    H = (a - nu*T)*t + (10 - 60*a)*nu
    fixed = H + (nu*F/2 - (1 - nu)*b - f)*t
    core = H + ((5/6)*F - (1 - nu)*b - f)*t - 10*nu*F
    tiny = H + (nu*(F - 1/50)/2 - (1 - nu)*b - f)*t - 10*nu*(1/50)
    return np.stack([fixed, core, tiny])/t


def high_gate(n, low, h, b, nu, p, copies=8):
    """Normalized HIGH margin gateG/(gateM (15 - 6 nu)) on a (nu, p) grid, all six branches.
    nu: (m,), p: (k,) -> array (6, m, k)."""
    B, L, cap, q, e, r, f = n
    t_, den, a, F0 = basics(n, low, b)
    T = t_ + b
    S = b - 2*e
    F = F0 - e
    K = copies
    BH, LH, hc = h[0], h[1], h[2]
    nu = nu[:, None]; p = p[None, :]
    tt = 15 - 6*nu
    base = (a - nu*T)*tt + (10 - 60*a)*nu + tt*(1 - 2*p)*nu*S - 10*nu*F - f*tt
    out = []
    for i in range(2):
        dI = 1.0 if i == 0 else 1 - p
        bI = 2*p*K*S if i == 0 else p*F
        for j in range(3):
            eP = 1.0 if j < 2 else LH - 2*p
            gP = 1.0 if j < 2 else LH
            hP = (2*p*S, 2*p*hc*F, 2*p*BH*F)[j]
            M = 12*nu*(dI*eP) + (5 - 6*nu)*(2*eP + dI*gP)
            N = 10*F*(dI*eP) + (5 - 6*nu)*(2*eP*bI + dI*hP)
            G = M*base + nu*tt*N
            out.append(G/(M*tt))
    return np.stack(out)


def margins(n, low, h, b, nnu=21, npp=41, copies=8, nfine=801):
    """The HIGH gate binds at nu = q: a fine p grid there, a coarse (nu, p) grid elsewhere."""
    q = n[3]
    nu = np.linspace(q, 0.75, nnu)
    p = np.linspace(0, 0.5, npp)
    sg, weak = scalar_gates(n, low, b)
    sec = sector_gates(n, low, b, nu)
    hg = high_gate(n, low, h, b, nu, p, copies)
    hq = high_gate(n, low, h, b, np.array([q]), np.linspace(0, 0.5, nfine), copies)
    return dict(scalar=min(sg.min(), weak), sector=sec.min(), high=min(hg.min(), hq.min()),
                high_at_q=hq.min(), den=sg[0], a=sg[2])


def cell_margins(n, low, h, b_left, nnu=41, npp=51):
    """Margins at both width endpoints b_left (the crossing) and the node's cap."""
    mL = margins(n, low, h, b_left, nnu, npp)
    mR = margins(n, low, h, n[2], nnu, npp)
    return mL, mR
