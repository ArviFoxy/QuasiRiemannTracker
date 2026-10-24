"""Numerical model of the final return certificate of PR #69 (Hailey Collet).

Formulas follow the paper's return chapter, eqs. (NR1)-(NR7) and (FR4)-(FR13).
E(d, C; delta, p) = 1/2 + 13h/75 - y/2 - l/2 - 9d/100 + delta/2
                    + delta*p*(l - C/2) + (3d/4) R*(kappa, delta, p)
must be <= theta - 1e-9 on the six conductor edges.
"""
import numpy as np

ETA = 1e-7
M_MINUS, M_PLUS, S_MINUS = 2/5, 11/25, 17/500


class Face:
    def __init__(self, B, Lam, s_plus, name):
        self.B, self.Lam, self.s_plus, self.name = B, Lam, s_plus, name


# PR 69 final faces (exact decimals from return.tex section 7)
FACE_C = Face(0.96226151753982, 3.14813176381578, 11/250, "C")
FACE_P = Face(0.96739031091242, 3.27307995389766, 43/1000, "P")
K_I_FINAL = 11243277/2500000           # natural cost from intermediate theta
B_P, LAM_P = FACE_P.B, FACE_P.Lam


def old_count(kappa, delta, p):
    V = 5/6 - delta
    D = 3 - p - 2*p/(3*kappa)
    C = 2*(1-p)*(1 - p/(3*kappa))
    J = V*D + delta*C
    N = (1-delta)*J + delta*C*V/2
    return N/J


def affine_count(face, delta, p, K_I, capped=False, check=True):
    """Return count exponent N/J for an affine (or capped) source branch,
    or np.inf where the admission tests (FR8) fail."""
    B, Lam, sp = face.B, face.Lam, face.s_plus
    V = 5/6 - delta
    if capped:
        zs = sp - ETA
        D = 3 - p
        A = 2.0 + 0*p
        C0 = 1 - 2*p*zs
        coef = 2*p*zs
    else:
        D = 3 - p - 4*p/Lam
        A = 2 - 4*p/Lam
        C0 = 1 - 2*p*B/Lam
        coef = 2*p*B/Lam
    U = (1-p)*C0
    J = V*D + delta*(1-p)*A
    N = (1-delta)*J + V*delta*U
    T = J + delta*U
    Rn = A*T + (coef - p)*J
    Mn = D*T - Rn
    R = N/J
    if not check:
        return R
    mH = (1 - K_I*S_MINUS)/2
    if capped:
        mL = M_MINUS + ETA
        mU = np.minimum(np.minimum(M_PLUS - ETA, mH - ETA), (B - Lam*zs)/2 - ETA)
    else:
        mL = np.maximum(M_MINUS + ETA, (B - Lam*(sp - ETA))/2 + ETA)
        mU = np.minimum(np.minimum(M_PLUS - ETA, mH - ETA),
                        (B - Lam*(S_MINUS + ETA))/2 - ETA)
    ok = (D > 0) & (A > 0) & (C0 > 0) & (J > 0) & (T - J > 0)
    ok &= (12499/10000)*J - T > 0
    ok &= Rn - (23/37)*D*J > 0
    ok &= D*J - Rn > 0
    ok &= Mn - mL*D*J > 0
    ok &= mU*D*J - Mn > 0
    ok &= N - (1 - 2*delta*mH - 2*delta*p*S_MINUS)*J > 0
    ok &= (M_PLUS - mH - ETA) > 0
    ok &= (B - 2*mH - Lam*(S_MINUS + ETA) - 2*ETA) > 0
    if capped:
        ok &= (zs - S_MINUS - ETA)*D*J > 0
    return np.where(ok, R, np.inf)


def count_envelope(kappa, delta, p, faces, K_I, weaker=8):
    R = old_count(kappa, delta, p)
    for f in faces:
        for j in range(weaker + 1):
            g = Face(f.B - j/4000, f.Lam, f.s_plus, f.name)
            R = np.minimum(R, affine_count(g, delta, p, K_I))
            R = np.minimum(R, affine_count(g, delta, p, K_I, capped=True))
    return R


def geometry(c, h):
    theta = 1 - c
    ell = 4*c - 1/3
    x = 1 + ell - h
    y = h - 2*ell
    kappa = 1 - 2*c
    return theta, ell, x, y, kappa


def edges(c, h, BP=B_P, LP=LAM_P):
    theta, ell, x, y, kappa = geometry(c, h)
    ds = 2*y/(1 + 6*kappa/25)
    dk = 2*y/(2 - BP + LP/25)
    dp = h + 1e-10
    d0 = 1/200
    CO = lambda d: min(d, 2*y - d)/(6*kappa)
    CN = lambda d: min(d/25, (2*y - (2 - BP)*d)/LP)
    return [("old_small", d0, CO(d0)), ("old_peak", y, CO(y)),
            ("old_switch", ds, CO(ds)), ("new_switch", ds, CN(ds)),
            ("new_kink", dk, CN(dk)), ("new_top", dp, CN(dp))]


def E_minus_theta(c, h, delta, p, faces=(FACE_C, FACE_P), K_I=K_I_FINAL,
                  BP=B_P, LP=LAM_P, count=None):
    theta, ell, x, y, kappa = geometry(c, h)
    if count is None:
        Rs = count_envelope(kappa, delta, p, faces, K_I)
    else:
        Rs = count(kappa, delta, p)
    worst = -np.inf
    where = None
    for name, d, C in edges(c, h, BP, LP):
        E = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + delta/2
             + delta*p*(ell - C/2) + 0.75*d*Rs)
        g = E - theta
        i = np.unravel_index(np.argmax(g), g.shape)
        if g[i] > worst:
            worst, where = g[i], (name, float(delta[i]), float(p[i]))
    return worst, where


def grid(nd=601, npp=301):
    d = np.linspace(0, 0.75, nd)
    pp = np.linspace(0, 0.5, npp)
    return np.meshgrid(d, pp, indexing="ij")


if __name__ == "__main__":
    c69, h69 = 1252270103/10000000000, 8001009617/10000000000
    dl, pp = grid()
    w, where = E_minus_theta(c69, h69, dl, pp)
    print("PR69 parameters: max(E - theta) =", w, "at", where)
