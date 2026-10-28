"""Count / gain models for the marked HIGH leaf (all float; vectorised numpy).

Notation (Lean/paper):  nu = delta = zero density, p = amplitude class (mean slot amplitude / nu, 0..1/2),
S = retained marked width, Q = envelope H, kappa = plain cost parameter (3/4 natural, 2*theta_rec-1 bootstrapped).
Every model returns the *count saving* cs = (1-R)*Q  (so the HIGH ledger is  J = cs + u - nu*(B-(L-2x)w-2x u) >= 0)
"""
import numpy as np

SIG_LIB = 7 / 37          # the library's slot-supply condition  (7/37) d <= sum widths


def rho(nu):
    return 1 - 10 * nu / (15 - 6 * nu)


# ---------------------------------------------------------------- (a) Cycle25 rowCount = Cycle61 countingR
def rowCount(d, p, k):
    """Cycle25DetectorRowCount.rowCount = Cycle61.Arithmetic.Bernstein.countingR  (Lean Feedback.lean:17)"""
    b = p / (3 * k)
    den = 3 - p - 2 * b
    c = 2 * (1 - p) * (1 - b) / den
    V = 5 / 6 - d
    return 1 - d + d * c * V / (2 * (V + d * c))


# ---------------------------------------------------------------- (c) face-based count (return's branch_affine)
def branch_poly(d, p, B, L, capped=False, zs=None):
    """cert_return.branch_affine evaluated pointwise: returns (J, N); R = N/J."""
    V = 5 / 6 - d
    if capped:
        D = 3 - p
        A = 2.0 + 0 * p
        C0 = 1 - 2 * zs * p
    else:
        D = 3 - p - 4 * p / L
        A = 2 - 4 * p / L
        C0 = 1 - 2 * B * p / L
    U = (1 - p) * C0
    J = V * D + d * (1 - p) * A
    N = (1 - d) * J + V * d * U
    return J, N


def R_face(d, p, B, L, capped=False, zs=None):
    J, N = branch_poly(d, p, B, L, capped, zs)
    return N / J


def R_old(d, p, k):
    """return's `old` branch (natural kappa) == rowCount"""
    V = 5 / 6 - d
    D = 3 - p - 2 * p / (3 * k)
    C = 2 * (1 - p) * (1 - p / (3 * k))
    J = V * D + d * C
    N = (1 - d) * J + d * C * V / 2
    return N / J


# ---------------------------------------------------------------- (d) repeated-mark gain  (Gain.lean / README sec. 2-3)
def xi_roots(nu, p, S, Q, K, BH, LH, hH):
    """per-class detector root xi^K_p = min over the 2x3 branch pairs of the branch roots (Gain.lean `xiP`).
    nu, p, S, Q broadcast; K may be None/inf-like (cap-only inverse) -> pass K=0 to drop the slot branch."""
    nu, p, S, Q = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, p, S, Q)))
    w = 5 - 6 * nu
    inv = [(1 / (1 - p), p * Q / (1 - p))]
    if K:
        inv.append((np.ones_like(p), 2 * p * K * S))
    d2 = 1 - 2 * p / LH
    pl = [(np.ones_like(p), 2 * p * S), (np.ones_like(p), 2 * p * hH * Q),
          (1 / d2, (2 * p * BH * Q / LH) / d2)]
    best = None
    for (si, oi) in inv:
        for (sj, oj) in pl:
            root = (5 * Q + w * (oi + oj / 2)) / (6 * nu + w * (si + sj / 2))
            best = root if best is None else np.minimum(best, root)
    return best


def xi0(nu):
    return 10 / (15 - 6 * nu)


def f_class(nu, p, S, Q, K, BH, LH, hH):
    """f^K_p(S,Q) = (1-2p) nu S + nu (xi^K_p - xi0 Q)"""
    xi = xi_roots(nu, p, S, Q, K, BH, LH, hH)
    return (1 - 2 * p) * nu * S + nu * (xi - xi0(nu) * Q)


PGRID = np.unique(np.concatenate([np.linspace(0, 0.40, 17), np.linspace(0.40, 0.5, 41)]))


def gain_K(nu, S, Q, K, BH, LH, hH, ps=PGRID):
    """G_K = min_p f^K_p ; returns (G, argmin p).  nu,S,Q broadcast with a trailing p axis."""
    nu, S, Q = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, S, Q)))
    f = f_class(nu[..., None], ps, S[..., None], Q[..., None], K, BH, LH, hH)
    i = np.argmin(f, axis=-1)
    return np.take_along_axis(f, i[..., None], -1)[..., 0], ps[i]


if __name__ == '__main__':
    # self checks
    for nu in (0.6, 0.7):
        print('p=0: rowCount == rho', rowCount(nu, 0.0, 0.75) - rho(nu), R_face(nu, 0.0, 0.98, 2.3) - rho(nu),
              R_old(nu, 0.3, 0.75) - rowCount(nu, 0.3, 0.75))
        print('f_0 = nu S:', f_class(nu, 0.0, 0.07, 1.0, 2, 0.98, 2.3, 0.1) - nu * 0.07)
