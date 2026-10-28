"""Count-saving models for the HIGH ledger of the density leaf.   cs(var, nu, x, S, Q, par) = (1-R)*Q  [or nu*xi for (d)]

    HIGH ledger (v = slot width above the crossing s0; w = s0+v root slot width; u = selected width; s = w-u retained;
                 Q = H = 1-6u envelope; x = mean slot amplitude / nu of the HIGH class, 0..1/2):
        J_x = cs(nu,x; s,Q) + u - nu*(B - (L-2x) w - 2x u)  >= 0   for all nu in [q,3/4], x in [0,1/2].
variants
    pr83   unmarked rho(nu)                       (PR 83 as is)
    a      black box: rowCount(nu, p=x*min(s/sigma,1), kappa), sigma = 7/37 (dummy zero-amplitude slots)
    u      ideal rowCount(nu, p=x, kappa)         (undiluted; supply assumed free)  [B2's "undiluted"]
    b0     limited supply sigma=s, p=x: B2 markedcount re-derivation (full needed width only)
    b1     limited supply sigma=s, p=x, partial z=min(s, needed) allowed (Lemma A_1 type)
    c      face-based count (return's C branch with the parent face (B0,L0)) with black-box dilution p=x*min(s/sigma,1)
    cu     same, undiluted p=x                      (== d_infinity: same detector, unlimited supply)
    cc     face-based *capped* branch zs = s (supply-limited plain witness), p = x undiluted  [sensitivity]
    dK     repeated marks (PR 73/76): K copies, p=x, HIGH parent face (B0,L0,h0): cs = nu*xi^K_p(S=s,Q)
par: kappa, B0, L0, h0, sigma (optional, default 7/37), shift_R (optional: R -> R - shift_R, i.e. cs += shift_R*Q)
"""
import numpy as np
import counts as C
import tables as T

SIG_LIB = 7 / 37


def cs(var, nu, x, S, Q, par):
    nu, x, S, Q = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, x, S, Q)))
    sig = par.get('sigma', SIG_LIB)
    kap = par['kappa']
    if var == 'pr83':
        out = (1 - C.rho(nu)) * Q
    elif var == 'a':
        out = (1 - C.rowCount(nu, x * np.minimum(S / Q / sig, 1.0), kap)) * Q
    elif var == 'u':
        out = (1 - C.rowCount(nu, x, kap)) * Q
    elif var in ('b0', 'b1'):
        out = (1 - T.R_b(nu, x, S / Q, kap, var == 'b1')) * Q
    elif var == 'c':
        out = (1 - C.R_face(nu, x * np.minimum(S / Q / sig, 1.0), par['B0'], par['L0'])) * Q
    elif var == 'cu':
        out = (1 - C.R_face(nu, x, par['B0'], par['L0'])) * Q
    elif var == 'cc':
        out = (1 - C.R_face(nu, x, par['B0'], par['L0'], capped=True, zs=S / Q)) * Q
    elif var.startswith('d'):
        K = int(var[1:])
        out = nu * C.xi_roots(nu, x, S, Q, K, par['B0'], par['L0'], par['h0'])
    else:
        raise ValueError(var)
    return out + par.get('shift_R', 0.0) * Q


ALL = ['pr83', 'a', 'b0', 'b1', 'c', 'cu', 'u', 'd1', 'd2', 'd3', 'd4']
