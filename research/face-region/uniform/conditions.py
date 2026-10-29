"""Scalar sufficient conditions for HybridGatesM.high_marked of one step (spec of the Lean lemma).
Inputs: parent (B0, L0), c0 = h0 = c = 1/10, step h, slope s0, selection (A, D).  Child B = B0 - s0 h, L = L0 - h.
Every condition is a closed-form inequality in these rationals; margins are returned (all must be > 0).

Structure (see UNIFORM_STEP.md):
 P10, P11, P12 : the (1,j) facets are minimised over p at p = 1/2          (worst corner S = s0, Q = 1, w = wmax)
 C11           : facet (1,1) >= facet (1,0) at p = 1/2  (S <= h0 Q)        (automatic for c = h0)
 C0, C00, C01, C02 : the eight-copy facets stay above phi_12(1/2)           (worst corner)
 N             : Gamma_10, Gamma_12 increase in nu on [q(v), 3/4]          (derivative bound)
 V10, V12      : Gamma_10(v, q(v)), Gamma_12(v, q(v)) >= r on [0, vmax]    (two-piece dip bound, sqrt-free)
"""
import numpy as np
from math import sqrt
H0 = 0.1; C = 0.1; K = 8

def basics(B0, L0, h, s0, A, D):
    vmax = C - s0
    E0 = h + (6*B0 - L0)*A
    q0 = 0.999*L0*A/E0
    qmin = 0.999*L0*A/(h*(1 + D*vmax) + (6*B0 - L0)*A)
    umax = A*vmax/(1 + D*vmax)
    return vmax, E0, q0, qmin, umax

def y_of_w(w): return w/(10 + 3*w)
def R_of(w, B0, L0):
    x = w/(2*(5 + w)); return (L0 - 1 + x*B0)/(L0 - 1 + x*L0)
def sigma_w(w, B0, L0):
    y = y_of_w(w); return (B0 - 1 + y)/(L0 - 1 + y)

def cond(B0, L0, h, s0, A, D, verbose=False):
    vmax, E0, q0, qmin, umax = basics(B0, L0, h, s0, A, D)
    L = L0 - h; B = B0 - s0*h
    wmax = 5 - 6*qmin; wmin = 0.5
    Qmin = 1 - 6*umax
    out = {}
    W = np.linspace(wmin, wmax, 201)
    # --- P10: S(2.5(w^2+5w+10)) - Q w^2 >= 0 (worst S=s0, Q=1)
    out['P10'] = np.min(s0*2.5*(W**2 + 5*W + 10) - W**2)
    # --- P11: affine in p -> both ends (worst S=s0 for the S-terms, Q=1)
    n0 = s0*(3*W**2 + 40*W + 100) - W*(H0*W + 10*H0 + 2*W)
    n1 = s0*(4.5*W**2 + 30*W + 50) - W*(2*W + 5*H0 - 0.5*H0*W)
    out['P11'] = min(np.min(n0), np.min(n1))
    # --- P12: N12(p) <= 0 on [0,1/2]  (concave quadratic in p): f(1/2) + max(0,-f'(1/2))/2 <= 0, and f(0) <= 0
    def N12(p, w, S, Q):
        Lm = L0; Bm = B0
        c0_ = Lm*(Bm*Q*w**2 + 10*Bm*Q*w + 2*Lm*Q*w**2 - 3*Lm*S*w**2 - 40*Lm*S*w - 100*Lm*S - 2*Q*w**2 - 10*Q*w + 2*S*w**2 + 30*S*w + 100*S)
        c1_ = (-3*Bm*Lm*Q*w**2 - 10*Bm*Lm*Q*w + 4*Bm*Q*w**2 - 3*Lm**2*S*w**2 + 20*Lm**2*S*w + 100*Lm**2*S - 2*Lm*Q*w**2
               + 10*Lm*Q*w + 2*Lm*S*w**2 + 50*Lm*S*w + 100*Lm*S - 40*S*w - 200*S)
        c2_ = 4*S*(w - 5)*(3*Lm*w + 10*Lm - 2*w - 10)
        return c0_ + c1_*p + c2_*p**2, c1_ + 2*c2_*p
    # N12 is increasing in Q? decreasing in S? take worst over the corners S in {s0, C}, Q in {Qmin, 1}
    worst = -np.inf
    for S_ in (s0, C):
        for Q_ in (Qmin, 1.0):
            f_half, d_half = N12(0.5, W, S_, Q_)
            f0, _ = N12(0.0, W, S_, Q_)
            worst = max(worst, np.max(f_half + np.maximum(0, -d_half)/2), np.max(f0))
    out['P12'] = -worst                                   # need N12 <= 0
    # --- comparisons for the eight-copy facets against phi_12(1/2) = Q (R - base)
    base = 10/(10 + W); phistar = (R_of(W, B0, L0) - base)       # per unit Q
    out['C0'] = np.min(s0 - 1.0*phistar)                               # S >= Q phi*/Q  (S=s0, Q=1)
    out['C00'] = np.min(17*s0*W/(W + 10) - phistar)                    # phi_00(1/2) >= phi*
    out['C01'] = np.min(s0 + (H0*W*1.0 + 15*s0*W - 10*s0)/(W + 10) - phistar)   # phi_01(1/2) at Q=1 (Q-term helps)
    # phi_02(p) >= S - max(N02(0),N02(1/2),0)/((w+10)(L0(w+10)-10)) >= phi*
    def N02(p, S_, Q_):
        return (-B0*Q_*W**2 - 10*B0*Q_*W - 15*L0*S_*W**2 - 140*L0*S_*W + 100*L0*S_ + 10*Q_*W + p*(32*S_*W**2 + 300*S_*W - 200*S_))
    worst02 = np.inf
    for S_ in (s0, C):
        for Q_ in (Qmin, 1.0):
            npos = np.maximum(0, np.maximum(N02(0, S_, Q_), N02(0.5, S_, Q_)))
            worst02 = min(worst02, np.min(S_ - npos/((W + 10)*(L0*(W + 10) - 10)) - Q_*phistar))
    out['C02'] = worst02
    # --- N: d/dnu Gamma_12 >= nu (L0-1)|sigma'| - (L0-1)(sigma(qmin)-s0)^+ - umax C'_max ; same order for Gamma_10
    NU = np.linspace(qmin, 0.75, 201); Wn = 5 - 6*NU
    yy = y_of_w(Wn)
    dsig = 60*(L0 - B0)/((10 + 3*Wn)**2*(L0 - 1 + yy)**2)
    Rn = R_of(Wn, B0, L0)
    dR = np.gradient(Rn, NU)
    Cp = 6*Rn + 6*NU*dR - 1
    out['N'] = np.min(NU*(L0 - 1)*dsig - (L0 - 1)*max(0.0, sigma_w(wmax, B0, L0) - s0) - umax*np.max(np.abs(Cp)) - (L0 - 1 - h)*0)
    # --- V12 and V10: two-piece bound.  Piece I: v in [0, v1], v1 = k1/D; Piece II: [v1, vmax].
    def sig_q(q): return sigma_w(5 - 6*q, B0, L0)
    Qs = np.linspace(qmin, q0, 401)
    Ls = np.max(np.abs(np.gradient(sig_q(Qs), Qs)))            # Lipschitz of sigma in q on [qmin, q0]
    C0v = 6*q0*R_of(5 - 6*q0, B0, L0) - q0 - 1                 # C(q) <= C(q0)
    m0 = (L0 - 1)*(s0 - sig_q(q0))
    beta = (L0 - 1 - h) - (L0 - 1)*Ls*q0*h*D/E0
    best = -np.inf
    for k1 in (1.0, 2.0, 3.0, 4.0, 6.0):
        v1 = min(k1/D, vmax)
        q1 = 0.999*L0*A/(h*(1 + D*v1) + (6*B0 - L0)*A)
        b = q1*beta; g = A*C0v
        # piece I: f(v) = q1 (m0 + beta v) - g v/(1+Dv) >= q1 m0 + (M - b - g)/D,  M^2 <= 4 b g
        M = 2*sqrt(max(b*g, 0.0))*(1 - 1e-12)
        pieceI = (q1*m0 + (M - b - g)/D if g > b else q1*m0) - (q0 - q1)*max(0.0, -m0)
        # piece II: q(v) >= qmin; X(v) >= m0 + beta v1; u <= A/D... use u(v) <= u(vmax)
        X2 = m0 + beta*v1
        pieceII = (qmin*X2 if X2 >= 0 else q0*X2) - C0v*min(A/D, umax)
        best = max(best, min(pieceI, pieceII))
    out['V12'] = best if beta >= 0 else -1.0
    out['beta'] = beta
    out['m0'] = m0
    return out

if __name__ == '__main__':
    import json
    from fractions import Fraction as Fr
    steps = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..', 'chain', 'steps_f050_dL200.json')))
    for idx in [0, 32, 64, 96, 120, 127, 128]:
        st = steps[idx]
        B0, L0, Bc, Lc, A, D = (float(Fr(st[k])) for k in ('B0', 'L0', 'B', 'L', 'A', 'D'))
        h = L0 - Lc; s0 = (B0 - Bc)/h
        o = cond(B0, L0, h, s0, A, D)
        print('step %3d ' % (idx + 1) + ' '.join('%s=%+.2e' % (k, v) for k, v in o.items()))

def cond_V10(B0, L0, h, s0, A, D):
    """Gamma_10(v,nu) = nu(L0-1+y)(s0 - sigma(nu)) + nu(L0-1-h+y) v - u C10(nu),  C10 = 5 nu (1-y) - 1; at nu = q(v)."""
    vmax, E0, q0, qmin, umax = basics(B0, L0, h, s0, A, D)
    def sig_q(q): return sigma_w(5 - 6*q, B0, L0)
    def y_q(q): return y_of_w(5 - 6*q)
    Qs = np.linspace(qmin, q0, 401)
    Ls = np.max(np.abs(np.gradient(sig_q(Qs), Qs)))
    ymin = y_q(q0); ymax = y_q(qmin)
    C10 = np.max(5*Qs*(1 - y_q(Qs)) - 1)
    m0 = (L0 - 1 + ymin)*(s0 - sig_q(q0)) if s0 >= sig_q(q0) else (L0 - 1 + ymax)*(s0 - sig_q(q0))
    beta = (L0 - 1 - h + ymin) - (L0 - 1 + ymax)*Ls*q0*h*D/E0
    best = -np.inf
    for k1 in (1.0, 2.0, 3.0, 4.0, 6.0):
        v1 = min(k1/D, vmax)
        q1 = 0.999*L0*A/(h*(1 + D*v1) + (6*B0 - L0)*A)
        b = q1*beta; g = A*C10
        M = 2*sqrt(max(b*g, 0.0))*(1 - 1e-12)
        pieceI = (q1*m0 + (M - b - g)/D if g > b else q1*m0) - (q0 - q1)*max(0.0, -m0)
        X2 = m0 + beta*v1
        pieceII = (qmin*X2 if X2 >= 0 else q0*X2) - C10*min(A/D, umax)
        best = max(best, min(pieceI, pieceII))
    return best if beta >= 0 else -1.0

def cond_1d(B0, L0, h, s0, A, D, qf=0.5):
    """Endpoint conditions of the 12 one-variable gates (c0 = c = 1/10)."""
    vmax, E0, q0, qmin, umax = basics(B0, L0, h, s0, A, D)
    L = L0 - h; B = B0 - s0*h
    o = {}
    o['q_floor'] = qmin - qf
    o['q_upper'] = 0.75 - q0
    o['H_lower'] = 0.1 - 6*umax
    o['ret_cap'] = 0.1*(1 - 6*umax) - (C - umax)
    o['ref_upper'] = 1/3 - 2*C - 3*umax
    def convex_gate(alpha, beta, gamma):
        v1 = min(1/D, vmax)
        return min(alpha, alpha + (beta - gamma*A)*v1, alpha + beta*v1 - gamma*A/D, alpha + beta*vmax - gamma*A/D)
    o['principal'] = convex_gate(1 - B + (L - 2)*s0, L - 2, 4.5)
    o['second_ref'] = convex_gate(0.05 + 1.5*(1 - B) + (1.5*L - 2.5)*s0, 1.5*L - 2.5, 4.5)
    o['second_diag'] = convex_gate(1 - B + (L - 1)*s0, L - 1, 4.0)
    return o
