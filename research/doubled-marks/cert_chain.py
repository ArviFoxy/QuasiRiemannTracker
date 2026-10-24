"""Exact certificate for the doubled-mark source chain (rational arithmetic + Bernstein).

For each node (LOW parent = HIGH parent = previous face; the natural premise first):
  NF8 : Lam < Lam0, 0 <= b_x <= min(h, h0); HIGH parent obeys 22/23 <= B_H <= 1, Lam_H > 1, 0 <= h_H < 1
  NF10: the 17 scalar gates at b in {b_x, h}
  NF13: three special-sector density gates on nu in [q, 3/4]
  HIGH: for every branch pair (i,j) and all (nu,p) in [q,3/4]x[0,1/2]:
        H + (1-2p) nu S + nu (root_ij - xi0 Fp) - f > 0          (doubled marks, k=2)
  (C1i) slope:  nu - 1/12 - (a_ij + 2 b_ij) >= 0 on [q,3/4] x [P1,1/2], and a_ij, b_ij >= 0 on [q,3/4]x[0,1/2]
  (C1ii) for p in [0,P1], x in [0,XMAX]: f_p^{ij}(x) >= min_{i'j'} f_{1/2}^{i'j'}(x)  (piecewise cover)
"""
import sys, json, itertools
from fractions import Fraction as Fr
import sympy as sp
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bern import positive, sign_definite_rational

nu, p, x = sp.symbols('nu p x')
R = sp.Rational
E_, R_, F_ = R(1, 10**12), R(1, 10**8), R(1, 10**7)        # schedule O
K = R(11243277, 2500000)
P1 = R(9, 20)
XMAX = R(1, 4)

def Q(v): return R(Fr(v).numerator, Fr(v).denominator)

def scalars(b, B, L, q, B0, L0, h0):
    e, r, f = E_, R_, F_
    t = B - L*(b - e); T = t + b; S = b - 2*e
    den = 1 - 6*q*B0/L0
    a = (q*(b + (t - B0)/L0) + r)/den
    F = 1 - 6*a; Fp = F - e
    Lref = R(49, 100) - K*b
    z0 = (B0*F - t)/L0
    g = {
        'den': den, 'S': S, 'a': a, '1/75-a': R(1, 75)-a, 'F-T/2': F - T/2 - 4*e,
        'B0F-t-b': B0*F - t - b - 4*e, '1-qh0': 1 - q*h0,
        'r-budget': r - (q*B0/L0 + q*h0 + 4)*e - 10*e, 'a-20e': a - 20*e,
        'Lref': Lref, '1-L-1/2-Kb': 1 - Lref - R(1, 2) - K*b - 10*e,
        'centered': R(5, 6) + R(499, 1000)*Lref - T - 9*a - f,
        '1-T-5a': 1 - T - 5*a - f, '1-r0-T-4a': 1 - R(1, 50) - T - 4*a - f,
        '1-r0-T-4.5a': 1 - R(1, 50) - T - R(9, 2)*a - f, 'L-7a': Lref - 7*a - f,
    }
    guard = h0*F - z0          # weak guard, >= 0
    return g, guard, dict(t=t, T=T, S=S, a=a, F=F, Fp=Fp, b=b)

def branches(S, Fp, BH, LH, hH, pv):
    inv = {'slots2': (1, 4*pv*S), 'cap': (1/(1-pv), pv*Fp/(1-pv))}
    pl = {'slots': (1, 2*pv*S), 'wcap': (1, 2*pv*hH*Fp), 'aff': (LH/(LH-2*pv), 2*pv*BH*Fp/(LH-2*pv))}
    return inv, pl

def high_exprs(c, BH, LH, hH):
    k = R(5, 6) - nu; tn = 15 - 6*nu
    rho = 1 - 10*nu/tn; xi0 = 10/tn
    H = 1 - rho - nu*c['T'] - c['a']*(5 - 6*rho)
    inv, pl = branches(c['S'], c['Fp'], BH, LH, hH, p)
    out = {}
    for (ni, (ai, bi)), (nj, (aj, bj)) in itertools.product(inv.items(), pl.items()):
        root = (R(5, 6)*c['Fp'] + k*(bi + bj/2))/(nu + k*(ai + aj/2))
        out[(ni, nj)] = H + (1 - 2*p)*nu*c['S'] + nu*(root - xi0*c['Fp']) - F_
    return out, H, rho

def special_exprs(c, H, rho):
    r0 = R(1, 50); b = c['b']; Fp = c['Fp']
    return {'fixedind': H + nu*Fp/2 - (1-nu)*b - F_,
            'smallcore': H + (rho - R(1, 6))*Fp - (1-nu)*b - F_,
            'tiny': H + nu*(Fp - r0)/2 - (1-rho)*r0 - (1-nu)*b - F_}

def fp_branch_forms(BH, LH, hH, pv):
    """f_p^{ij}(S,F) = A_ij S + B_ij F (homogeneous), returns dict of (A,B) as expressions in nu,pv."""
    k = R(5, 6) - nu; xi0 = 10/(15 - 6*nu)
    Ssym, Fsym = sp.symbols('S_ F_')
    inv, pl = branches(Ssym, Fsym, BH, LH, hH, pv)
    out = {}
    for (ni, (ai, bi)), (nj, (aj, bj)) in itertools.product(inv.items(), pl.items()):
        root = (R(5, 6)*Fsym + k*(bi + bj/2))/(nu + k*(ai + aj/2))
        f = (1 - 2*pv)*nu*Ssym + nu*(root - xi0*Fsym)
        A = sp.diff(f, Ssym); Bc = sp.diff(f, Fsym)
        out[(ni, nj)] = (sp.simplify(A), sp.simplify(Bc))
    return out

def certify_node(node, par, HP, verbose=False):
    B, L, q, h = Q(node['B']), Q(node['L']), Q(node['q']), Q(node['cap'])
    B0, L0, h0 = par
    BH, LH, hH = HP
    rep = {}
    assert L < L0, "Lam < Lam0"
    bx = (B0 - B)/(L0 - L)
    assert 0 <= bx <= min(h, h0), "0 <= b_x <= min(h,h0)"
    assert R(22, 23) <= BH <= 1 and LH > 1 and 0 <= hH < 1, "HIGH parent domain"
    minscalar = None
    nboxes = 0
    for b in (bx, h):
        g, guard, c = scalars(b, B, L, q, B0, L0, h0)
        for kname, v in g.items():
            assert v > 0, f"scalar gate {kname} at b={float(b)}: {float(v)}"
            minscalar = v if minscalar is None else min(minscalar, v)
        assert guard >= 0, f"guard h0F-z0 at b={float(b)}: {float(guard)}"
        hx, H, rho = high_exprs(c, BH, LH, hH)
        for key, ex in hx.items():
            ok, n = sign_definite_rational(ex, [nu, p], [(q, R(3, 4)), (0, R(1, 2))])
            nboxes += n
        for key, ex in special_exprs(c, H, rho).items():
            ok, n = sign_definite_rational(ex, [nu], [(q, R(3, 4))])
            nboxes += n
    # (C1i) slopes and monotonicity
    forms = fp_branch_forms(BH, LH, hH, p)
    for key, (A, Bc) in forms.items():
        sign_definite_rational(nu - R(1, 12) - (A + 2*Bc), [nu, p], [(q, R(3, 4)), (P1, R(1, 2))], strict=False)
        sign_definite_rational(A, [nu, p], [(q, R(3, 4)), (0, R(1, 2))], strict=False)
        sign_definite_rational(Bc, [nu, p], [(q, R(3, 4)), (0, R(1, 2))], strict=False)
    rep['bx'] = bx; rep['min_scalar'] = minscalar; rep['boxes'] = nboxes
    return rep

def certify_C1ii(HP, q, verbose=False):
    """for p in [0,P1], x in [0,XMAX], nu in [q,3/4]: each f_p^{ij}(x,1) >= min_{i'j'} f_{1/2}^{i'j'}(x,1)."""
    BH, LH, hH = HP
    fp = fp_branch_forms(BH, LH, hH, p)
    fh = fp_branch_forms(BH, LH, hH, R(1, 2))
    vals_p = {k: A*x + Bc for k, (A, Bc) in fp.items()}
    vals_h = {k: A*x + Bc for k, (A, Bc) in fh.items()}
    total = 0
    for key, vp in vals_p.items():
        # try a single comparison branch on the whole box, else split the box in x and p
        boxes = [[(q, R(3, 4)), (0, P1), (0, XMAX)]]
        while boxes:
            bx = boxes.pop()
            done = False
            for kh, vh in vals_h.items():
                try:
                    sign_definite_rational(vp - vh, [nu, p, x], bx, strict=False, maxdepth=6)
                    done = True; total += 1
                    break
                except ValueError:
                    continue
            if not done:
                # split along x then p
                w0 = [R(3, 4) - q, P1, XMAX]
                w = [(bx[i][1] - bx[i][0])/w0[i] for i in range(3)]
                ax = max(range(3), key=lambda i: w[i])
                if w[ax] < R(1, 10**7):
                    raise ValueError(f"C1ii failed for {key} on {bx}")
                mid = (bx[ax][0] + bx[ax][1])/2
                b1 = list(bx); b2 = list(bx)
                b1[ax] = (bx[ax][0], mid); b2[ax] = (mid, bx[ax][1])
                boxes += [b1, b2]
    return total

if __name__ == "__main__":
    nodes = json.load(open(sys.argv[1]))
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    par = (R(1), K, R(11, 200))
    for n in nodes[:start]:
        par = (Q(n['B']), Q(n['L']), Q(n['cap']))
    worst = None
    for i, n in enumerate(nodes[start:], start):
        rep = certify_node(n, par, par)
        c1 = certify_C1ii(par, Q(n['q']))
        print(f"node {i:2d} pivot {n['pivot']}: OK  b_x={float(rep['bx']):.8f} min scalar={float(rep['min_scalar']):.3e} "
              f"bernstein boxes={rep['boxes']} C1ii boxes={c1}", flush=True)
        par = (Q(n['B']), Q(n['L']), Q(n['cap']))
    print("ALL NODES CERTIFIED")
