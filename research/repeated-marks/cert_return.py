"""Exact final-return certificate (PR #69 first-return FR4-FR22 / return NR1-NR14) for new faces C, P.

All arithmetic in Fractions.  Bivariate polynomials in (d=delta, p) are dicts {(i,j): coeff}.
For each conductor edge a closed rectangle cover of [0,3/4]x[0,1/2] is built; each rectangle
uses one count branch b with
   F_b = J_b (theta - r0 - E_base(d,C; delta,p)) - (3/4) d N_b  > 0   (tensor Bernstein, no splitting)
and, for improved branches, all FR8 admission polynomials > 0 on the upward window
[delta0,delta1] x [p0,1/2]."""
import sys, json, itertools
from fractions import Fraction as Fr
from math import comb

# ---------- bivariate polynomials ----------
def P(c=None):
    return dict(c or {})
def const(a): return {(0, 0): Fr(a)}
DEL = {(1, 0): Fr(1)}
PP = {(0, 1): Fr(1)}
def add(*ps):
    out = {}
    for q in ps:
        for k, v in q.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}
def neg(a): return {k: -v for k, v in a.items()}
def sub(a, b): return add(a, neg(b))
def smul(s, a): return {k: Fr(s)*v for k, v in a.items() if Fr(s)*v != 0}
def mul(a, b):
    out = {}
    for (i, j), u in a.items():
        for (k, l), v in b.items():
            out[(i+k, j+l)] = out.get((i+k, j+l), 0) + u*v
    return {k: v for k, v in out.items() if v != 0}
def dp(a): return {(i, j-1): j*v for (i, j), v in a.items() if j > 0}
def degs(a):
    if not a: return (0, 0)
    return (max(i for i, j in a), max(j for i, j in a))

def bernstein_min(a, box):
    """exact minimum tensor Bernstein coefficient of polynomial a on box [(d0,d1),(p0,p1)]."""
    (d0, d1), (p0, p1) = box
    n, m = degs(a)
    # substitute d = d0 + (d1-d0) u, p = p0 + (p1-p0) v
    sc = {}
    w1, w2 = d1-d0, p1-p0
    for (i, j), c in a.items():
        for s in range(i+1):
            ci = c*comb(i, s)*d0**(i-s)*w1**s
            for t in range(j+1):
                key = (s, t)
                sc[key] = sc.get(key, 0) + ci*comb(j, t)*p0**(j-t)*w2**t
    best = None
    for I in range(n+1):
        for J in range(m+1):
            b = Fr(0)
            for s in range(I+1):
                for t in range(J+1):
                    c = sc.get((s, t), 0)
                    if c:
                        b += c*Fr(comb(I, s)*comb(J, t), comb(n, s)*comb(m, t))
            best = b if best is None else min(best, b)
    return best

# ---------- parameters ----------
ETA = Fr(1, 10**7)
M_MINUS, M_PLUS, S_MINUS = Fr(2, 5), Fr(11, 25), Fr(17, 500)
R0 = Fr(1, 10**9)
K_I = Fr(11243277, 2500000)
M_H = (1 - K_I*Fr(17, 500))/2
V = sub(const(Fr(5, 6)), DEL)

def branch_affine(B, L, capped=False, zs=None):
    if capped:
        D = sub(const(3), PP); A = const(2)
        C0 = sub(const(1), smul(2*zs, PP)); coef = smul(2*zs, PP)
    else:
        D = sub(sub(const(3), PP), smul(Fr(4)/L, PP)); A = sub(const(2), smul(Fr(4)/L, PP))
        C0 = sub(const(1), smul(2*B/L, PP)); coef = smul(2*B/L, PP)
    U = mul(sub(const(1), PP), C0)
    J = add(mul(V, D), mul(mul(DEL, sub(const(1), PP)), A))
    N = add(mul(sub(const(1), DEL), J), mul(mul(V, DEL), U))
    T = add(J, mul(DEL, U))
    Rn = add(mul(A, T), mul(sub(coef, PP), J))
    Mn = sub(mul(D, T), Rn)
    return dict(D=D, A=A, C0=C0, U=U, J=J, N=N, T=T, Rn=Rn, Mn=Mn)

def branch_old(kappa):
    D = sub(sub(const(3), PP), smul(Fr(2)/(3*kappa), PP))
    C = mul(smul(2, sub(const(1), PP)), sub(const(1), smul(Fr(1)/(3*kappa), PP)))
    J = add(mul(V, D), mul(DEL, C))
    N = add(mul(sub(const(1), DEL), J), smul(Fr(1, 2), mul(mul(DEL, C), V)))
    return dict(J=J, N=N)

def admission_polys(br, B, L, s_plus, capped):
    if capped:
        zs = s_plus - ETA
        mL = M_MINUS + ETA
        mU = min(M_PLUS - ETA, M_H - ETA, (B - L*zs)/2 - ETA)
    else:
        mL = max(M_MINUS + ETA, (B - L*(s_plus - ETA))/2 + ETA)
        mU = min(M_PLUS - ETA, M_H - ETA, (B - L*(S_MINUS + ETA))/2 - ETA)
    D, A, C0, U, J, N, T, Rn, Mn = (br[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'Rn', 'Mn'))
    DJ = mul(D, J)
    polys = {
        'D': D, 'A': A, 'C0': C0, 'J': J, 'T-J': sub(T, J),
        '1.2499J-T': sub(smul(Fr(12499, 10000), J), T),
        'Rn-23/37DJ': sub(Rn, smul(Fr(23, 37), DJ)), 'DJ-Rn': sub(DJ, Rn),
        'Mn-mLDJ': sub(Mn, smul(mL, DJ)), 'mUDJ-Mn': sub(smul(mU, DJ), Mn),
        'N-tail': sub(N, mul(add(const(1), smul(-2*M_H, DEL), smul(-2*S_MINUS, mul(DEL, PP))), J)),
        'UJp-UpJ': sub(mul(U, dp(J)), mul(dp(U), J)),
    }
    if capped:
        polys['cap'] = smul(zs - S_MINUS - ETA, DJ)
    scal = {'mplus-mH': M_PLUS - M_H - ETA, 'B-2mH-L(s-+eta)': B - 2*M_H - L*(S_MINUS + ETA) - 2*ETA}
    return polys, scal

# ---------- geometry ----------
def geometry(theta, h, BP, LP, sP=Fr(1, 25)):
    ell = Fr(11, 3) - 4*theta
    x = 1 + ell - h; y = h - 2*ell
    kap = 2*theta - 1
    d0 = Fr(1, 200); dplus = h + Fr(1, 10**10)
    ds = 2*y/(1 + 6*kap*sP)
    dk = 2*y/(2 - BP + LP*sP)
    return dict(theta=theta, h=h, ell=ell, x=x, y=y, kap=kap, sP=sP, d0=d0, dplus=dplus, ds=ds, dk=dk)

def edges(G, BP, LP):
    y, kap, sP = G['y'], G['kap'], G['sP']
    CO = lambda d: min(d, 2*y - d)/(6*kap)
    CN = lambda d: min(sP*d, (2*y - (2 - BP)*d)/LP)
    E = [('old_small', G['d0'], CO(G['d0'])), ('old_peak', y, CO(y)),
         ('old_switch', G['ds'], CO(G['ds'])), ('new_switch', G['ds'], CN(G['ds']))]
    if G['dk'] < G['dplus']:
        E.append(('new_kink', G['dk'], CN(G['dk'])))
    E.append(('new_top', G['dplus'], CN(G['dplus'])))
    return E

def return_poly(br, G, d, C):
    Eb = add(const(Fr(1, 2) + 13*G['h']/75 - G['y']/2 - G['ell']/2 - Fr(9, 100)*d),
             smul(Fr(1, 2), DEL), smul(G['ell'] - C/2, mul(DEL, PP)))
    return sub(mul(br['J'], sub(const(G['theta'] - R0), Eb)), smul(Fr(3, 4)*d, br['N']))

# ---------- cover ----------
def candidates(faces, kap):
    out = [('old', branch_old(kap), None)]
    for name, (B, L, s_plus) in faces.items():
        for j in range(9):
            Bj = B - Fr(j, 4000)
            out.append((f'{name}-{j}' if j else name, branch_affine(Bj, L), (Bj, L, s_plus, False)))
            out.append((f'{name}cap-{j}' if j else f'{name}cap',
                        branch_affine(Bj, L, capped=True, zs=s_plus - ETA), (Bj, L, s_plus, True)))
    return out

ADM_CACHE = {}
def admitted(name, br, meta, window):
    key = (name, window)
    if key in ADM_CACHE: return ADM_CACHE[key]
    B, L, s_plus, capped = meta
    polys, scal = admission_polys(br, B, L, s_plus, capped)
    ok = all(v > 0 for v in scal.values())
    mn = None
    if ok:
        for k, q in polys.items():
            m = bernstein_min(q, window)
            mn = m if mn is None else min(mn, m)
            if m <= 0: ok = False; break
    ADM_CACHE[key] = (ok, mn)
    return ok, mn

def cover_edge(G, d, C, cands, box=((Fr(0), Fr(3, 4)), (Fr(0), Fr(1, 2))), depth=0, maxdepth=34, out=None):
    if out is None: out = []
    (d0, d1), (p0, p1) = box
    for name, br, meta in cands:
        rp = return_poly(br, G, d, C)
        m = bernstein_min(rp, box)
        if m <= 0: continue
        if meta is not None:
            ok, am = admitted(name, br, meta, ((d0, d1), (p0, Fr(1, 2))))
            if not ok: continue
        else:
            am = None
            if bernstein_min(br['J'], box) <= 0: continue
        out.append((name, box, m, am))
        return out
    if depth >= maxdepth:
        raise ValueError(f"cover failed at box {[(float(a), float(b)) for a, b in box]}")
    # split the longer normalized side
    if (d1-d0)/Fr(3, 4) >= (p1-p0)/Fr(1, 2):
        mid = (d0+d1)/2
        cover_edge(G, d, C, cands, ((d0, mid), (p0, p1)), depth+1, maxdepth, out)
        cover_edge(G, d, C, cands, ((mid, d1), (p0, p1)), depth+1, maxdepth, out)
    else:
        mid = (p0+p1)/2
        cover_edge(G, d, C, cands, ((d0, d1), (p0, mid)), depth+1, maxdepth, out)
        cover_edge(G, d, C, cands, ((d0, d1), (mid, p1)), depth+1, maxdepth, out)
    return out

# ---------- scalar receipt ----------
def receipt(G, BP, LP, capC, capP, sC, sP_, theta_I, tf=Fr(1, 400)):
    th, h, ell, x, y, kap, sP = (G[k] for k in ('theta', 'h', 'ell', 'x', 'y', 'kap', 'sP'))
    d0, dplus, ds, dk = G['d0'], G['dplus'], G['ds'], G['dk']
    n0 = lambda d: 1 - y/d
    zd = lambda d, t: min(sP, (BP - 2*n0(d) - 2*t)/LP)
    nmax = 1 - y/dplus + tf
    Ffl = lambda d: Fr(4, 25)*x - Fr(3, 20) - Fr(51, 100)*y + Fr(67, 100)*d - Fr(3, 20)*ell
    r = {
        'Gram_x_above_ell': x - ell, 'Gram_y_above_x': y - x, 'Gram_ell_below_one_fifth': Fr(1, 5) - ell,
        'Gram_2x_above_y_plus_ell': 2*x - y - ell,
        'conductor_small_before_peak': y - d0, 'conductor_peak_before_switch': ds - y,
        **({'conductor_switch_before_kink': dk - ds, 'conductor_kink_before_top': dplus - dk}
           if dk < dplus else {'conductor_switch_before_top': dplus - ds, 'kink_not_before_top': dk - dplus + Fr(1, 10**30)}),
        'conductor_top_before_twoy': 2*y - dplus,
        'physical_plain_lower': n0(ds) - M_MINUS - ETA,
        'physical_plain_upper': M_PLUS - ETA - (n0(dplus) + tf),
        'physical_plain_upper_lean_264_625': Fr(264, 625) - (n0(dplus) + tf),
        'shift_bound_9_50': Fr(9, 50) - (2*y/ds - 1) + Fr(1, 10**30),
        'dMinus_lower_3_4': ds - Fr(3, 4),
        'physical_width_lower': zd(dplus, tf) - S_MINUS - ETA,
        'physical_width_upper': Fr(43, 1000) - ETA - zd(ds, 0),
        'small_width_shortening': 1 - 2*nmax - Fr(9, 2)*Fr(17, 500) - ETA,
        'short_plain_shortening': 1 - Fr(2, 5) - BP/2 - (Fr(9, 2) - LP/2)*sP - ETA,
        'large_shift': (Fr(7, 18) - Fr(1, 500))*tf + (1 - BP)/18 + (LP/18 - Fr(1, 4))*sP - ETA,
        'large_shift_clipped': Fr(1, 2) - Fr(1, 500) - 1/(2*LP),
        'small_shift_cost': Fr(1, 2) - 1/(2*LP) - Fr(1, 500),
        'prime_supply': ell/dplus - Fr(1, 5),
        'capacity_domain': (2*y - dplus)/2,
        'capacity_positive_at_top': (2*y - (2 - BP)*dplus)/LP,
        'incumbent': 2*(theta_I - th),
        'feedback_kappa': kap - Fr(7, 10), 'feedback_d': 1 - dplus, 'feedback_y': Fr(1, 2) - y,
        'floor': th - (4 + y - x)/6 - Fr(1, 200) - Ffl(dplus),
        'small_row': -Fr(1, 20) - (13*h/75 - y/2 + Fr(63, 50)*d0),
        'principal_w': y/20 - (1 + h)/1000 - Fr(1, 4000),
        'principal_z': h/600 - Fr(1, 1000) - Fr(1, 4000),
        'holomorphic_box': th - Fr(17, 20),
        'source_lambda_low': LP - 3, 'source_lambda_high': Fr(9, 2) - LP,
        'source_intercept': 1 - BP,
        'source_C_cap': capC - sC, 'source_P_cap': capP - sP_,
        'numerator_cap_sP_le_capP': capP - sP,
        'kappa_sub_5_288_25_784': Fr(1, 8) - Fr(5, 288) - Fr(25, 784),
    }
    return r

GLOBAL_DROP = ('small_width_shortening', 'short_plain_shortening', 'large_shift', 'physical_plain_upper',
               'physical_plain_upper_lean_264_625', 'physical_width_lower', 'physical_width_upper',
               'physical_plain_lower', 'shift_bound_9_50')

def run(theta, h, C, Pf, theta_I=Fr(8747759, 10**7), verbose=True, tf=Fr(1, 400), sP=Fr(1, 25),
        sC=Fr(11, 250), sPp=Fr(43, 1000), mode='pr69'):
    (BC, LC, capC), (BP, LP, capP) = C, Pf
    G = geometry(theta, h, BP, LP, sP)
    faces = {'C': (BC, LC, sC), 'P': (BP, LP, sPp)}
    rec = receipt(G, BP, LP, capC, capP, sC, sPp, theta_I, tf)
    if mode == 'global':
        rec = {k: v for k, v in rec.items() if k not in GLOBAL_DROP}
    bad = {k: float(v) for k, v in rec.items() if v <= 0}
    if verbose:
        print("receipt min:", min(rec.items(), key=lambda kv: kv[1])[0], float(min(rec.values())), "bad:", bad)
    cands = candidates(faces, G['kap'])
    total = []
    for name, d, Ccap in edges(G, BP, LP):
        cov = cover_edge(G, d, Ccap, cands)
        mret = min(c[2] for c in cov)
        madm = min((c[3] for c in cov if c[3] is not None), default=None)
        if verbose:
            print(f"edge {name}: {len(cov)} rectangles, min return coeff {float(mret):.3e}, "
                  f"min admission coeff {float(madm) if madm is not None else None}", flush=True)
        total += [(name,) + c for c in cov]
    return rec, total, bad

if __name__ == "__main__":
    nodes = json.load(open(sys.argv[1]))
    theta = Fr(sys.argv[2]); h = Fr(sys.argv[3])
    iC = int(sys.argv[4]) if len(sys.argv) > 4 else -1
    pP = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0395
    nC = nodes[iC]
    nP = min(nodes, key=lambda n: abs(n['pivot'] - pP))
    C = (Fr(nC['B']), Fr(nC['L']), Fr(nC['cap']))
    Pf = (Fr(nP['B']), Fr(nP['L']), Fr(nP['cap']))
    tf = Fr(sys.argv[6]) if len(sys.argv) > 6 else Fr(1, 400)
    rec, cov, bad = run(theta, h, C, Pf, tf=tf)
    print("TOTAL rectangles:", len(cov), "receipt failures:", bad)
    print("smallest receipts:", sorted(((float(v), k) for k, v in rec.items()))[:6])
