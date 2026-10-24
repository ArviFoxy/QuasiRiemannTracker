"""ss_fb: model of the feedback source step (feedback.tex NF4, NF10-NF13).
gates(...) returns the minimum reserve over all gates at both width endpoints.
Structural knobs (default = PR69):
  kamp : radius/density exchange of the LOW amplifier (6 in PR69: F = 1 - kamp*a,
         LOW denominator 1 - kamp*q*B0/Lam0)
  lowrate : erasure cost per unit slot width in LOW as a multiple of q (1 in PR69)
  xi_fn : optional override of the HIGH gain (function of nu,S,Fp,face)
"""
import numpy as np
K_I = 4.4978269 # natural cost used in sources; feedback uses 4.4973108
NU = None

def six_gains(nu, S, Fp, BH, LH, hH):
    w = 5-6*nu; tn = 15-6*nu
    g1 = 3*nu*w/tn*S
    g2 = 2*nu*w/tn*S + nu*w*hH/tn*Fp
    D13 = LH*tn-10
    g3 = 2*nu*w*(LH-1)/D13*S + nu*w*(BH*tn-10)/(tn*D13)*Fp
    g4 = nu*w/(10+3*w)*S + 2*nu*w**2/(tn*(10+3*w))*Fp
    g5 = (2*nu*w**2/(tn*(10+3*w)) + nu*w*hH/(10+3*w))*Fp
    D23 = LH*(10+3*w)-(10+2*w)
    g6 = nu*w*(2*w*(LH-1)+BH*tn-10)/(tn*D23)*Fp
    return np.minimum.reduce([g1,g2,g3,g4,g5,g6])

def three_gains(nu, S, Fp):
    d=5-2*nu; w=5-6*nu
    phi=nu*w/d
    A=14*nu*w/(115-54*nu); D=2*nu*w**2/(3*d*(115-54*nu)); C=16*nu*w**2/(3*d*(185-138*nu))
    return np.minimum.reduce([phi*S, A*S+D*Fp, C*Fp])

def gates_at(b, B, Lam, q, B0, L0, h0, HP, sched=(1e-17,1e-12,1e-10), K=4.4973108,
             kamp=6.0, lowrate=1.0, rho_fn=None, gain_fn=None, nnu=801, detail=False):
    e, r, f = sched
    t = B - Lam*(b-e); T = t+b; S = b-2*e
    qq = q*lowrate
    den = 1 - kamp*qq*B0/L0
    a = (qq*(b+(t-B0)/L0)+r)/den
    F = 1-kamp*a; Fp = F-e
    Lref = 49/100 - K*b
    z0 = (B0*F-t)/L0
    g = {}
    g['den'] = den; g['S'] = S; g['a'] = a; g['1/75-a'] = 1/75-a
    g['F-T/2'] = F-T/2-4*e; g['B0F-t-b'] = B0*F-t-b-4*e; g['1-qh0'] = 1-q*h0
    g['Lref'] = Lref; g['1-L-1/2-Kb'] = 1-Lref-1/2-K*b-10*e
    g['centered'] = 5/6+0.499*Lref-T-9*a-f
    g['1-T-5a'] = 1-T-5*a-f; g['1-r0-T-4a'] = 1-1/50-T-4*a-f
    g['1-r0-T-4.5a'] = 1-1/50-T-4.5*a-f; g['L-7a'] = Lref-7*a-f
    g['h0F-z0'] = h0*F-z0 + 1e-30
    nu = np.linspace(q, 0.75, nnu)
    w = 5-6*nu; tn = 15-6*nu
    rho = 1-10*nu/tn if rho_fn is None else rho_fn(nu)
    import os as _os
    _noamp = _os.environ.get('HIGH_NOAMP','0')=='1'
    H = 1-rho-nu*T-(0 if _noamp else a)*(5-6*rho)
    if gain_fn is not None:
        G = gain_fn(nu, S, (1-e) if _noamp else Fp)
    elif HP is None:
        G = three_gains(nu, S, Fp)
    else:
        G = six_gains(nu, S, Fp, *HP)
    reg = H + G - f
    i = np.argmin(reg); g['HIGH'] = (reg[i], nu[i])
    r0 = 1/50
    sp = {'fixedind': H+nu*Fp/2-(1-nu)*b, 'smallcore': H+(rho-1/6)*Fp-(1-nu)*b,
          'tiny': H+nu*(Fp-r0)/2-(1-rho)*r0-(1-nu)*b}
    for k, v in sp.items():
        i = np.argmin(v); g['sp:'+k] = (v[i]-f, nu[i])
    return g

def minres(g):
    vals = []
    for k, v in g.items():
        if k in ('a','den','S'): 
            if (v if not isinstance(v,tuple) else v[0]) <= 0: return -1, k
            continue
        x = v[0] if isinstance(v, tuple) else v
        vals.append((x, k))
    return min(vals)

def check(B, Lam, q, h, B0, L0, h0, HP, **kw):
    if not (Lam < L0): return (-1, 'Lam>=L0'), None
    bx = (B0-B)/(L0-Lam)
    if not (0 <= bx <= min(h, h0)): return (-1, 'bx'), bx
    m = min(minres(gates_at(bx, B, Lam, q, B0, L0, h0, HP, **kw)),
            minres(gates_at(h, B, Lam, q, B0, L0, h0, HP, **kw)))
    return m, bx

if __name__ == "__main__":
    g5C = (0.96226354319698, 3.14817962398374, 0.0549989)
    g4C = (0.96226831325612, 3.14829232960439, 0.0549989)
    g6C = (0.96226151753982, 3.14813176381578, 0.54526708734661, 0.0549989)
    m, bx = check(g6C[0], g6C[1], g6C[2], g6C[3], *g5C, HP=g4C)
    print("g6_C from g5_C (LOW) g4_C (HIGH): min reserve", m, "b_x", bx)
    for b in (bx, g6C[3]):
        g = gates_at(b, g6C[0], g6C[1], g6C[2], *g5C, HP=g4C)
        print('b=',b, sorted([(v[0] if isinstance(v,tuple) else v, k) for k,v in g.items()])[:6])
    g4P = (0.96739119188673, 3.27310219934594, 0.0549989)
    g1P = (0.96739676975432, 3.27324305194549, 0.0549989)
    g7P = (0.96739031091242, 3.27307995389766, 0.56390239081147, 0.0549989)
    m, bx = check(g7P[0], g7P[1], g7P[2], g7P[3], *g4P, HP=g1P)
    print("g7_P from g4_P (LOW) g1_P (HIGH): min reserve", m, "b_x", bx)
