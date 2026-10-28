import numpy as np
from fractions import Fraction as F

def gates(B0,L0,c0,B,L,c,A,D, n=2001):
    s0 = (B0-B)/(L0-L)
    vmax = c - s0
    v = np.linspace(0, vmax, n)
    w = s0 + v
    u = A*v/(1+D*v)
    E = (L0-L)*(1+D*v)+(6*B0-L0)*A
    q = 0.999*L0*A/E
    rho = lambda nu: 1-10*nu/(15-6*nu)
    omr = 10*q/(15-6*q)  # 1-rho(q)
    G = {}
    G['width_pos (c-s0)'] = np.array([vmax])
    G['q_lower q-1/2'] = q-0.5
    G['q_upper 3/4-q'] = 0.75-q
    G['q_floor q-13/20'] = q-0.65
    G['H_lower 1-6u-9/10'] = 1-6*u-0.9
    G['retained_cap c0(1-6u)-(w-u)'] = c0*(1-6*u)-(w-u)
    G['retained_width w-u'] = w-u
    G['low_per_width (1/1000)L0 A/(1+Dv)'] = 0.001*L0*A/(1+D*v)
    highJ = omr - q*B + q*(L-1)*w - (6*omr - q - 1)*u
    G['high_at_q J(w,q)'] = highJ
    G['high_deriv 25/24 H-(B-(L-1)w-u)'] = 25/24*(1-6*u) - (B-(L-1)*w-u)
    G['principal 1-B+(L-2)w-4.5u'] = 1-B+(L-2)*w-4.5*u
    G['second_ref'] = 1/20+1.5*(1-B)+(1.5*L-2.5)*w-4.5*u
    G['second_diag 1-B+(L-1)w-4u'] = 1-B+(L-1)*w-4*u
    G['ref_upper 1/3-2w-3u'] = 1/3-2*w-3*u
    G['sel_deriv A/(1+Dv)^2'] = A/(1+D*v)**2
    # derived: overshoot q(6B0-L0) <= L0
    G['overshoot L0-q(6B0-L0)'] = L0-q*(6*B0-L0)
    return s0, v, q, u, G

def report(name, args):
    s0, v, q, u, G = gates(*args)
    print("==", name, "args", args, " s0=%.5f vmax=%.5f" % (s0, args[5]-s0))
    print("   q range [%.4f, %.4f]; u range [%.4f, %.4f]" % (q.min(), q.max(), u.min(), u.max()))
    for k, arr in G.items():
        i = int(np.argmin(arr))
        print("   %-40s min=%+.6f at v=%.4f" % (k, arr.min(), v[i] if len(arr)>1 else 0))

if __name__ == '__main__':
    report("dsFirst", (0.9999,2.58,0.12,0.9959,2.5,0.1,1.2,140))
    report("dsSecond", (0.9959,2.5,0.1,0.9934,2.45,0.1,0.7,70))
