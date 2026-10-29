"""Vectorised facet values phi_k(p) (= facet/nu) and chain-relevant sampler."""
import json, os
import numpy as np
from fractions import Fraction as Fr
K = 8
def phis_vec(nu, p, B, L, h0, S, Q):
    """all args broadcastable; returns array [..., 6]"""
    w = 5 - 6*nu; base = 10/(15 - 6*nu)
    inv = [(np.ones_like(p), -2*p*K*S), (1/(1-p), -p*Q/(1-p))]
    d2 = 1 - 2*p/L
    pl = [(np.ones_like(p), -2*p*S), (np.ones_like(p), -2*p*h0*Q), (1/d2, -(2*p*B*Q/L)/d2)]
    out = []
    for si, oi in inv:
        for sj, oj in pl:
            slope = 6*nu + w*(si + sj/2); off = w*(oi + oj/2)
            out.append((1 - 2*p)*S + (5*Q - off)/slope - base*Q)
    return np.stack(np.broadcast_arrays(*out), -1)
steps = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'chain', 'steps_f050_dL200.json')))
CH = np.array([[float(Fr(s[k])) for k in ('B0', 'L0', 'A', 'D')] for s in steps])
def y_of(q): return (5 - 6*q)/(25 - 18*q)
def sample(n, rng, dB=1e-3, ds=5e-4, h=0.005, c=0.1, vpow=3):
    i = rng.integers(0, len(CH), n)
    B0 = CH[i, 0] + rng.uniform(-dB, dB, n); L0 = CH[i, 1]
    A = rng.uniform(0.4, 0.7, n); D = np.exp(rng.uniform(np.log(20), np.log(1000), n))
    q0 = np.minimum(0.999*L0*A/(h + (6*B0 - L0)*A), 0.75)
    sig = (B0 - 1 + y_of(q0))/(L0 - 1 + y_of(q0))
    s0 = sig + rng.uniform(0, ds, n)
    v = (c - s0)*rng.uniform(0, 1, n)**vpow
    u = A*v/(1 + D*v); S = s0 + v - u; Q = 1 - 6*u
    qv = np.minimum(0.999*L0*A/(h*(1 + D*v) + (6*B0 - L0)*A), 0.75)
    nu = qv + (0.75 - qv)*rng.uniform(0, 1, n)**2
    ok = (q0 >= 0.5) & (qv >= 0.5)
    return dict(B0=B0[ok], L0=L0[ok], A=A[ok], D=D[ok], s0=s0[ok], v=v[ok], u=u[ok], S=S[ok], Q=Q[ok], nu=nu[ok], qv=qv[ok])
