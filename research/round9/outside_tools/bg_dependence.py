#!/usr/bin/env python3
"""
What does the normalized block frame bound F (Lemma BG) depend on?

Smooth part (largest prime factor pi has N(pi) <= K), blocks B_pi.  Replace the cofactor data
e_pi(m) (the column vector divided by its block phase) by:
  true      : g~(m) conj((m/pi)_3) A(pi m)            (the actual P1 vector)
  noslot    : g~(m) conj((m/pi)_3)                    (A = 1)
  gtm only  : g~(m)                                   (no cubic coupling to the block prime)
  random    : independent random phases
  aligned   : (m/k0)_2  for one fixed row k0          (cofactor aligned with a quadratic character)
  half-al.  : (m/k0)_2 on half the blocks, random on the rest
and report F = lambda_max(sum_pi wt_pi wt_pi^*) against (1 + sqrt(m/K'))^2, and the max over
block phases of the column branch / diag.
usage: python3 bg_dependence.py K N Lslot
"""
import sys, math, numpy as np
from block_gram import build, W3
from zw import cubic_sym_elem

K, N, Ls = map(int, sys.argv[1:4])
rng = np.random.default_rng(5)
d = build(K, N, Ls)
Phi, gt, A, big, cols, ar, pel, gtab = d['Phi'], d['gt'], d['A'], d['big'], d['cols'], d['ar'], d['pel'], d['gtab']
Kp, Np = Phi.shape
bn = np.array([b[0] for b in big])
sm = np.nonzero(bn <= K)[0]
blocks = {}
for j in sm:
    blocks.setdefault(big[j], []).append(j)
keys = list(blocks)
m = len(keys)

# cofactor data: for n = pi * mm, compute g~(mm) and conj((mm/pi)_3) directly
def cof_parts(j, key):
    c = cols[j]
    ks = list(zip(c['ps'], c['rs']))
    rest = [k for k in ks if k != key]
    gm = 1 + 0j
    for k in rest:
        gm *= gtab.prime[k][2]
    for i in range(len(rest)):
        for l in range(i + 1, len(rest)):
            ei = pel[rest[i]]
            gm *= np.conj(cubic_sym_elem(ar, ei['a'], ei['b'], rest[l][0], rest[l][1]))
    # coupling conj((m/pi)_3) = prod over primes q | m of conj((q/pi)_3)
    cpl = 1 + 0j
    for k in rest:
        eq = pel[k]
        cpl *= np.conj(cubic_sym_elem(ar, eq['a'], eq['b'], key[0], key[1]))
    return gm, cpl

GM = np.zeros(Np, complex); CPL = np.zeros(Np, complex)
for key, js in blocks.items():
    for j in js:
        GM[j], CPL[j] = cof_parts(j, key)
# sanity: g~(n) = g~(pi) * GM * CPL  (twisted multiplicativity, either orientation of the coupling)
err = []
for key, js in blocks.items():
    gp = gtab.prime[key][2]
    for j in js[:3]:
        err.append(abs(gt[j] - gp * GM[j] * CPL[j]))
print(f"twisted-multiplicativity check on the smooth blocks: max err {max(err):.2e}")

k0 = Kp // 3
variants = {
    'true': GM * CPL * A,
    'noslot': GM * CPL,
    'gtm only': GM,
    'random': np.exp(2j * np.pi * rng.random(Np)),
    'aligned': Phi[k0].astype(complex),
}
half = np.exp(2j * np.pi * rng.random(Np))
for i, (key, js) in enumerate(blocks.items()):
    if i % 2 == 0:
        half[js] = Phi[k0, js]
variants['half-aligned'] = half

def stats(e, name):
    Wm = np.zeros((Kp, m), complex)
    for i, key in enumerate(keys):
        js = blocks[key]
        Wm[:, i] = Phi[:, js] @ e[js]
    nrm = np.linalg.norm(Wm, axis=0)
    ok = nrm > 1e-9
    F = np.linalg.svd(Wm[:, ok] / nrm[ok], compute_uv=False)[0] ** 2
    blk = np.sum(nrm ** 2)
    cp = np.zeros(Np, complex); cp[sm] = e[sm]
    diag = np.sum((Phi ** 2) @ np.abs(cp) ** 2)
    G = Wm.conj().T @ Wm
    best = 0.0
    for x in [np.linalg.svd(Wm, full_matrices=False)[2][0].conj()] + [np.exp(2j*np.pi*rng.random(m)) for _ in range(3)]:
        x = np.exp(1j * np.angle(x))
        for _ in range(60):
            x = np.exp(1j * np.angle(G @ x))
        best = max(best, np.real(np.vdot(x, G @ x)))
    ls = (Kp + len(sm)) * np.sum(np.abs(cp) ** 2) / diag
    print(f"  {name:13s} F={F:7.2f}  F/(1+sqrt(m/K'))^2={F/(1+math.sqrt(m/Kp))**2:6.2f}  blk/diag={blk/diag:5.2f}  "
          f"max_phases CB/diag={best/diag:7.2f}  LS/diag={ls:5.1f}", flush=True)

print(f"K'={Kp} N'={Np} smooth cols {len(sm)} blocks m={m}  (1+sqrt(m/K'))^2={(1+math.sqrt(m/Kp))**2:.2f}")
for name, e in variants.items():
    stats(e, name)
