"""Does the theta excess survive when reciprocity is broken?

RCHAR: each row prime's sextic character (x/pi)_6 is replaced by its conjugate at random (e_pi in {1, 5}).  Every row
is still a character of the source mod z, but (x/z)_6 ~ (z/x)_6 fails.  In the Poisson dual, the pair factor
chi_z(z') conj chi_z'(z) is then a varying sixth root of unity instead of the reciprocity sign, so the dual atoms no
longer add coherently.  The script compares r(c) = |E^T c|^2/(S |c|^2) for the theta vectors conj G(z) chi_z(u)
profile of the sextic matrix and of RCHAR (built from RCHAR's own Gauss sums: g(conj chi) = chi(-1) conj g(chi) per
prime, with the CRT cross factors of the modified characters), against random phases.

usage: python3 -I theta_reciprocity.py B L [seed]
"""
import os, sys
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 29
F = tc.build(B, L)
E, R, S, rows, SA, SB, pc, ID, Grow, unit_tw, gen = F.E, F.R, F.S, F.rows, F.SA, F.SB, F.pc, F.ID, F.Grow, F.unit_tw, F.generator
uid = np.unique(rows['PID'][rows['PID'] >= 0])
T = pc.symbol_table(ID, uid, SA, SB).astype(np.int16)
LOC = pc.local_index(rows['PID'], uid)
prof = (rows['N'] / B) ** -0.5
rng = np.random.default_rng(seed)
ec = rng.choice([1, 5], size=len(uid))
Tc = np.where(T < 6, (T * ec[:, None]) % 6, T).astype(np.int8)
Mc = pc.chi_chunk(LOC, Tc, 0, R).astype(np.complex128)
# Gauss sums of the conjugated rows: g(conj chi) = chi(-1) conj g(chi) per prime; build per row as a product with
# the CRT cross factors of the modified characters (computed numerically from the modified symbols)
pos = {int(u): j for j, u in enumerate(uid)}
G2 = np.zeros(R, complex)
for zi in range(R):
    ids = [int(i) for i in rows['PID'][zi] if i >= 0]
    g = 1 + 0j
    gens = [gen(i) for i in ids]
    for i, gi in zip(ids, gens):
        e = ec[pos[i]]
        gp = gi['G'] if e == 1 else np.conj(gi['G']) * F.sym(gi['prime'], (-1, 0)) 
        g *= gp
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            ea, eb = ec[pos[ids[a_]]], ec[pos[ids[b_]]]
            s1 = F.sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) ** eb
            s2 = F.sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b'])) ** ea
            g *= s1 * s2
    G2[zi] = g
def r(M, c):
    v = M.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))
rb = [r(Mc, np.exp(2j*np.pi*rng.random(R))*prof) for _ in range(8)]
print('RCHAR random phases %.3f +- %.3f' % (np.mean(rb), np.std(rb)))
print('RCHAR conj G2 (its own Gauss sums) per unit twist: %s' % np.round([r(Mc, np.conj(G2)*unit_tw[:, k]*prof) for k in range(6)], 3))
print('RCHAR G2: %s' % np.round([r(Mc, G2*unit_tw[:, k]*prof) for k in range(6)], 3))
print('sextic conj G: %s' % np.round([r(E, np.conj(Grow)*unit_tw[:, k]*prof) for k in range(6)], 3))
