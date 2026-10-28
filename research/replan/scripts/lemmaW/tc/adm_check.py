# Exact check of the 16 admission windows (240 guard certificates) of PR 86 against our admission polynomials (Collet structure, PR 86 constants)
import re, glob
from fractions import Fraction as Fr
import pr86, cert_return as CR, gen_return_lean as GR
U86 = '$SCRATCH/upstream/submissions/2026-10-28-density-split-fine-chain/src/Submissions/density_split_fine_chain/Return/Rows'
cfg = pr86.Cfg()
pr86.apply_globals(cfg)
G = pr86.geometry(cfg)
cands = {nm: (br, meta) for nm, br, meta in pr86.candidate_list(cfg, G)}
brmap = {'C': 'C', 'capP': 'Pcap'}
pat = re.compile(r'theorem admission(\d+)_(\d+)_identity \(δ p : ℝ\) : admissionGuard \.(\w+) δ p (\d+) =\s*\n\s*Record12518109\.Bernstein\.bsum (\d+) (\d+) \(([^:]+):ℝ\) \w+ \(([^:]+):ℝ\) \(([^:]+):ℝ\) \(([^:]+):ℝ\) \(([^:]+):ℝ\)')
tot = ok = 0; bad = []
for f in sorted(glob.glob(U86 + '/Admission*.lean')):
    txt = open(f).read()
    for m in pat.finditer(txt):
        w, j, br, jj, n1, n2, mv, d0, d1, p0, p1 = m.groups()
        mv, d0, d1, p0, p1 = (Fr(x) for x in (mv, d0, d1, p0, p1))
        b, meta = cands[brmap[br]]
        guards = GR.guards(b, meta)
        mine = CR.bernstein_min(guards[int(j)], ((d0, d1), (p0, Fr(1, 2))))
        tot += 1
        if mine == mv: ok += 1
        else: bad.append((w, j, br, float(mine), float(mv)))
print('admission guard certificates compared: %d, exactly equal: %d' % (tot, ok))
print('mismatches:', bad[:10])
