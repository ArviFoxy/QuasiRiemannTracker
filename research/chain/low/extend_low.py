"""What-if (not yet a Lean structure): continue the exact floor-1/2 chain below q = 1/2.
Gate library = the marked library without `q_lower` (dens > 1/2), floor QF; the marked precondition `1/2 <= floor`
of gen_hybrid is bypassed (Collet's count holds for a > 51/100; the Lean side needs the fork of the a >= 3/4 wrappers).
usage: python3 extend_low.py QF NSTEPS OUT.json"""
import sys, os, json, math
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'density'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'newpowers', 'ta'))
from dataclasses import replace
import gen_hybrid as GH
import design_chain as DC
import chain2 as C2

QF, N, OUT = Fr(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
GH.Params.check_marked_preconditions = lambda self: None          # what-if only
lib = GH.marked_lib(GH.PR83_LIB)
lib = replace(lib, gates=tuple(g for g in lib.gates if g.key != 'q_lower'))
steps = json.load(open(os.path.join(HERE, '..', 'steps_f050_dL200.json')))
last = steps[-1]
B0, L0, c0 = Fr(last['B']), Fr(last['L']), Fr(last['c'])
cfg = C2.Cfg(gain=1.0, floor=float(QF), qlow=float(QF), dfac=0.999, boot=False, dL=0.005, nu_mode='q')
guess = (math.log(float(Fr(last['A']))), math.log(float(Fr(last['D']))))
s_guess = last['s0']
out = []
for i in range(N):
    r = C2.best_step(cfg, float(B0), float(L0), float(c0), guess, s_guess)
    if r is None or r[0] >= 0.9:
        print('float wall'); break
    s0f, Af, Df, _ = r
    A, D = Fr(round(Af * 10 ** 6), 10 ** 6), Fr(round(Df * 500), 500)
    B = DC.exact_step(B0, L0, c0, Fr(1, 200), A, D, QF, 10 ** 8, lib, s0f)
    if B is None:
        print('exact wall'); break
    L, c = L0 - Fr(1, 200), Fr(1, 10)
    out.append(dict(B0=str(B0), L0=str(L0), c0=str(c0), B=str(B), L=str(L), c=str(c), A=str(A), D=str(D),
                    floor=str(QF), s0=float((B0 - B) * 200)))
    print('[%d] L=%.4f B=%.9f s0=%.6f' % (130 + i, float(L), float(B), float((B0 - B) * 200)), flush=True)
    json.dump(out, open(OUT, 'w'), indent=1)
    B0, L0, c0 = B, L, c
    guess, s_guess = (math.log(Af), math.log(Df)), s0f
