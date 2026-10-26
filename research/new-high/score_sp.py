"""Re-optimize the return's physical numerator cap sP for a flow (P at the envelope crossing face nearest
s*, C at 0.06), since a better face raises the second branch of C_N(d+) ~ (B_P - (2 - 2y/h))/L_P.
Environment QRH_KL/QRH_CI/QRH_TMAX as in ret_new.py (default: unmodified return).
usage: python3 score_sp.py FLOW.json sP1,sP2,... [Pface_s]"""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ret_new as RN
import score as SC
import score2 as S2
from fractions import Fraction as Fr


def theta(args):
    BP, LP, BC, LC, sP = args
    RS = RN.RS
    P = dict(RS.DEF); P.update(SC.DESIGN)
    P.update(BP=f'{BP:.8f}', LP=f'{LP:.8f}', BC=f'{BC:.8f}', LC=f'{LC:.8f}', sP=str(sP))
    P = {k: Fr(v) for k, v in P.items()}
    return RS.ts(P, lo=8650000)


if __name__ == '__main__':
    path = sys.argv[1]; sps = sys.argv[2].split(',')
    rows = json.load(open(path))
    ss = S2.crossing(rows)
    grid = sorted({round(x['s'], 6) for x in rows})
    if len(sys.argv) > 3:
        sp_face = float(sys.argv[3])
    else:
        sp_face = min(grid, key=lambda s: abs(s - ss)) if ss else grid[-1]
    BP, LP = SC.face_at(rows, sp_face); BC, LC = SC.face_at(rows, 0.06)
    with Pool(4) as pool:
        res = pool.map(theta, [(BP, LP, BC, LC, sp) for sp in sps])
    tag = f"kL={RN.KL} cI={RN.CI} TMAX={RN.TMAX}"
    for sp, th in zip(sps, res):
        print(f"[{tag}] {os.path.basename(path)} s*={ss} P@{sp_face} (B-0.843)/L={(BP-0.843)/LP:.5f} sP={sp} theta*={th}", flush=True)
