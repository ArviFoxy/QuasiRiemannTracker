"""theta* for a chain file, respecting the HIGH-parent domain of cert_chain_k (22/23 <= B_H): the chain is
cut after the first node whose B < 22/23 (that node may still serve as the count/physical face, as node 58 does).
args: chain.json [relax22] [relaxLP] [h list]"""
import sys, os, json
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import cert_return as CR
path = sys.argv[1]
relax22 = 'relax22' in sys.argv; relaxLP = 'relaxLP' in sys.argv
if relaxLP: CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
nodes = json.load(open(path))
if not relax22:
    cut = []
    for n in nodes:
        cut.append(n)
        if Fr(n['B']) < Fr(22, 23): break
    nodes = cut
def face(n): return (Fr(n['B']), Fr(n['L']), Fr(n['cap']))
def ok(theta, h, C, P):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(theta, h, C, P, verbose=False, sP=Fr(9,200), sC=Fr(13,250), mode='global')
        return not bad
    except ValueError:
        return False
def best(C, P, h=Fr(401,500), lo=8744000, hi=8747758):
    if not ok(Fr(hi,10**7), h, C, P): return None
    while hi-lo > 1:
        mid = (lo+hi)//2
        if ok(Fr(mid,10**7), h, C, P): hi = mid
        else: lo = mid
    return hi
cands = [n for n in nodes if float(Fr(n['cap'])) >= 0.0521]
nC = max(cands, key=lambda n: float(Fr(n['B'])) - float(Fr(n['L']))*0.045)
nPs = [n for n in nodes if float(Fr(n['cap'])) >= 0.045 and (relaxLP or float(Fr(n['L'])) > 3)]
zph = lambda n: (float(Fr(n['B'])) - 0.83666)/float(Fr(n['L']))
nP = max(nPs, key=zph)
print(f"{path} (relax22={relax22}, relaxLP={relaxLP}, {len(nodes)} nodes kept, last pivot {nodes[-1]['pivot']}): "
      f"C pivot {nC['pivot']} (B={float(Fr(nC['B'])):.6f}, h@.045={float(Fr(nC['B']))-float(Fr(nC['L']))*0.045:.6f}), "
      f"P pivot {nP['pivot']} (L={float(Fr(nP['L'])):.4f}, z_phys={zph(nP):.6f})", flush=True)
hs = [Fr(x) for x in sys.argv if '/' in x and not x.endswith('.json')] or [Fr(401,500)]
for hh in hs:
    print('  h =', float(hh), 'theta* =', best(face(nC), face(nP), h=hh), flush=True)
