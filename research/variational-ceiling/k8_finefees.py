"""Our 59-node K = 8 chain (the Lean branch's pivots and cap rule) rebuilt with PR #71's fine fee tuple.
usage: python3 k8_finefees.py e,r,f OUT.json"""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import cchain_k as CK
CK.SCHED = tuple(float(x) for x in sys.argv[1].split(','))
capf = lambda s: min(0.0549989, round(s + 0.016, 7))
piv = [round(0.0135 + 0.0005*i, 4) for i in range(58)] + [0.04232]
nodes = CK.build(piv, capf, 8)
json.dump(nodes, open(sys.argv[2], 'w'), indent=1)
print("nodes:", len(nodes))
