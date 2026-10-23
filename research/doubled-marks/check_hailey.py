import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json, numpy as np
sys.path.insert(0, HERE)
from replay import feasible, SCHED, K_FB, gain_half
from ss_fb import gates_at, minres
G=json.load(open(os.path.join(HERE, 'feedback_graph.json')))
H={r['name']:r for r in G}
fails=[]; worst=[]
for r in G[1:]:
    lp=H[r['low']]; par=(lp['B'],lp['L'],lp['cap'])
    HP=None
    if r['high']:
        hp=H[r['high']]; HP=(hp['B'],hp['L'],hp['cap'])
    bx=(par[0]-r['B'])/(par[1]-r['L'])
    m=1e9; arg=None
    for b in (bx, r['cap']):
        g=gates_at(b, r['B'], r['L'], r['q'], *par, HP, sched=SCHED[r['bud']], K=K_FB, gain_fn=gain_half(1,HP), nnu=801)
        mm=minres(g)
        if mm[0]<m: m,arg=mm[0],(mm[1],b)
    worst.append((m,r['name'],arg))
    if m<=0: fails.append((r['name'],m,arg))
print("nodes:",len(G)-1,"fails:",len(fails))
for f in fails[:10]: print(f)
worst.sort()
print("smallest reserves:",worst[:5])
