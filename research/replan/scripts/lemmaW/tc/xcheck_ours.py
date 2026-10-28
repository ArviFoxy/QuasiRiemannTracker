# Cross-check of pr86.py against the earlier Lemma W report (research/return-transfer/REPORT.md, exact): our flat faces_k92.json
import json, time
from fractions import Fraction as Fr
import pr86
F = json.load(open('/home/user/QuasiRiemannTracker/research/mixed-step/faces_k92.json'))
FR = json.load(open('/home/user/QuasiRiemannTracker/research/mixed-step/faces_k92_ramp.json'))
def cfg_from(F, **kw):
    c = pr86.Cfg(BC=Fr(F['C']['B']), LC=Fr(F['C']['L']), capC=Fr(F['C']['cap']), BP=Fr(F['P']['B']), LP=Fr(F['P']['L']), capP=Fr(F['P']['cap']),
                 sP=Fr(29,500), dm=None, edges='ours', dMinusLower=Fr(1,2), reserve=Fr(1,10**9),
                 branches=['old','C','Ccap','C-7','P','Pcap'], bounds=(Fr(874,1000),Fr(807,1000),Fr(467,1000),Fr(171,1000)),
                 mMinus=Fr(2,5), sMinus=Fr(17,500), mPlus=Fr(11,25), h=Fr(2011,2500))
    c.__dict__.update(kw); return c
def run(label, cfg, anchor=8742800, lo=8700000):
    t0=time.time(); t = pr86.theta_star(cfg, anchor=anchor, lo=lo)
    print('%-92s theta* = %s %s [%.1fs]' % (label, None if t is None else '%.7f' % (t/1e7), '' if t is None else pr86.report(cfg,t), time.time()-t0), flush=True)
    return t
# Collet's windows exactly as in the report: window caps sC = 29/500 (C) and 43/1000 (P), m_- = 2/5, s_- = 17/500
run('faces_k92 (caps 3/40): Collet windows [report: 0.8742701]', cfg_from(F, wC=Fr(29,500), wP=Fr(43,1000)))
run('faces_k92: Lemma W, window caps = cap-1e-4 [report: 0.8741364 at h=2011/2500]', cfg_from(F, windows='lemmaW', wC=Fr(749,10000), wP=Fr(749,10000)), anchor=8741600)
run('faces_k92: Lemma W, window caps = face caps', cfg_from(F, windows='lemmaW'), anchor=8741600)
# attribution of the PR 83/86 retune of constants (mMinus=.377,sMinus=.03, window caps = face caps) on these flat faces
run('faces_k92: Collet structure, PR86 constants mMinus=.377 sMinus=.03, window caps = face caps', cfg_from(F, mMinus=Fr(377,1000), sMinus=Fr(3,100)), anchor=8742800)
run('faces_k92_ramp (caps .085/.0805): Collet windows (2/5, 17/500, caps 29/500, 43/1000)', cfg_from(FR, wC=Fr(29,500), wP=Fr(43,1000), h=Fr(403,500)), anchor=8742800)
run('faces_k92_ramp: Collet structure, PR86 constants, window caps = face caps', cfg_from(FR, mMinus=Fr(377,1000), sMinus=Fr(3,100), h=Fr(403,500)), anchor=8742800)
run('faces_k92_ramp: Lemma W (face caps) [report design (b): 0.8740728]', cfg_from(FR, windows='lemmaW', h=Fr(403,500)), anchor=8741200)
