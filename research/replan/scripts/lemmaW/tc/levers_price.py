# hypothetical analytic levers priced exactly on the PR 86 role split (46/38) and on the lowered-floor split (73/38); wide ell box (pricing only)
import json
from fractions import Fraction as Fr
import pr86, best, levers_pr86 as LV
from lowfloor_greedy import face, base
six = ['old','C','Ccap','C-7','P','Pcap']
WIDE = (Fr(87,100), Fr(806,1000), Fr(467,1000), Fr(18,100))
def th(c):
    r = best.theta_best(c, unit=10**9, anchor=873960000, lo=873500000, step=1000); return None if r is None else r[0]/1e9
for label, kc, kp in (('PR86 chain role split 46/38', 46, 38), ('lowered floor split 73/38', 73, 38)):
    fc, fp = face(kc), face(kp)
    cfg = base.copy(BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1], windows='lemmaW', branches=six, bounds=WIDE)
    LV.set_lev(); t0 = th(cfg)
    print('== %s: base %.9f (gap to bar %.3e)' % (label, t0, t0-0.8739358))
    for name, lev in (('dE=-1e-5', dict(dE=Fr(-1,100000))), ('dE=-1e-4', dict(dE=Fr(-1,10000))), ('dR=1e-4 (count R lowered)', dict(dR=Fr(1,10000))), ('dC=+1e-3 (capacity)', dict(dC=Fr(1,1000))),
                      ('CI=1.995', dict(CI=Fr(1995,1000))), ('CI=1.99', dict(CI=Fr(199,100))), ('CI=1.9', dict(CI=Fr(19,10))),
                      ('KL=0.83', dict(KL=Fr(83,100))), ('KL=0.82', dict(KL=Fr(82,100))), ('KL=0.80', dict(KL=Fr(8,10))),
                      ('eta4=5e-4', dict(eta4=Fr(5,10000))), ('Cfull (delta p C instead of delta p C/2)', dict(Cfull=1))):
        LV.set_lev(**lev); t = th(cfg)
        print('   %-42s theta*=%.9f shift %+.3e gap to bar %+.3e' % (name, t, t-t0, t-0.8739358), flush=True)
    LV.set_lev()
