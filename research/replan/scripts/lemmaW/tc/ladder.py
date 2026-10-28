# attribution ladder: from OUR Collet-window toolchain (original constants) to the PR 86 return, all on PR 86's faces; floor-coupled h
import json
from fractions import Fraction as Fr
import pr86, best
chain = json.load(open('chain86.json'))
B46, L46 = Fr(chain[46]['B']), Fr(chain[46]['L'])
six = ['old','C','Ccap','C-7','P','Pcap']
cfg0 = pr86.Cfg(BC=B46, LC=L46, BP=B46, LP=L46, edges='ours', dMinusLower=Fr(1,2), branches=six, reserve=Fr(1,10**9),
                mMinus=Fr(2,5), sMinus=Fr(17,500), mPlus=Fr(11,25), wC=Fr(29,500), wP=Fr(43,1000))
def th(cfg):
    r = best.theta_best(cfg, unit=10**9, anchor=874100000, lo=873900000, step=2000, maxstep=200); return None if r is None else r[0]/1e9
steps = [('L0 our Collet constants (m_-=2/5, s_-=17/500, window caps 29/500 & 43/1000), six branches, our 6 edges', cfg0)]
c1 = cfg0.copy(sMinus=Fr(3,100)); steps.append(('L1 + s_- = 3/100 (natural join 0.4235 -> 0.4325)', c1))
c2 = c1.copy(mMinus=Fr(377,1000)); steps.append(('L2 + m_- = 377/1000', c2))
c3 = c2.copy(wC=None, wP=None); steps.append(('L3 + window caps = face caps (0.09999 / 31/500)', c3))
c4 = c3.copy(edges='pr86', dMinusLower=Fr(3,4), branches=['old','C','Pcap'], reserve=Fr(1,10**8)); steps.append(('L4 + PR 86 edge set (dm=19/25), branches old/C/capP, reserve 1e-8  [= PR 86 replica]', c4))
c5 = c3.copy(windows='lemmaW'); steps.append(('L3 with Lemma W windows instead (m_-=0, crossover join)', c5))
c6 = cfg0.copy(windows='lemmaW'); steps.append(('L0 with Lemma W windows (window caps = 29/500 & 43/1000)', c6))
for lab, c in steps:
    print('%-100s theta* = %s' % (lab, th(c)), flush=True)
