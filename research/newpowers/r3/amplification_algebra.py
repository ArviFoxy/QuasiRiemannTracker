"""Exponent arithmetic for amplifiers (copies with exchange rate e, i.e. multiplicity (H/U)^{1/e}) and moment powers.  Own derivations;
every Lean quantity used is cited in R3_return.md.  Units: exponents of U (row norm), except where Z is said.
Run:  python3 amplification_algebra.py   -> logs/amplification_algebra.log"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pm import *
import numpy as np

m = scenario('A'); bnd = m.binding()
d_, R_, h_ = float(bnd['delta']), float(bnd['R']), bnd['h']
ell = 11/3 - 4*bnd['theta']
m0 = 2*ell/h_                       # plain length of the numerator packet, = 1 - y/d at d = h
C = bnd['C']; q = d_*0.5            # q = delta*p at p = 1/2
Ct = C/h_                           # capacity in U units
print('binding point (scenario A): delta=%.5f R=%.6f h=%.6f ell=%.6f m0=2ell/h=%.5f C=%.5f C/h=%.5f q=delta p=%.5f' % (d_, R_, h_, ell, m0, C, Ct, q))

# ------------------------------------------------------------------ 1. when can copies pay?  (plateau vs slope)
print('\n== 1. amplification by exact copies with exchange rate e: multiplicity (H/U)^(1/e)')
print('   bound for rows<=U from a known bound B(H) at a larger range H:  B_amp(U) = min_{H>=U} B(H) / (H/U)^(1/e)')
print('   pays iff B is flatter than H^(1/e) somewhere.  Slopes d log B / d log H of the bounds that occur in the return:')
for name, slope in (('Lemma 17.1 / 18.1 diagonal (marked inverse, face)', 1.0), ('Moebius plateau H<D (long line)', 0.0),
                    ('quadratic large sieve N>K plateau (column branch)', 0.0), ('sextic large sieve (KD)^(2/3) range', 2/3)):
    verdict = 'never (slope >= 1/e for every e>=1)' if slope >= 1 else ('exchange rate e > %.2f' % (1 / slope) if slope > 0 else 'any exchange rate (flat)')
    print('   %-55s slope %.2f  -> amplification pays for: %s' % (name, slope, verdict))

# ------------------------------------------------------------------ 2. amplified marked inverse (I line) beyond the diagonal
print('\n== 2. amplified marked inverse moment (slots kept): exponent(r,z) = 1 + (e-1)/e*(r + c_I z - 1)_+ - delta r - 2 q z')
for e in (6, 4, 3, 2):
    slope_z = (e-1)/e*2 - 2*q            # d/dz beyond the diagonal, c_I = 2
    print('   exchange rate %d: d exponent / d z = %+.4f  (needs < 0 to pay)  [2q = %.4f]' % (e, slope_z, 2*q))
print('   break-even exchange rate for the I line: (e-1)/e*2 = 2q  ->  e = %.4f  (i.e. a multiplier family denser than X^(1/%.3f))' % (1/(1-q), 1/(1-q)))
print('   with loss rate lam per unit excess instead (P1-type partial saving): pays iff lam < delta p = %.4f' % q)

# ------------------------------------------------------------------ 3. long line with supply-limited fourth-power width
print('\n== 3. long line: L(r) = (1+5r)/6 - min(w/3,(r-1)/12) - delta r   (w = fourth-power width absorbed, units of log U)')
t = 1.1427
print('   at t* = %.4f: pure sixth powers L = %.6f ; pure fourth powers (w=(t-1)/4=%.4f) would give shift %.5f' % (t, (1+5*t)/6 - d_*t, (t-1)/4, (t-1)/12))
for s, wneed in (('A', 8.6547e-4), ('B', 1.5588e-3)):
    mm = scenario(s)
    print('   scenario %s: needed w = %.3e (U units) = %.3e (Z units) = %.2f%% of the slot supply ell/d=%.4f, = %.2f%% of a pure fourth-power family' %
          (s, wneed, wneed*h_, 100*wneed/(ell/h_), ell/h_, 100*wneed/((t-1)/4)))
    # equivalent k_L
    mm.wL = wneed; tt = mm.theta_star()
    print('      check: PM theta* with wL=%.4e : %.9f (bar %.7f)' % (wneed, tt, BAR))

# ------------------------------------------------------------------ 4. Hoelder orders: large-values lines
print('\n== 4. Hoelder orders as large-values lines.  Sum_B |S| <= max_v [ v + min(R, mu_k - k v) ] (v = exponent of |S|)')
v4 = (1 - R_ - 2*q*Ct)/4
E4 = R_ + v4
print('   k=4 with slot weight 2 (the Lean proof): corner v4=(1-R-2qC/d)/4=%.5f, value R+v4=%.5f  (cap |S|<=U^(delta m0/2)=%.5f)' % (v4, E4, d_*m0/2))
for k in (2, 6, 8):
    # Hoelder-k with NO slot credit (conservative) vs k=4 WITH credit; mu_k* = threshold exponent of the k-th moment
    muk = R_ + k*v4
    print('   k=%d: line mu_k - k v crosses R exactly at the 4th-moment corner iff mu_k = R + k v4 = %.4f   (diagonal mu=1; excess lam*=%.4f)' % (k, muk, muk - 1))
# the actual availability of the 2k-th moment of the plain packet (length m0, rows U)
print('   available 6th moment of the packet S (length m0=%.4f): large sieve on S^3 (length D=3m0=%.4f):' % (m0, 3*m0))
D3 = 3*m0
ideal = max(1, D3)
sextic = max(1, D3, (2/3)*(1+D3))
print('       ideal (K+D) sieve:  mu6 = %.4f ;  sextic sieve Lemma 9.1 (K+D+(KD)^(2/3)):  mu6 = %.4f' % (ideal, sextic))
def amp_best(Dlen, e, sieve):
    best = 1e9
    for hp in np.linspace(1, 1 + 6*(Dlen), 4001):
        f = max(hp, Dlen) if sieve == 'ideal' else max(hp, Dlen, (2/3)*(hp + Dlen))
        best = min(best, f - (hp - 1)/e)
    return best
for e in (6, 4, 3, 2.285, 2):
    print('       amplified with exchange rate %-5s: ideal sieve mu6 = %.4f ; sextic sieve mu6 = %.4f   (need <= %.4f)' % (e, amp_best(D3, e, 'ideal'), amp_best(D3, e, 'sextic'), R_ + 6*v4))
# critical exchange rate (ideal sieve): D3(1-1/e)+1/e = R+6 v4
mu_star = R_ + 6*v4
e_crit = (D3 - 1)/(D3 - mu_star)
print('   critical exchange rate (ideal large sieve) for Hoelder-6 to beat Hoelder-4: e <= %.3f' % e_crit)
print('   k=8: need mu8 <= %.4f; ideal sieve on S^4 (length %.4f) amplified e=6: %.4f' % (R_ + 8*v4, 4*m0, amp_best(4*m0, 6, 'ideal')))
gain6 = lambda mu: h_*((R_ - 1 + 2*(mu-1))/12)   # E(Hoelder-6, no slots handled separately) - E(Hoelder-4) at equal capacity
print('   if the 6th moment were diagonal (mu6=1) with the same slot credit, E would drop by %.5f (= %.1fx the 4.9e-5 needed)' % (-gain6(1.0), -gain6(1.0)/4.9e-5))

# Hoelder-2 for comparison (face m0 + z <= 1/2 from the generic sextic sieve, full credit q*C2; LOG.md / B1, not Lean-literal)
C2t = max(0.0, 0.5 - m0)                       # capacity in U units
E2 = (R_ + 1)/2 - q*C2t
E4_ = R_ + v4
print('   Hoelder-2 (face m0+z<=1/2, credit q C2, C2/d=%.4f): exponent %.5f  vs Hoelder-4 %.5f   -> worse by %.5f (x d = %.4f in E)' % (C2t, E2, E4_, E2 - E4_, h_*(E2 - E4_)))
for k, mu in ((6, 1.0), (6, 1.154), (6, 1.2279), (6, 1.5156)):
    Ek = (1 - 1/k)*R_ + mu/k
    print('   Hoelder-%d with mu_%d=%.4f (no slot credit): exponent %.5f ; minus Hoelder-4: %+.5f (x d = %+.4f in E)' % (k, k, mu, Ek, Ek - E4_, h_*(Ek - E4_)))

# ------------------------------------------------------------------ 5. pointwise cap on the packet
print('\n== 5. pointwise cap on |S| (zero-free region): kappa_S = delta*m0/2 = %.5f ; Hoelder-4 extremal level v4 = %.5f' % (d_*m0/2, v4))
print('   a cap below v4 binds: E falls by d per unit of cap; the cap must be lowered by %.2f%% to tie and by %.2f%% to gain 4.9e-5' %
      (100*(1 - v4/(d_*m0/2)), 100*(1 - (v4 - 4.9e-5/h_)/(d_*m0/2))))

# ------------------------------------------------------------------ 6. doubled slots: cost discount <-> epsilon
print('\n== 6. doubled slots: a face with weight |Q|^4 at cost (2 - eta) Lam per unit width gives credit (1/2+eps) q C, eps = eta/(2(2-eta))')
for s, eps in (('A', 0.0045901), ('B', 0.0083357)):
    eta = 4*eps/(1 + 2*eps)
    print('   scenario %s: eps=%.5f  <->  eta = %.5f  (second copy %.2f%% cheaper than the first; cost %.4f Lam)' % (s, eps, eta, 100*eta/2, 2-eta))
print('   K copies (weight |Q|^{2K}) with face cost c_K Lam per unit width: eps_K = 1/(2 c_K / K)... credit per cost scales by K/c_K')
for K, cK in ((2, 1.98), (2, 1.9), (3, 2.95), (3, 2.9)):
    print('      K=%d c_K=%.2f -> credit factor K/c_K = %.4f -> eps = %.5f' % (K, cK, K/cK, 0.5*K/cK - 0.5))

# ------------------------------------------------------------------ 7. column branch: twist-to-dilation conversion (own derivation)
print('\n== 7. column branch (P1 regime): split n = n1 n2, turn the n2-twist chi_{n2}(n1)^4 into the dilation k -> k n2^4 (cf. whole_column),')
print('      Cauchy in n2, then the sextic sieve (Lemma 9.1: K + D + (KD)^(2/3)) on n1 over the rows W = K N2^4.   exponents are log_K')
def lk(x): return x
def new_exp(a, dprime):           # N2 = K^a, N = K^(1+dprime), N1 = N/N2
    N = 1 + dprime; N1 = N - a; W = 1 + 4*a
    sieve = max(W, N1, (2/3)*(W + N1))
    return a + sieve + N1          # ||c||^2 = N2 (Cauchy), times sieve, times ||beta1||^2 = N1
def old_exp(dprime): return max(1, 1 + dprime) + (1 + dprime)       # (K+N) * ||c||^2 , ||c||^2 = N
for dprime in (1e-4, 1e-2, 0.1, 0.5):
    grid = [(new_exp(a, dprime) - old_exp(dprime), a) for a in np.linspace(0, 1 + dprime, 2001)]
    best = min(grid)
    print('   N=K^(1+%.4g): converted minus original exponent, minimised over N2=K^a: %+.4f (at a=%.3f)   [>0: the conversion loses]' % (dprime, best[0], best[1]))
