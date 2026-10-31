"""Task B3, growth law: predict the top outlier of E for B = L = 3e3 ... 3e5 from the coherent kernel of the source Gram.

Mechanism (theta_mech_corner.py):  H = E^* E has the coherent part  H_coh(x,x') = R kappa (N N')^(-1/3) B^(-1/6) Theta(x) conj Theta(x')
conj g~(x) g~(x')  for N N' >~ B   (K(y) = H_coh sqrt(N N')/R ~ kappa y^(1/6), y = N N'/B: the sixth-power multiplicity).  It is
a rank-one spike  sigma^2 u v^*  with  v = Theta conj g~ N^(-1/3)  and

    sigma^2 / R = fit * kappa * B^(-1/6) * sum_{x <= L} N(x)^(-2/3)   (~ 3 kappa rho B^(1/6)),

rho = density of sources.  With the masked-noise BBP formula  s^2/S = v0 (sigma~^2 + R)(sigma~^2 + S)/(sigma~^2 S),
sigma~^2 = sigma^2/v0 (v0 = 0.952 = fraction of nonzero entries), this gives the top eigenvalue and the implied BBP strength
theta = sigma~^2/sqrt(R S).

Inputs read from the logs of this directory (nothing is refitted at large B):
  * kappa = pair-weighted mean of K/y^(1/6) over the kernel bins 6 <= y <= 2000 of theta_mech_corner_B{3000,10000,30000}.log;
  * fit = mean over those three B of (compressed excess of the 12-dim class-signed span, from the same logs) / (kernel prediction
    kappa B^(-1/6) sum N^(-2/3));  it measures how much of the rank-one kernel the 12 class coefficients capture;
  * observed tops: 'sextic E' and the masked-random tops of theta_top_free2_B*.log (and theta_top_free_B*.log for 2e5, 3e5).

usage: python3 -I theta_mech_growth.py
"""
import os, sys, re, glob, math
sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'prime_pool'))
sys.path.insert(0, os.path.join(HERE, '..'))
import ppcore as pc          # noqa: E402

V0N = 0.952


def sum_n23(B):
    ID = pc.Ideals(2 * B + 16)
    SA, SB, SN = pc.primary_elements(B)
    spf = ID.spf
    SNi = SN.astype(np.int64)
    ok = (SNi > 1) & (SNi % 2 == 1)
    for p in range(2, int(math.isqrt(B)) + 1):
        if spf[p] == p:
            ok &= (SNi % (p * p) != 0)
    return float(np.sum(SN[ok].astype(float) ** (-2 / 3))), int(ok.sum())


# ---- kappa and the 12-dim excess from the corner logs
kap_rows = []
exc = {}
for B in (3000, 10000, 30000):
    txt = open(os.path.join(HERE, 'theta_mech_corner_B%d.log' % B)).read()
    ks, ws = [], []
    for m in re.finditer(r'\[\s*([\d.e+]+),\s*([\d.e+]+)\)\s+(\d+)\s+([+-][\d.]+)\s+([\d.]+)\s+([+-][\d.]+)\s+([+-][\d.]+)\s+([+-][\d.]+)\s+y=([\d.]+)', txt):
        y = float(m.group(9))
        if 6 <= y <= 2000:
            ks.append(float(m.group(7))); ws.append(int(m.group(3)))
    kappa_B = float(np.average(ks, weights=ws))
    kap_rows.append(kappa_B)
    m = re.search(r'alpha = 0\.333 \(reference\)\s+dim\s+12\s+top s\^2/R \[([\d.]+)[^\]]*\]\s+\(random phases ([\d.]+)', txt)
    exc[B] = float(m.group(1)) - float(m.group(2))
    print('B = %6d: kernel plateau K/y^(1/6) over 6 <= y <= 2000 = %.3f ; compressed excess of the 12-dim span = %.3f' % (B, kappa_B, exc[B]))
kappa = float(np.mean(kap_rows))
print('kappa = %.3f (mean of %s)' % (kappa, np.round(kap_rows, 3)))
fits = []
for B in (3000, 10000, 30000):
    s23, _ = sum_n23(B)
    fits.append(exc[B] / (kappa * B ** (-1 / 6) * s23))
fit = float(np.mean(fits))
print('fit factor (observed 12-dim excess / rank-one kernel prediction) = %s -> %.3f' % (np.round(fits, 3), fit))

# ---- observed tops
obs = {}
for f in sorted(glob.glob(os.path.join(HERE, 'theta_top_free2_B*.log')) + glob.glob(os.path.join(HERE, 'theta_top_free_B*00000.log'))):
    txt = open(f).read()
    m = re.search(r'B=(\d+) L=(\d+)\s+R=(\d+) rows\s+S=(\d+) sources', txt)
    if not m:
        continue
    B, R, S = int(m.group(1)), int(m.group(3)), int(m.group(4))
    t = re.search(r'sextic E\s*:\s*\[([\d.]+)', txt)
    e = [float(x) for x in re.findall(r'masked random\s*:\s*\[([\d.]+)', txt)]
    if t and e and B >= 3000:
        obs[B] = (R, S, float(t.group(1)), float(np.mean(e)))
print('\nB        R      S    sum N^-2/3   sigma^2/R   theta_pred theta_obs  top_pred  top_obs   diff     theta/B^(1/6): pred obs')
for B in sorted(obs):
    R, S, top, edge = obs[B]
    s23, _ = sum_n23(B)
    sig2R = fit * kappa * B ** (-1 / 6) * s23
    sig2 = sig2R * R / V0N
    thp = sig2 / math.sqrt(R * S)
    tp = V0N * (sig2 + R) * (sig2 + S) / sig2 / S if thp > 1 else edge
    # observed theta from lambda/edge = (sqrt(theta) + 1/sqrt(theta))^2 / 4
    r = top / edge
    tt = 4 * r
    tho = ((math.sqrt(tt) + math.sqrt(tt - 4)) / 2) ** 2 if tt > 4 else float('nan')
    print('%7d %6d %6d  %8.2f    %6.3f      %6.3f    %6.3f    %6.3f   %6.3f  %+6.2f%%     %.3f  %.3f' %
          (B, R, S, s23, sig2R, thp, tho, tp, top, 100 * (tp / top - 1), thp / B ** (1 / 6), tho / B ** (1 / 6)))
print('\nasymptotic constant: theta ~ 3 kappa fit rho sqrt(R/S) / v0 * B^(1/6) = %.3f B^(1/6)   (rho = 0.2594, R/S = 1.088)' % (3 * kappa * fit * 0.2594 * math.sqrt(1.088) / V0N))
