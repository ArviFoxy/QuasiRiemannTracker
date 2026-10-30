"""How the theta excess spreads over twists: is the excess span V low-dimensional?

The Poisson dual of the row Gram at source length L is a weighted copy of the family at the dual length H = B^2/L:
the dual frequencies h = m j^6 act on the rows as chi_z(m), so the twist m enters with multiplicity ~ (H/N m)^{1/6}.
Prediction: the twisted theta vector c_m(z) = conj G(z,1) chi_z(u) chi_z(m) profile(z) carries excess
r(c_m) - r_random ~ c (H/N m)^{1/6}, slowly decaying in N(m).  If so, removing the excess down to B^gamma needs every
twist with N(m) <= B^{1-6 gamma} in V, so V is not low-dimensional.

For a stratified sample of twists m (sources of E, log-uniform in N(m)) the script measures the dual energy ratio
r(c) = |E^T c|^2/(S |c|^2), averaged over the six unit twists u, against random-phase rows with the same twist and
profile.  It prints per-bin means and the fitted slope of log(excess) against log N(m) (prediction -1/6).

usage: python3 -I theta_twists.py B L [twists_per_bin] [bins]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
per_bin = int(sys.argv[3]) if len(sys.argv) > 3 else 16
nbins = int(sys.argv[4]) if len(sys.argv) > 4 else 16
rng = np.random.default_rng(7)
F = tc.build(B, L)
E, R, S, rows, SN, Grow, unit_tw, t0 = F.E, F.R, F.S, F.rows, F.SN, F.Grow, F.unit_tw, F.t0
H = B * B / L
prof = (rows['N'] / B) ** -0.5


def ratios(C):
    """r for each column of C (rows x k), in chunks."""
    out = np.empty(C.shape[1])
    for s in range(0, C.shape[1], 256):
        Cc = C[:, s:s + 256]
        V = E.T @ Cc
        out[s:s + 256] = (np.abs(V) ** 2).sum(0) / (S * (np.abs(Cc) ** 2).sum(0))
    return out


# ---- the untwisted theta (m = 1) and its random-phase baseline
th = np.conj(Grow)[:, None] * unit_tw * prof[:, None]
r1 = ratios(th)
ph = np.exp(2j * np.pi * rng.random((R, 24)))
rb = ratios(ph * prof[:, None])
base, sd = rb.mean(), rb.std()
print('H = B^2/L = %.0f.  untwisted theta r over the six units: %s, mean %.3f; random phases %.3f +- %.3f'
      % (H, np.round(r1, 3), r1.mean(), base, sd), flush=True)

# ---- stratified twists: log-uniform bins in N(m)
edges = np.exp(np.linspace(math.log(7), math.log(SN.max() + 1), nbins + 1))
picks = []
for b0, b1 in zip(edges[:-1], edges[1:]):
    idx = np.nonzero((SN >= b0) & (SN < b1))[0]
    if len(idx):
        picks.append(rng.choice(idx, min(per_bin, len(idx)), replace=False))
picks = np.concatenate(picks)
print('%d twists in %d bins; computing %d theta columns and %d random-phase columns' %
      (len(picks), nbins, 6 * len(picks), 2 * len(picks)), flush=True)

rt = np.empty(len(picks)); rc = np.empty(len(picks)); rp = np.empty(len(picks)); rr = np.empty(len(picks))
for s in range(0, len(picks), 64):
    P = picks[s:s + 64]
    tw = E[:, P]                                                   # chi_z(m) per column
    Ct = (np.conj(Grow) * prof)[:, None, None] * unit_tw[:, :, None] * tw[:, None, :]
    rt[s:s + 64] = ratios(Ct.reshape(R, -1)).reshape(6, -1).mean(0)
    Cc = (np.conj(Grow) * prof)[:, None, None] * unit_tw[:, :, None] * np.conj(tw)[:, None, :]
    rc[s:s + 64] = ratios(Cc.reshape(R, -1)).reshape(6, -1).mean(0)
    rp[s:s + 64] = ratios(prof[:, None] * tw)                      # plain twist, no Gauss sum
    rr[s:s + 64] = ratios(np.exp(2j * np.pi * rng.random((R, len(P)))) * prof[:, None] * tw)
    print('  %d/%d twists  (%.0fs)' % (min(s + 64, len(picks)), len(picks), time.time() - t0), flush=True)

Nm = SN[picks].astype(float)
print('\n  N(m) bin        n   theta chi(m)   theta conj chi(m)   plain chi(m)   random phases   excess    pred c(H/N)^(1/6)')
c_fit = (r1.mean() - base) / H ** (1 / 6)
rows_out = []
for b0, b1 in zip(edges[:-1], edges[1:]):
    sel = (Nm >= b0) & (Nm < b1)
    if not sel.any():
        continue
    ex = rt[sel].mean() - rr[sel].mean()
    nm = math.exp(np.log(Nm[sel]).mean())
    rows_out.append((nm, ex, sel.sum()))
    print('  [%6.0f,%6.0f)  %3d   %.3f          %.3f               %.3f          %.3f           %+.3f    %+.3f' %
          (b0, b1, sel.sum(), rt[sel].mean(), rc[sel].mean(), rp[sel].mean(), rr[sel].mean(), ex,
           c_fit * (H / nm) ** (1 / 6)))
x = np.array([math.log(a) for a, e, n in rows_out if e > 0])
y = np.array([math.log(e) for a, e, n in rows_out if e > 0])
if len(x) > 2:
    slope, icpt = np.polyfit(x, y, 1)
    print('\n  fit log(excess) = %.3f log N(m) + %.3f over %d bins with positive excess (prediction slope -1/6 = -0.167)'
          % (slope, icpt, len(x)))
sem = rr.std() / math.sqrt(per_bin)
print('  per-bin noise of the random baseline: sd %.4f per twist, ~%.4f per bin mean' % (rr.std(), sem))
print('done in %.1fs' % (time.time() - t0))
