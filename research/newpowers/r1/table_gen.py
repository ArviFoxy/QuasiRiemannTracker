"""table_gen.py -- prints the exact classification tables used in the report (pure formulas, all cells are numerically verified in e12)."""
def code(m, k):
    r = (2 * m + k) % 6
    base = {0: '1', 3: 'Q', 2: 'C', 4: 'C', 1: 'S', 5: 'S'}[r]
    if r == 0:
        return '1' if m % 2 == 0 else 'e'
    return base if m % 2 == 0 else 'e' + base
print("leftover after dilating the residual by D^k, block D^m  (1 exact; e = only the ray sign eps(D,n);")
print("  Q quadratic chi^3, C cubic chi^{2,4}, S sextic chi^{1,5}; prefix e: times eps(D,n) when m is odd)")
print("m\\k  " + " ".join("%3d" % k for k in range(1, 13)))
for m in range(1, 7):
    print("m=%d  " % m + " ".join("%3s" % code(m, k) for k in range(1, 13)))
print()
print("minimal exact dilation exponent k(m) = 4m mod 6 (exact up to eps); cost k/m; free-variable exponent kappa = (5-m) mod 6 (n coprime to D)")
for m in range(1, 7):
    k = (4 * m) % 6
    kap_raw = k + m - 1
    rng_ = [j for j in range(1, kap_raw + 1) if j % 6]
    if m < 6:
        scal = "|gaussRow(D^m,h)| = N^{%s} exactly when v_D(h) = %d, else 0" % ((m - 1) / 2, m - 1)
    else:
        scal = "gaussRow(D^6,h) = -N^2 (v_D(h)=5), N^2 (N-1) (v_D(h)>=6), 0 (v_D(h)<=4)"
    print("m=%d  k=%d  k/m=%.3f  kappa=k+m-1=%d (mod 6: %d)  exact on residual columns with v_p(n) in %s ;  %s" %
          (m, k, k / m, kap_raw, (5 - m) % 6, rng_, scal))
