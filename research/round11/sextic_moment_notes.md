# Round 11 — sextic Möbius mean value: fresh-look notes

Target: Σ_{N(u)~U} |M_u(D,s)|² ≪ (U + D (U/D)^λ) Σ|μ|² N^{-2σ}, λ ≥ 0.16834, at D = U^{1.155}
(need gain ≥ U^{2.6e-4} over amplification bound U^{1/6} D^{5/6}).

Conventions in these notes: "PROVED" = rigorous argument sketched here; "HEURISTIC" = plausible
but not proved; "NUMERIC" = experiment output.

## Step 0 — setup
- Notes file created. Scripts go in this directory.

Context read: P1_PROBLEM.md (atom 2 section), round9/numerics/README.md, round10/README.md (§2, §5),
literature/README.md, STRUCTURE.md §1-4. Note from STRUCTURE §5: the rows are twists of a TARGET
character eta, so the coefficients are really mu(n)eta(n) (still multiplicative); s = the target zero
is ONE fixed point for all rows (no sup over t is needed).

## Step 1 — reformulations (analysis)

### 1a. Twist-averaging is easy (PROVED, given the same full-family large sieve that amplification uses)
psi_{u b^2} = psi_u * kappa_b (kappa_b = cubic symbol mod b), psi_{u c^3} = psi_u * lambda_c (quadratic).
Write Q(a) := sum_{u~U} |sum_n a_n psi_u(n)|^2. Then for fixed coefficient vector mu:
  sum_{b~B} Q(mu*kappa_b) = sum_{u,b} |M_{u b^2}|^2 <= C * sum_{v <= 4UB^2} |M_v|^2 <= C(UB^2 + D)||mu||^2
(each v = u b^2 has O(1) representations). Hence
  (1/B) sum_{b~B} Q(mu kappa_b) <= C(UB + D/B)||mu||^2  -> B = (D/U)^{1/2}:  2C sqrt(UD)  => lambda = 1/2.
Same with quadratic twists (c^3, cost C^3): lambda = 1/3.
So the AVERAGE over cubic twists of the long moment is far better than needed; the whole difficulty is
that we need one specific twist (the trivial one, or eta). This is the precise sense in which
"exchange rates 2 and 3" exist: they produce cubic/quadratic TWISTS, not copies. Exact copies need
sixth powers (Kummer), confirmed.

### 1b. Combining rates 2 and 3 does not produce copies (PROVED, elementary)
psi_{u c^2 b^3} = psi_u kappa_c lambda_b; a copy needs kappa_c = lambda_b = 1, i.e. c a cube and
b a square, i.e. u a^6 again. Writing psi_u = lambda_u * conj(kappa_u) and amplifying the two factors
separately puts the rows on the diagonal of the product family {lambda_x conj(kappa_y)}, whose size is
>= U^2 > D; extracting the diagonal costs a factor U. Dead.

### 1c. Thickened families (quadratic/cubic twist families) — what a large sieve would need to give
F2_W = {psi_y lambda_w : y~U, w <= W, all w} = {psi_{y w^3}}: contains sqrt(W) exact copies of each row
(w = c^2). F3_W = {psi_y kappa_w} = {psi_{y w^2}}: W^{1/3} copies (w = c^3).
If sum_{F}|M|^2 <= (|F| + D) X ||mu||^2 at the balanced point |F| = D, then
  F2 (W = D/U): sum_u |M_u|^2 <= 2X sqrt(UD)       -> suffices if X <= U^{0.0514} (= (D/U)^{1/3} U^{-2.6e-4})
  F3 (W = D/U): sum_u |M_u|^2 <= 2X U^{1/3}D^{2/3} -> suffices if X <= U^{0.0256}.
BUT (PROVED): for general coefficients sum_{F2}|<a,chi>|^2 >= sqrt(W) D ||a||^2 (take a = conj psi_{y0}),
so X >= (D/U)^{1/2} = U^{0.0775} > 0.0514 for general a: the gain must come from mu, exactly as for
a^6. Moreover sum_{F2}|M|^2 = sum_{w0 sqfree} (W/w0)^{1/2} Q(mu lambda_{w0}) is a weighted average of
twisted moments with weight sqrt(W) on our own family, so any scale-by-scale proof is circular.
Only a "holistic" proof (Poisson over the whole family at once) avoids circularity; for the full
family {psi_v : v <= H} Poisson in v shrinks the dual to D^2/H, but for a PRODUCT family Poisson
dualises each factor separately (dual volume D^4/|F| instead of D^2/|F|). That is the structural
reason sparse/product moduli sets do not help. (HEURISTIC but robust.)

### 1d. "Sparse moduli" for {u a^6}
As characters of n the moduli u a^6 give literally psi_u 1_{(n,a)=1}: no structure beyond copies, so
any large sieve for this sparse set is A * (large sieve for {psi_u}) for general coefficients
(PROVED). Answer to the question "structure beyond copies": none, for general coefficients.

## Step 2 — "simplest thing": bootstrap pointwise bounds x factorization x amplification (quantified)
Script: factor_split_mass.py, log: factor_split_mass.log (Poisson–Dirichlet model of prime-factor sizes).
Assumes round 10's global-strip bootstrap: every row zero-free right of beta* ~ 0.875, so every prime/
Moebius block of length B has |block|^2 <= B^{delta*} * (its diagonal), delta* = 0.749 (U^{o(1)} losses).
For a piece whose prime factors have log-sizes alpha_i (units log U, sum = t), put a sub-product of
total size s in the pointwise group, the rest in the mean-value group:
  cost(s) = delta* s + (5/6) max(0, t - s - 1)      (amplification alone: (5/6)(t-1) = 0.12917)
  gain(s) = s(5/6 - delta*) = 0.0843 s  for s <= t-1;  cost <= 0.1289 also for s in [0.155, 0.172].
So a configuration gains >= 2.6e-4 iff it has a sub-product with s in [0.0031, 0.1721].
NUMERIC (t = 1.155): mass with enough gain = 99.05%; median gain on it U^{0.011} (max U^{0.0131}).
Bad mass = 0.95% (0.23% with a prime >= U, 0.72% with all primes < U). delta* = 0.70: 0.59%;
delta* = 0.60: 0.26%. t = 1.30: 0.50%.
Bad set (PROVED, by the inequality above): n = m * r with m <= U^{0.0031} (any) and r U^{0.172}-ROUGH,
i.e. r = product of <= 6 primes each > U^{0.172}. On r no grouping beats amplification:
pointwise on any prime costs >= 0.749*0.172 = 0.129; fourth moments of a Type II p1*p2 with
p1,p2 >= U^{1/2} give exactly (5/12)(2t-2) = 0.129 (no gain, no loss); Hoelder never beats it.
CONSEQUENCE: this route improves the long moment by a CONSTANT factor (~50-100x asymptotically,
from the 1% core), not by a power. A power saving is EQUIVALENT (given the bootstrap) to a power
saving for the rough core alone:
  (CORE)  sum_u |sum_{r~R, P^-(r) > U^{0.172}} mu(r) psi_u(r) r^{-s}|^2 <= U^{-eta} Amp(R) ||.||^2,
          R in [D U^{-0.0031}, D].
The core is parity-sensitive: sieve (Type I) information cannot see it (sieve level D/U = U^{0.155}
< z = U^{0.172}, sifting ratio s < 1). This sharpens round 10 §5 ("every decomposition carries the
long prime sum"): it is not just the long prime sum, it is the whole U^{0.172}-rough part, whose
mass is ~1% of ||mu||^2 but carries no saving.

### 2b. CORRECTION to Step 2 (important)
Step 2 charged the mean-value group T cost 0 whenever its length is <= U. That is only available for
FULL Moebius blocks (inverse moment via Poisson + theta reflection, needs the Hasse–Davenport identity
for mu*g6). For general coefficients (products of prime blocks, rough Moebius, mu*x^{omega_I}) the
sextic sieve (7/8 Lemma 9.1) carries (UN)^{2/3}: T-cost = max(0, (2y-1)/3). With that cost model:
  cost(s) = 0.749 s + (1.31 - 2s)/3 = 0.437 + 0.082 s  (s <= 0.655), or 0.749 s >= 0.49 otherwise
=> NO configuration gains. Flexible grouping is worthless with the tools that exist; only identities
of the form mu*w = f * mu (full Moebius in T), e.g. mu log = -Lambda * mu or Ramare, can be used, and
round 10 §1 already shows they reproduce the lattice game (85% of log-mass sits on prime factors
> U^{0.172}, whose pieces lose).
So Step 2 is a CONDITIONAL reduction:
  IF (A) the sextic family had a diagonal mean value for prime-product coefficients up to length U
     (i.e. no Gauss-bias term (UN)^{2/3} for such vectors), THEN with the bootstrap 99% of the mass
     gains up to U^{0.013}, and the problem reduces to (B) = the U^{0.172}-rough core (~1% mass),
     which still needs its own power saving.
Both (A) and (B) are open; (B) is parity-sensitive. So no power saving from this route.

### 2c. Weighted witness mu*omega_I (checked, fails for the known reason)
mu(n) omega_I(n) = -sum_{p|n, p in I} mu(n/p) gives an exact factorization P_I(s) * M(D/P) with a full
Moebius block, so its long moment gains (5/6 - delta*) log_U P. It only counts bad rows at which the
prime band P_I is not small. Round 10's adversary (zeros in a vertical progression of spacing
2pi/(s0 log U)) makes prime bands coherent only at scales U^{k s0}, so for I below U^{s0} the weighted
witness is NOT large on adversarial rows. Small-ball bounds for P_I over the family cannot be made
power-small either (only ~log U/log P_max moments are controlled). Dead, consistent with round 10.

## Step 3 — is sub-problem (A) (no Gauss bias for the dyadic family) visibly true? (NUMERIC)
Script ls_constant_support.py; logs ls_constant_U3000.log, ls_constant_U8000.log.
Delta = sigma_max(Psi)^2 for Psi[u,n] = psi_u(n), rows = actual family (R = 778 / 2076), flat weights,
columns = split primes / U^{0.3}-rough squarefree / all squarefree, N(n) in [N, 2N), N = U^y.
  Delta / (sqrt R + sqrt C)^2 = 0.93 - 0.99 (U=3000), 0.95 - 1.00 (U=8000), every support, y = 0.5..1.155.
  A (RC)^{2/3} Gauss-bias term would be 2.6 - 3.6 x the edge at U=8000: it is ABSENT.
Reading: for rows of norm exactly ~U the general-coefficient large sieve is at the Marchenko–Pastur
edge, i.e. the conjectured (U + N)^{1+o(1)}. The sharp extra terms of De Faveri / Lemma 9.1 come from
families containing small moduli (twisted-theta main terms scale like N(m)^{-1/3}, so for dyadic
m ~ U they are at most ~N^{2/3}U^{1/3} < max(U, N)). (HEURISTIC for the last sentence.)
So (A) is very likely TRUE and possibly provable by tracking Patterson-type main terms for dyadic
moduli; but by Step 2b, (A) + bootstrap only localizes the problem to the rough core (log saving).

## Step 3b — the core IS round 10's adversary (consistency check, analysis)
Round 10: the adversary sits at t = 3 s0, s0 = 0.385, i.e. the configuration (0.385, 0.385, 0.385):
three primes of size U^{0.385} -- inside the U^{0.172}-rough core. Its count via the sixth moment of
Q(P) = sum_{p~P} psi_u(p) p^{-s}, P = U^{0.385}:  sum_u |Q|^6 = sum_u |Q^3|^2 (length P^3 = D)
by amplification -> count exponent 1/6 + (5/6)(1.155) - 3(0.385)(0.455) = 0.6036 = R (exactly the
game value). Fourth moment (needs (A) at length U^{0.77}): 1 - 2(0.385)(0.455) = 0.65 (worse).
So the irreducible atom can be stated as a SIXTH MOMENT OF A SHORT PRIME POLYNOMIAL:
  (ATOM)  sum_{u~U} |sum_{p~P} psi_u(p) p^{-s}|^6 <= U^{1.129 - eta} (E|Q|^2)^3,  P = U^{t/3}.
This is cleaner than the long Moebius moment (no mu, length P < U^{1/2}, only the 6th power is long),
and it is exactly where amplification binds. Newton expansion Q^3 = 6 e3 + (mixed terms of mass
O(1/P)) shows the cube is generic squarefree; the quadratic piece sum_p psi_u(p)^3 = sum_p lambda_u(p)
is negligible. (PROVED-level bookkeeping; the bound itself is open.)

## Step 4 — answers to the framing questions, named assumption, next steps

### Averaging that thickens the family
- Twists (1a): the average over cubic twists is easy (lambda = 1/2), BUT per unit of conductor the twisted
  family {psi_{ub^2}} (conductor ~UB, size UB) has per-row bound 2 D^{5/6} U^{-5/6} B^{-2/3}, while the
  plain squarefree family at the same conductor X = UB has 2 D^{5/6} X^{-5/6} = 2 D^{5/6}U^{-5/6}B^{-5/6}.
  The twisted family is WORSE by B^{1/6}. So "rate 2" is conductor enlargement in disguise. It helps
  only if the global count prices rows by number rather than by conductor (to be checked by the
  owners of the chain; HEURISTIC).
- s (t-aspect): no exact copies in t (rate infinity); hybrid family size UT; best T = 1. Worse than
  amplification by (D/U)^{1/6} if used instead of it; no gain if combined. (PROVED, elementary.)
- amplifier variable a: copies are exact on (n,a) = 1; the deviation is a shorter Moebius sum
  (M_{up^6} = M_u + psi_u(p) p^{-s} M_u^{(p)}(D/p)); averaging over a is exactly amplification.
  Nothing extra.
- BDH/dispersion need the full character group per modulus (orthogonality -> congruences). Any
  thickening + positivity loses the thickening factor; a slice comparison needs equidistribution
  in the twist, which is the problem again. Dispersion in (u,u') runs into the same self-dual
  Poisson step (P-V alone gives U^{1.5}D^{0.5} >> target).

### Named assumption
Not Kummer rigidity per se (1a shows cheaper rates exist but cost conductor). The load-bearing
assumption is: THE WITNESS MUST BE CONTROLLED ON THE U^{0.172}-ROUGH PART OF ITS SUPPORT.
Equivalently (Step 3b) one must bound a sixth moment of a prime polynomial of length U^{t/3}.
If the long witness could be supported on n with a prime factor in [U^{0.003}, U^{0.172}]
(and (A) holds), bootstrap + grouping gives up to U^{0.013} >> U^{2.6e-4}. The lattice adversary
lives exactly on the complement, so this cannot be had for free.
Secondary: the (UN)^{2/3} Gauss-bias term of the available sextic sieve. Numerically it is absent
for the dyadic family (Step 3); proving that removes "no mean value for prime sums beyond U^{1/2}".

### Ranked next steps
1. ATOM (Step 3b): sum_u |Q_u(U^{t/3})|^6 below U^{1.129-eta}(E|Q|^2)^3. Mu-free, short polynomial;
   in the Poisson dual Q^3 becomes a TRILINEAR Gauss-sum form with cubic cross-symbols
   prod (p_i/p_j)_3: the structure that Heath-Brown's cubic sieve and Dunn–Radziwill's Type II
   exploit. Needed: a mean-square (over dual frequency) saving, not pointwise.
2. Prove (A): diagonal sextic large sieve for rows N(u) ~ U and N <= U (numerically at the MP edge,
   Delta/edge 0.95-1.00 at U = 8000). Yields with the bootstrap a 50-100x constant / log saving and
   reduces atom 2 to the rough core; also lifts the U^{1/2} barrier for prime sums used elsewhere.
3. Check with the chain owners whether rows can be priced by count (then twisted families give
   lambda = 1/2); low probability, cheap to check.
4. Metaplectic: mu*g6 = theta_3 coefficients (Hasse–Davenport) on the dual side; a spectral large
   sieve for sextic twists of theta_3 at K = D^2/U > D. Long-term.
