# P1 via signal processing / high-dimensional probability (fresh7c, 2026-10-25)

Status labels: **[R]** rigorous (proof sketched here, standard tools), **[H]** heuristic,
**[N]** numerical (model over Z[omega], scripts in this directory).

Model ([N] throughout): columns = primary split-squarefree n with N/2 < N(n) <= N (O/n = Z/N(n));
rows = primary split-squarefree k with N(k) <= K; marks = primary split primes P with L < N(P) <= 2L;
beta = g~(n) = g(n)/sqrt(N(n)), g(n) = sum_{x mod n} (x/n)_3 e(Tr(x/(n sqrt-3))), computed exactly
(direct sums for primes, twisted multiplicativity for composites, checked against direct sums to 1e-15).
Counts: K' rows, N' columns, L' marks.

## 0. Verdict

No signal-processing tool closes P1. Each tool either (a) uses only statistics of the coefficient
vector that an explicit adversary also has, while the adversary attains the N-term, or
(b) reduces P1 to an equivalent statement at the same self-dual point. Three things come out of the
attempt:

1. **A rigorous random-model theorem.** Matrix concentration (non-commutative Khintchine) proves
   the diagonal bound K·N·log for beta with independent random phases. Independence is needed only
   per multiplicative block {pi·m}. The only inputs are the two large sieves used as black boxes.
   So the factor N/K = L lost by the hybrid lemma is exactly the price of treating the product of
   two operator norms as the operator norm of the product, and P1 is a derandomization problem.
2. **A structural fact the project notes do not record.** In the paper the marks are sextic
   characters, so chi_P(n)^{-2} = conj((n/P)_3). With twisted multiplicativity this gives
   beta(n)·chi_P(n)^{-2} = g~(nP)/g~(P). The slot space W is spanned by prime dilates of the theta
   coefficients. For smooth (Type I) slots, Poisson in the slot variable cancels the Gauss sum
   exactly, and the column vector becomes a short sum of cubic characters. In the model, 98.8–99.2%
   of its energy lies in a span of 3–9% of the dimension. Smooth-slot P1 is therefore implied by a
   Gauss-sum-free uncertainty principle between quadratic and cubic characters (Lemma Q3). That is
   precisely the uncertainty principle of idea 1, and it is numerically random-like.
3. **Sharp no-go statements.** These cover coherence, uncertainty principles, paving, sketching,
   moments, pointwise Lindelöf, and every "algebraic-only" proof (sections 3.1–3.7).

The residual hard core is the Type II part of the prime slots, with bilinear slot coefficients. On
it, every positivity step re-creates the N-term as the diagonal of an overcomplete dual sieve
(section 3.8).

## 1. Conventions and three structural facts

**1.1 Orientation and absorbability [R + N].** Paper: chi_p(a) = (a/p)_6 (sextic), so chi_k^3 = (./k)_2
and chi_P^{-2} = conj((./P)_3). The toy `atom1/toy/colbranch_exp.py` used (n/P)_3, which is the
conjugate. The orientation makes no numerical difference (tables below), but it does matter
structurally. Twisted multiplicativity in this normalization is

    g(c1 c2) = conj((c1/c2)_3) g(c1) g(c2)        (checked: test_gauss.py),

so

    g~(n) conj((n/P)_3) = g~(nP)/g~(P)             (checked to 9e-16: test_absorb.py; the other
                                                    orientation fails by O(1)).

Hence c = beta·A = sum_P a''(P)·D_P g~, where (D_P f)(n) = f(Pn) and a''(P) = a'(P)/g~(P). W is the
orbit of the theta coefficients under prime dilations.

- *Interpretation.* For a GL(2) Hecke eigenform, dilation by a prime is Hecke-free
  (lambda(pn) = lambda(p)lambda(n) − lambda(n/p)). The twisted L-function of the dilate is then a
  degree-1 polynomial in p^{-s} times L(s, f⊗chi), and the level does not grow.
- For theta_3 only dilations by cubes are Hecke operators (T_{p^3}). A prime dilation equals a
  cubic twist, i.e. level P^2.
- This is the precise reason why marks raise the conductor and cube marks do not (README "cube
  marks lose the sextic slot factor").

**1.2 The cubic sign [R + N].** g~(pi)^3 = lambda(pi) := pi/|pi| (classical: g^3 = p·pi). This
extends to all squarefree n, and g~(n)^2 = conj(g~(n))·lambda(n) (Jacobi sum J(chi,chi) = pi;
verified numerically). So g~ = lambda^{1/3}·omega^{e(n)}, and all of the arithmetic sits in the
choice of cube root e(n), which Heath-Brown–Patterson equidistribute.

**1.3 Smooth slots cancel the Gauss sum [R heuristic-exact + N].** Let
A_I(n) = sum_{P primary} w(N(P)/L) N(P)^{-1/2} conj((n/P)_3) be the slot sum over all P, not just
primes. Cubic reciprocity gives conj((n/P)_3) = conj(chi_n(P)) with chi_n = (./n)_3 primitive mod
n. Poisson in P (lattice 3O, modulus n) produces tau(conj chi_n, mu) = chi_n(mu)·conj(g(n)), so

    g~(n) A_I(n) = (L/N)^{1/2} · sum_{N(mu) <~ 27 N/L} phi(N(mu)L/N(n)) (mu/n)_3      (no Gauss sum).

- In the toy orientation one gets g~(n)^2 = conj(g~(n))·lambda(n) instead, and nothing cancels.
- Numerically (exp_typeI.py, K=600, N=60000, L=6000, Gaussian slot weight, N'=7796): 98.8%, 99.1%
  and 99.2% of ||c_I||^2 lies in the span of the cubic characters mu -> (mu/n)_3 with N(mu) <= 135,
  270 and 405. That span has dimension 237, 456 and 705, i.e. 3.0%, 5.8% and 9.0% of N'.
- For comparison, the other orientation puts 6.5%, 11.6% and 15.9% there; random phases 2.9%,
  5.5% and 8.7%; A_I alone 15–25%.

## 2. Exact SP reformulations

- **(R1) Subspace angle.** P1 for arbitrary slot coefficients is ||P_V P_W||^2 <= N^{-eta}.
  - V = span{(./k)_2 : k <= K}, of dimension K. W = span{D_P g~ : P ~ L}, of dimension L. Both live
    in C^N with N = KL.
  - Random subspaces of these dimensions have (sqrt(K/N) + sqrt(L/N))^2 ≈ 1/L.
  - [N] max cos^2 = 0.0493 against a random-subspace edge of 0.0525 (K'=156, N'=7796, L'=60).
- **(R2) Stable rank.** Let S(k,P) = sum_n beta(n)(n/k)_2 chi_P(n)^{-2} be the K×L matrix of
  twisted central values. Then the column branch with arbitrary a satisfies sup = ||S||_op^2, and
  P1 ⟺ ||S||_op^2 <= N^{2−eta}. Equivalently, since ||S||_F^2 ≈ KLN = N^2, the stable rank of S is
  at least N^eta.
  - A random-like S has stable rank ≈ L.
  - [N] At K'=156, N'=7796, L'=60: ||S||_op^2/(N'(sqrtK'+sqrtL')^2) = 0.92–0.93,
    ||S||_F^2/(K'L'N') = 0.92–0.95, stable rank 22.5–23.6. An iid Gaussian matrix gives 0.93, 0.98
    and 23.9. The adversarial beta = (n/k0)·conj chi_{P0} gives 15.2, 1.49 and 2.2.
- **(R3) What the two uses need.**
  - Use (a), the inverse-moment budget (README table: column branch <= Z^{0.871−0.0011}): any bound
    (K + N^{1−eta}K^{eta})||c||^2 with **eta >= 0.0085** suffices, since N/K = Z^{0.129}. The LOG
    remark "K + N^{1−eta}K^eta never suffices" applies only to use (b).
  - Use (b), the probe at N = K^{1+1.3e-4}: needs the off-diagonal a power below the diagonal at
    N ≈ K.
  - The two requirements are different. Use (a) is a power saving in the N-term at N = K^{1.17}.

## 3. Idea by idea

### 3.1 Uncertainty principles / incoherence

- **Claim tested.** ||Proj_V c||^2 <= (K/N)^{1−eta}||c||^2 for c = beta·A.
- **Coherence-type uncertainty principles [R no-go].** These are Donoho–Stark, Elad–Bruckstein,
  Gershgorin and Schur. Their bounds read ||P_V P_W||^2 <= ||P_V P_W||_F^2 = ||S||_F^2/N^2 (up to
  Riesz constants) <= KL·max|S|^2/N^2. They can never beat ||S||_F^2/N^2, which is ≈ 0.92–0.98 [N]
  (KLN = N^2 at the binding).
  - The same applies to "pointwise Lindelöf for every L(1/2, theta⊗chi_k⊗chi_P)", i.e.
    |S(k,P)| <= N^{1/2+eps}. It gives only ||S a'||^2 <= K(sum_P q_P^{-1/2})^2 N = N^2. A K×L matrix
    with flat entries can be rank one.
  - **Even GRH for every twist does not imply P1 for arbitrary a(P).** One also needs the L-values
    to decorrelate across marks P ≠ P' (Lemma MM below).
- **Spread adversary [R].** c' = (1/sqrt K) sum_k eps_k chi_k attains ||Phi c'||^2 ≈ N||c'||^2. It
  has the flat coherence |<c',chi_k>|^2 ≈ N^2/K = N·L for every k. To exclude it pointwise one needs
  |S_k|^2 <= N·L·N^{-eta}, which is near-Lindelöf in the k-aspect (convexity at this length is N^2).
- **Prime-slot uncertainty principle (Lemma Q3).** What does come out positively is the uncertainty
  principle that P1 reduces to for smooth slots (1.3). It is stated as Lemma Q3 in section 5.
  - [N] quadratic span (156) against cubic span (237/456/705): max cos^2 = 0.084/0.127/0.172
    against random edges 0.100/0.147/0.196. It is random-like.
  - But Poisson in n maps Lemma Q3 back to cubic Gauss sums at mu, twisted by (k/mu)_6 (the
    Gauss-sum content is conserved). Coherence-type proofs of Lemma Q3 fail as well: Burgess entries
    give ||E|| <= K^{11/8}N^{1/2} > N.

### 3.2 Matrix concentration / non-commutative Khintchine

- **Theorem [R].** Write S = sum_n beta(n) phi_n x_n^T with phi_n = ((n/k)_2)_k in R^K and
  x_n = (chi_P(n)^{-2})_P in C^L.
  - Partition the columns into multiplicative blocks: choose any divisor d(n) | n with
    N(n/d(n)) <= M <= K, and put B_d = {n : d(n) = d}, a set of multiples d·m with N(m) <= M.
    Such a choice exists for every n, including smooth n, by multiplying prime factors until the
    product exceeds N/K.
  - Let beta(n) = eps_B·beta_0(n), where the eps_B are independent Steinhaus or Rademacher signs and
    |beta_0| <= 1 is arbitrary (it may depend on the block).
  - Matrix Rademacher series (Tropp 2012, Thm 4.1.1) give E||S||_op <= sqrt(2 log(K+L))·sigma,
    where sigma^2 = max(||sum_B S_B S_B^*||, ||sum_B S_B^* S_B||).
  - Use S_B S_B^* <= ||X|_B||^2 Phi_B Phi_B^* and S_B^* S_B <= ||Phi|_B||^2 X_B^* X_B. On a block,
    Phi|_B and X|_B are the length-M sieves (row signs chi_k(pi) and chi_P(pi) factor out). This
    gives

        sigma^2 <= max( (M + L + (ML)^{2/3})·(K+N),  (K+M)·(N + L + (NL)^{2/3}) ) (KN)^eps
               ≈ K N   for M <= K, at N = KL.

  - So **E(column branch) << K·N·log** for every slot vector with ||a'|| ≍ 1: the diagonal. Blocks
    of size 1 (fully random beta) are included.
  - [N] exp_spectral.py already shows ||S||_op^2 is the same for the true g~ and for fully random
    beta (0.92 against 0.90 times N'(sqrtK'+sqrtL')^2).
  - exp_frame_nck.py (block-randomized beta, explicit sigma^2) is written but was **not executed in
    this session**, because the shell was unavailable at the end.
- **Where it breaks.** The proof needs only E[eps_B conj(eps_B')] = delta. Derandomizing needs
  moment bounds tr((SS^*)^m) for the actual Gauss sums.
  - The diagonal of those moments contains sum_P F_P^m, so it already requires the single-mark
    bound F_P = ||Phi(beta·chi_P^{-2})||^2 <= N^{2−eta}. The single-mark problem sits at its own
    self-dual point N = K·N(P).
  - The m = 2 moment even needs F_P <= N^2/sqrt L, which is stronger than P1.
  - Random a(P) instead gives sum |a'|^2 F_P (README).

### 3.3 Moment method / operator norm against Frobenius

- [R] tr((S^*S)^m) >= sum_P F_P^m and tr((SS^*)^m) >= sum_k (sum_P |S(k,P)|^2)^m. So a moment proof
  needs both of the following:
  - per-column bounds, i.e. single-mark P1 (quadratic N-term);
  - per-row bounds sum_P |S(k,P)|^2 <= L·N^{1+o(1)}. Heath-Brown's cubic sieve gives only N^2 here
    (its N-term; the truth is LN).
- No normalization avoids this. Whitening rows or columns needs the same row and column bounds.
- Splitting ||S^*S|| <= max_P F_P + ||offdiag|| shows that P1 follows from:
  - (i) single-mark P1 uniformly in P; and
  - (ii) the mixed-moment bound sum_{P≠P'} |sum_k S(k,P) conj S(k,P')|^2 <= N^{4−2eta}.
- Both have no main term issue: the mixed diagonal is K·sum_n chi_P^{-2} conj(chi_{P'}^{-2})(n),
  which is small. But both sit at the self-dual point.

### 3.4 Frame theory, frame potential, paving

- **Row paving** is exact (||Phi c||^2 = sum_j ||Phi_{R_j} c||^2) but useless: ||Phi_{R_j}||^2 >= N
  for any nonempty block.
- **Column paving** (MSS / Anderson). diag(P_V) ≈ K/N, so there are partitions into r ≈ N/K blocks
  with ||P_T P_V P_T|| <= 4K/N. The arithmetic blocks {pi·m : m ~ K} achieve ||Phi|_T||^2 <= K + M
  explicitly.
  - [R] Any bound of the form sum_j ||Phi|_{T_j}|| ||c_{T_j}|| is >= ||Phi||_op ||c|| on the
    extremal c. So the gain can only come from cross-block cancellation, and the cross terms are
    exactly the original off-diagonal G(n,n') = sum_k chi_k(nn') for n, n' in different blocks.
  - 3.2 shows that random block phases would supply that cancellation.
- **Frame bounds** of the quadratic dictionary. exp_frame_nck.py measures the spread of
  sigma^2(Phi)/N' (not executed, see 3.2).
  - [H] Poisson in n suggests the spread is O(1) about 1, with the deviation living on a
    subspace of dimension ≈ K/L (the dual length K^2/N), signed by reciprocity classes.

### 3.5 Sketching / random restrictions

- [R] Restricting to n ≡ 0 (q) with q ~ N/K makes every restricted problem diagonal:
  sum_k |sum_m c(qm) chi_k(m)|^2 <= (K + N/q)||c_q||^2.
- The recombination identity is
  ||Phi c||^2 = sum_q ||v_q||^2 + sum_{q≠q'} sum_k (qq'/k)_2 T_q(k) conj T_{q'}(k),
  with T_q(k) = sum_m c(qm)(m/k)_2.
- The cross terms are the original off-diagonal grouped by (q,q'). The triangle inequality returns
  N. Random restrictions change the quantity instead of bounding it.

### 3.6 Dual certificates / majorants

- [R] A certificate for ||P_V c|| small is a psd majorant T >= P_V with <c,Tc> computable.
- Majorants built from larger character families give their frame bound, which is >= the N-term
  whenever the family contains the extremal directions.
- Arithmetic majorants (Poisson/Voronoi) see c, but at N = KL they are involutions: the dual
  diagonal equals the original N-term, and the signed dual is the original problem (LOG "P1 seen
  three ways", claim (i), confirmed).

### 3.7 Own: the algebraic no-go (rigorous adversary)

- **Construction.** Change beta only on prime columns pi with N(pi) > N/7. These divide no
  composite column, since composite norms are >= 7·N(pi). Choose beta'(pi) in
  lambda(pi)^{1/3}·{1, omega, omega^2} to make c' = beta'A correlate with chi_k0, or with a spread
  F = sum_k eps_k chi_k.
- **Every algebraic identity survives:** |beta'| = 1, twisted multiplicativity, beta'^3 = lambda,
  and all composite values. Yet, choosing the cube root within 60° of the phase of the composite
  part's correlation, |<c',chi_k0>| >= (1/2) sum_{pi~N} |A(pi)| ≈ c·(N/log N)·(E|A|^2)^{1/2}.
- **Consequence.** ||Phi c'||^2 >> (L/log^2 N)·K·N, a power violation. Any proof must use the
  automorphy of theta_3 (Voronoi-type, analytic input) at prime arguments, and that is self-dual at
  N = KL.
- [N] exp_prime_adversary.py: ratio to the diagonal 3.59/2.80 at (K,N) = (300, 12000) and
  5.78/3.87 at (600, 60000), for the single and spread versions; marked versions 3.41/2.80 and
  5.33/3.56. Allowances are 22.6 and 53.7.
- [N] exp_adversary.py: coordinate ascent over all prime values (twisted multiplicativity kept) at
  (300, 12000) reaches 13.1 with free phases and 9.7 under the cube-root constraint, out of 22.6.

### 3.8 Own: prime slots = Type I + Type II

- Heath-Brown or Vaughan for the prime slot weights splits them into two types.
- **Type I** pieces have a long smooth slot variable e. Poisson in e cancels g~(n) (1.3), and the
  column vector becomes a cubic-character polynomial with short twists conj((n/d)_3). This leads to
  Lemma Q3. The cubic span has dimension NL^2/E^3 < N when E > L^{2/3}.
- **Type II** pieces (slot = de, both >= L^theta, arbitrary coefficients) are the hard core.
  - Cauchy over d, a positivity extension to all d ~ D, and Poisson in d again cancel the Gauss sums
    exactly. The cross term conj((n'/n)_3)(n/n')_3 = 1 by reciprocity.
  - What remains is sum_{h <~ N^2/D} |sum_n A_2(n)B(n)(h/n)_3|^2, an overcomplete cubic sieve whose
    *diagonal* is the N-term. So positivity is fatal here, exactly as LOG claim (i) says.

## 4. Numerics summary

| quantity | model value | random-model value | aligned/adversarial |
|---|---|---|---|
| ‖Φc‖²/Diag, c = g~·A (both orientations), several sizes | 0.87–1.03 | 0.97–1.09 | 13.7–46 |
| ‖P_V c‖²/(K'/N') | 0.87–1.06 | 0.95–1.10 | 12–50 |
| stable rank of S (L'=60) | 22.5–23.6 | 23.9 (Gaussian) | 2.2 |
| max cos² V vs W | 0.049 | edge 0.0525 | — |
| single-mark F_P/Diag_P (60 marks) | 0.81–1.17 (mean 1.00) | — | — |
| c_I in cubic span (dim 3–9%) | 98.8–99.2% | 2.9–8.7% | — |
| algebraic adversary ratio | — | — | 2.8–5.8 (primes only), 9.7–13.1 (all primes) |

Logs are in `logs_*.txt`. Data is cached in `data/`.

## 5. The cleanest open lemmas

- **Lemma Q3 (quadratic–cubic uncertainty principle; implies P1 for smooth/Type I slots).**
  - Let W be smooth, N = K^{1+delta} with delta ≈ 0.17, and M ≍ 27N/L ≍ K.
  - Let E(k,mu) = sum_n W(N(n)/N) mu^2(n) (n/k)_2 (mu/n)_3, for k ranging over nontrivial
    squarefree k <= K and mu ranging over N(mu) <= M with (mu/.)_3 nontrivial.
  - Claim: ||E||_op <= N^{1−eta}.
  - Trivially ||E|| <= N^{1+eps} (product of two large sieves). The random value is ≈ 2·sqrt(KM).
  - For use (a), ||E||_op^2 <= N^2 (K/N)^{0.0085}, i.e. ||E||_op <= N^{1−0.00063}, suffices, since
    C_I ≈ (L/N)||E phi||^2 ≲ 27||E||^2.
  - Equivalently: no function on n ~ N lies close to both the quadratic span and the cubic span.
  - It is free of Gauss sums and theta functions, but Poisson in n turns it back into cubic Gauss
    sums twisted by sextic characters.
- **Lemma BD (block decoupling, which derandomizes 3.2).**
  - For blocks B_pi = {pi·m : m ~ M <= K}, take S_pi(k,P) = sum_m g~(m) conj((m/pi)_3) chi_k(pi m)
    chi_P(pi m)^{-2}.
  - Claim: ||sum_pi g~(pi) S_pi||_op^2 <= N^{o(1)} max(||sum S_pi S_pi^*||, ||sum S_pi^* S_pi||).
  - True for independent random phases [R]. Implies P1 [R].
- **Lemmas SM + MM (single-mark and mixed second moments).** This is the pair (i) and (ii) of 3.3.
  It is the minimal input for a moment proof.

## 6. Files

All files are in this directory. Each script prints its log.

| file | contents |
|---|---|
| `zw.py` | Z[omega] arithmetic |
| `build.py` | data cache |
| `test_gauss.py` | twisted multiplicativity and g~^2 = conj(g~)·lambda |
| `test_absorb.py` | absorbability (1.1) |
| `exp_spectral.py` | (R1), (R2), single marks |
| `exp_adversary.py` | coordinate-ascent adversary (3.7) |
| `exp_prime_adversary.py` | prime-column adversary (3.7) |
| `exp_typeI.py` | Gauss-sum cancellation and Lemma Q3 angles (1.3, 3.1) |
| `exp_frame_nck.py` | frame bounds and the NCK check (3.2, 3.4); not run |
| `logs_*.txt` | verbatim outputs of the runs |
