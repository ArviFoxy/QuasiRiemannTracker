# Doubled marks in the source HIGH count

**Claim.** Every Dirichlet $L$-function is nonvanishing on $\Re s>\theta$ for

$$\theta \approx 0.8747521,$$

about $2.1\cdot10^{-5}$ below the current record $0.874772906$ (PR #70) and
$2.08\cdot10^{-5}$ below PR #69. The gain comes from one new argument in the
source step of PR #69 (Hailey Collet, *A zero-free half-plane from finite
ordinary source moments*). Everything else in that proof is reused unchanged.

Status: the argument is complete and the numbers come from a model of PR #69's
gates that reproduces all 221 of its certified source nodes. The exact rational
certificates and the Lean formalization for this specific graph are not yet
written (see the last section).

## 1. Where the change is

PR #69 proves a finite family of "ordinary source" moments
$G(B,\Lambda,h)$: $\mathcal E\ll U^{1+\epsilon}$ whenever
$m_1+m_2+\Lambda s\le B$, $0\le s\le h$ (sources.tex G1). Each new face is
derived from an earlier LOW parent and an earlier HIGH parent. The derivation
needs the HIGH gate (feedback.tex HF15, Lean `regular_gate_of_six`)

$$H+\mathcal G(S,F)>e_H,\qquad H=1-\rho-\nu T-a(5-6\rho),$$

on the whole density interval $\nu\in[q,3/4]$. Here $\mathcal G$ is the gain
from counting HIGH rows with the same-zero detector (feedback.tex HF2–HF7).

In that count the inverse witness uses the child's marked slots **at most once
each**. Its marked width is

$$z_I=\min\Bigl(S,\tfrac{Q-r}{2}\Bigr)\qquad\text{(sources.tex LD, feedback.tex HF3; Lean \texttt{inverseThreshold}, \texttt{fiber\_exponent})}.$$

The binding facet at every converged face is the "available slots / available
slots" branch with gain $\varphi S$. At the pivot $r\approx0.80$, so the inverse
capacity $(Q-r)/2\approx0.10$ is more than twice the available width
$S\approx0.042$. The capacity is therefore under-used.

## 2. The analytic input already exists: repeated prime lists

PR #69 foundations.tex, **Lemma 8.1 (overlap adapter for the inverse moment)**:

> The estimate of Theorem 7.3 remains valid for a fixed finite number of
> possibly overlapping or repeated prime lists with the same bounded annular
> coefficients. Both admission inequalities may use the full sum of the
> original slot widths.

The proof is a random $K$-colouring: distinct tuples get prescribed colours
with probability $K^{-K}$, so the full product is an average over products on
disjoint coloured lists. Repeated-prime tuples have bounded central mass and are
frozen before the row norm. The lemma is formalized in the dependency tree of
PR #69 as

`Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.overlapping_inverse_marked_energy`

It takes arbitrary lists `L : ι → Finset (Ideal O)` with no disjointness
hypothesis, and admits the energy whenever $r+2\sum_i\ell_i<1$ and
$2r+8\sum_i\ell_i<3$, with widths counted with multiplicity. PR #69 states the
lemma but never uses it in the source HIGH count.

### Lemma A (doubled-mark inverse gate)

Take a HIGH row fiber at density $\nu$ with available marked width $S$ in
amplitude class $p\in[0,1/2]$. For every $z\in[0,2S]$ with
$r+2z<Q-c_1$ and $2r+8z<3Q-c_2$,

$$\#\text{fiber}\ll U^{\,Q-\nu r-2\nu p z+\text{loss}}.$$

*Proof.* Order the marked slots by amplitude and give each a multiplicity
$k_i\in\{0,1,2\}$ greedily, filling width $z$ up to one mesh slot. The
amplitude per unit width of the selected multiset is at least the mean, so the
product has $|\prod_iQ_i^{k_i}|^2\ge U^{2\nu p z-\text{mesh}}$. Apply the
overlap adapter to the lists $L_{(i,c)}=L_i$, $c\le k_i$, and then use
Markov's inequality, exactly as in the one-copy gate `hIM` of
`fiber_exponent`. $\square$

## 3. Amplitude classes need their own detector cutoff

PR #69 passes from $p=1/2$ to general $p$ through the inequality
$2pz+(1-2p)S\ge z$ for $z\le S$ (LD, "the passage from $p=1/2$ ...";
Lean `amplitude_credit`). With $z>S$ this inequality fails. The fix uses the
fact that the detector cutoff is chosen per row class, before any witness is
taken (paper Prop. 4510; first-return §2 "choose $t=t_*$ before selecting its
witnesses"). An amplitude bin is such a class.

Write $w=5-6\nu$, $\xi_0=10/(3(5-2\nu))$, and let $(B_H,\Lambda_H,h_H)$ be the
HIGH parent. For $p\in[0,1/2]$ define the thresholds

$$I_p(\xi)=\max\Bigl(\xi-4pS,\ \frac{\xi-pQ}{1-p}\Bigr),\qquad
P_p(\xi)=\max\Bigl(\xi-2pS,\ \xi-2ph_HQ,\ \frac{\xi-2pB_HQ/\Lambda_H}{1-2p/\Lambda_H}\Bigr).$$

Let $\xi_p$ be the root of
$6\nu\xi+w\,(I_p(\xi)+P_p(\xi)/2)=5Q$. Put

$$f_p(S,Q)=(1-2p)\nu S+\nu(\xi_p-\xi_0Q),\qquad
\boxed{\ \mathcal G_2(S,Q)=\min_{0\le p\le 1/2}f_p(S,Q)\ }.$$

### Lemma B (weighted HIGH mass with doubled marks)

Put $x=\xi_0Q+\mathcal G_2/\nu$, and in amplitude class $p$ use the cutoff
$t_p=I_p(x_p')+P_p(x_p')/2$ with $x_p'=x-(1-2p)S$. Then the class's weighted
mass satisfies

$$E+2\nu pS\le Q-\nu x+\nu S+\text{loss}=\rho Q+\nu S-\mathcal G_2(S,Q)+\text{loss}.$$

This is HF10 with $\mathcal G_*$ replaced by $\mathcal G_2$.

*Proof.* By definition $x_p'\le\xi_p$, and the left side of the cutoff
equation increases in $\xi$, so $6\nu x_p'+w\,t_p\le5Q$. This pays the long
branch: for $r>1$, $E\le(1+5t_p)/6-\nu t_p\le Q-\nu x_p'$. The same-zero
alternative (Lean `same_zero_alternative`) gives either
$r\ge I_p(x_p')-\epsilon$ or $2m\ge P_p(x_p')$.

- In the inverse case take $z=\min(2S,(Q-r)/2)$. Then $r+2pz\ge x_p'$, and
  Lemma A gives $E\le Q-\nu x_p'$.
- In the plain case take $z_P=\min(S,h_HQ,(B_HQ-2m)/\Lambda_H)$, use the PR #69
  plain gate, and get $E\le Q-\nu x_p'$.

Adding the weight $2\nu pS$ gives $Q-\nu x+\nu S$. $\square$

At $p=1/2$ the thresholds are HF3–HF4 with $2S$ in place of $S$ in the inverse
branch. The six facets of HF6 become:

| inverse branch | plain branch | gain at $p=1/2$ |
|---|---|---|
| doubled slots | slots | $\tfrac53\varphi S$ |
| doubled slots | parent width cap | $\tfrac43\varphi S+\tfrac{\varphi h}{3}Q$ |
| doubled slots | parent affine cap | $\dfrac{4\nu w(\Lambda-1)}{D_{13}}S+\dfrac{\nu w(Bt_\nu-10)}{t_\nu D_{13}}Q$ |
| inverse cap | (three branches) | unchanged |

With $k$ copies the leading facet is $(2k+1)\varphi S/3$.

In almost the whole range of use, $\mathcal G_2=f_{1/2}$. A $p<1/2$ wins only in
a small corner, $\nu<0.53$ and $S/Q>0.058$, by at most $3\cdot10^{-5}$; the
minimizer there is $p\ge0.476$. The certificates use the exact minimum over
$p$.

## 4. Side conditions (all re-checked)

- **(C1) Common-width payment** (LD14a / HF12; Lean `common_gain_reserve`, which
  needs $\mathcal G(S,F)-\mathcal G(L,Q)-\nu(c+d)\le-(c+d)/12$).
  - $\mathcal G_2$ is a minimum of nonnegative affine forms in $(S,Q)$, one for
    each amplitude and branch pair. So the bound follows from a slope bound
    $a+2b\le\nu-1/12$ for a minimizing form at $(L,Q)$.
  - A minimizer with $p\ge0.476$ exists for every $\nu\ge0.505$ and every
    $L/Q\in[0,1]$. At $L=0$ all $p$ tie and $p=1/2$ is chosen.
  - On the new chain, for $\nu\in[q,3/4]$, $p\in[0.476,1/2]$ and all branch
    pairs, $\nu-1/12-(a+2b)\ge0.0145$. Every node has $q\ge0.5155$.
  - The crude bound $\varphi+2C_{\max}$ of HF12 must be replaced by this
    facet-wise bound, because $\tfrac53\varphi+2C_{\max}>\nu$ near $\nu=1/2$.
- **(C2) Root completion** (HF11–HF14, RT1).
  - The row-width coefficients do not involve $S$, so doubling leaves them
    unchanged, and each stays at most $C_{\max}=\nu(1-\xi_0)$.
  - $\mathcal G_2\le f_{1/2}\le C_{\max}Q$ by the slot-free facets.
  - So (HF13) and (HF14) apply verbatim.
- **(C3) Inverse admissions.**
  - $z\le(Q-r)/2$ and $r\ge I(x)-\epsilon\ge x-2S>Q/2$ give $2r+8z\le4Q-2r<3Q$
    with a fixed margin.
  - At the pivots, $r\approx0.80$, $r+4S\approx0.97<1$ and $2r+16S\approx2.27<3$.
- **(C4) Detector range.** The cutoffs $t_p$ lie in $[Q,\tfrac32Q]$ for every
  $p$; they run from $1.5(x-S)$ at $p=0$ to $1.5x-2.5S$ at $p=1/2$.
- **(C5) HF1 floor.** Every HIGH parent used has $B\ge0.95704>22/23$.

## 5. The new source chain

The chain starts from the natural premise $G(1,4.4973108,0.055)$, with natural
cost $K=6(2\theta_I-1)$ from PR #69's intermediate bound $\theta_I=0.8747759$.
It has 59 derived faces with monotone pivots
$b_\times=0.0135,0.0140,\dots,0.0420,0.04232$ and caps
$h=\min(0.0549989,\,b_\times+0.016)$. Each face uses the previous face as both
its LOW parent and its HIGH parent.

Each $\Lambda$ is the smallest value passing every PR #69 gate at both width
endpoints, with the HIGH gain $\mathcal G_2$ above. The gates are the scalar
LOW, centered, diagonal and cap gates, and the HIGH and special sectors on the
whole density interval. The gate model (`ss_fb.py`) accepts all 221 printed
nodes of PR #69's graph with reserves between $4.9\cdot10^{-10}$ and $10^{-8}$.
With one copy, the same construction lands within $1.3\cdot10^{-4}$ of
Hailey's height for face C.

| face | pivot | $B$ | $\Lambda$ | height at $s=0.0423245$ |
|---|---|---|---|---|
| PR #69 C (`alt_focused_g6_C`) | 0.04232 | 0.962261518 | 3.148131764 | 0.829018 |
| new C, two copies | 0.04232 | 0.956438687 | 2.955200319 | **0.831361** |
| PR #69 P (`alt_focused_g7_P`) | 0.03960 | 0.967390311 | 3.273079954 | 0.837776 at $s=0.0396$ |
| new P, two copies | 0.03950 | 0.962769810 | 3.109026905 | **0.839641** at $s=0.0396$ |

The same construction with one copy gives $0.828887$ and $0.837651$. The gain
from doubling is therefore $+2.47\cdot10^{-3}$ and $+1.99\cdot10^{-3}$ in face
height. This matches the envelope ODE ($+2.48\cdot10^{-3}$ and
$+2.00\cdot10^{-3}$).

## 6. The final return

These two faces go into PR #69's final return (first-return FR4–FR13): the new C
face feeds the same-zero count and the new P face feeds the physical numerator.
The return keeps every admission test of FR8, the weaker faces $B-j/4000$, and
the six conductor edges. The model is `model69.py`, validated against PR #69 to
$10^{-9}$. It gives

$$c=0.1252479354\quad(\text{PR \#69 in the same model: }0.1252270226),\qquad \Delta c=+2.09\cdot10^{-5},$$

that is, $\theta=1-c\approx0.8747520646$, at $h\approx0.79925$.

## 7. What remains for a verified submission

1. **Exact rational certificates.**
   - For each node, prove all gates with strictly positive reserves. The HIGH
     gate becomes a two-variable $(\nu,p)$ Bernstein check per branch pair.
   - Certify the two global lemmas: the minimizer location of (C1) and the slope
     bound.
   - Certify the return on Bernstein rectangles (FR14–FR16) with the new faces.
2. **Lean.** The changes are confined to `Record1252270103Source/High`:
   - `inverseThreshold` with $2S$;
   - a per-amplitude version of `fiber_exponent`;
   - `Facets` and `GainBounds` with the new slopes;
   - the graph and the return certificates.

   The analytic input (`overlapping_inverse_marked_energy`) is already proved.

## Files

- `rep_gain.py`: brute-force amplitude-resolved HIGH gain. It reproduces LD2
  without doubling.
- `gain_k.py`: exact closed-form $f_p$ and $\mathcal G_k$ with $k$ copies, plus
  the $p=1/2$ facets.
- `replay.py`, `check_hailey.py`: gate model and the check that all 221 PR #69
  nodes pass.
- `build_chain.py`, `build_chain_pmin.py`, `chainp_k2_0.0005.json`: chain
  construction with the exact amplitude-minimized gain, and the resulting
  59-node chain.
- `verify_chain_pmin.py`: re-verification of every node on a 401-point
  amplitude grid.
- `lip_p.py`: the slope bound of (C1).
- `price_faces.py`: the final return with the new faces.
