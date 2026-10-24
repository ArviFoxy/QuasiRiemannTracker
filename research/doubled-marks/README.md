# Doubled marks in the source HIGH count

> **Superseded.** See `../repeated-marks/README.md`. It uses each slot up to $K$ times,
> replaces §4's (C1) argument by a general payment lemma (Lemma C), and removes
> PR #69's conservative return guards (Lemma D). The certificate below remains valid for
> the doubled-mark chain. One correction from independent review: PR #69 already routes
> the HIGH inverse field through the overlap adapter (pools may overlap); what it never
> does is repeat a slot.

**Result.** Every Dirichlet $L$-function is nonvanishing on

$$\Re s>\theta=\frac{8747514}{10^7}=0.8747514,$$

excluding the principal pole. The current record is $0.874772906$ (PR #70)
and PR #69 had $0.8747729897$. The new bound is lower by
$2.15\cdot10^{-5}$.

The gain comes from one new argument inside the source step of PR #69 (Hailey
Collet, *A zero-free half-plane from finite ordinary source moments*): the
source HIGH count may use each marked slot twice in its inverse witness. The
analytic input for this is already proved in PR #69's dependency tree; PR #69
states it but never uses it in the HIGH count. Every other part of PR #69 is
reused unchanged.

The doubled-mark gate also forces a per-amplitude detector cutoff (§3) and a new
source graph (§5). One return parameter changes: the free-shift cutoff $t_f$
(§6).

**Status.**
- The mathematical argument is complete (§§2–4).
- Exact rational-arithmetic certificates (Bernstein expansions over $\mathbb Q$,
  no floating point) cover the new 59-face source graph and the final return.
  They are in `certificate_doubled_marks.json`, produced by `certify_all.py`.
- The certifier for the return reproduces PR #69's own final certificate
  exactly (`test_return69.py`).
- Not yet done: the Lean formalization required for admission to the tracker
  (§7).

## 1. Where the change is

PR #69 proves a finite family of ordinary source moments $G(B,\Lambda,h)$:

$$\mathcal E\ll U^{1+\epsilon}\quad\text{whenever }m_1+m_2+\Lambda s\le B,\ 0\le s\le h\qquad\text{(sources.tex G1, feedback.tex NF1)}.$$

Each face is derived from an earlier LOW parent and an earlier HIGH parent
through the gates NF8–NF13. The HIGH gate (NF11–NF12; Lean
`Record1252270103Finite.densityGate`) is

$$H_\nu+\mathcal G(S,F_p)>f,\qquad H_\nu=1-\rho_\nu-\nu T-a(5-6\rho_\nu),\qquad \nu\in[q,3/4].$$

Here $\mathcal G$ is the gain of the same-zero detector count of HIGH rows
(feedback.tex HF2–HF10). In that count the inverse witness uses the child's
marked slots **at most once each**:

$$z_I=\min\Bigl(S,\frac{Q-r}{2}\Bigr)\qquad\text{(LD, HF3; Lean \texttt{inverseThreshold}, \texttt{fiber\_exponent}, \texttt{inverse\_fiber\_count})}.$$

At every converged face the binding facet is "available slots / available
slots", with gain $\varphi S$. At the pivot the inverse capacity
$(Q-r)/2\approx0.10$ is more than twice the available marked width
$S\approx0.042$, so the capacity is under-used.

## 2. The analytic input: repeated prime lists

PR #69 foundations.tex, **Lemma 8.1 (overlap adapter for the inverse moment)**:

> The estimate of Theorem 7.3 remains valid for a fixed finite number of
> possibly overlapping or repeated prime lists with the same bounded annular
> coefficients. Both admission inequalities may use the full sum of the
> original slot widths.

The proof colours the union of the lists randomly with $K$ colours. Distinct
tuples receive their prescribed colours with probability $K^{-K}$, so the
product is $K^K$ times an average of products on disjoint coloured lists. Blocks
of equal primes have central mass $\ll1$ and are frozen before the row norm.

In Lean this is
`Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.overlapping_inverse_marked_energy`.
It takes arbitrary lists `L : ι → Finset (Ideal O)` with no disjointness
hypothesis, and admits the energy when $r+2\sum_i\ell_i<1$ and
$2r+8\sum_i\ell_i<3$, with widths counted with multiplicity.

**Lemma A (doubled-mark inverse gate).** Take a HIGH row fiber at density
$\nu$, with available marked width $S$ and slot amplitudes of mean class
$p\in[0,1/2]$. For every $z\in[0,2S]$ with $r+2z<Q-c_1$ and $2r+8z<3Q-c_2$,

$$\#\text{fiber}\ll U^{\,Q-\nu r-2\nu p z+\text{loss}}.$$

*Proof.* Order the slots by amplitude bin and give each a multiplicity
$k_i\in\{0,1,2\}$ greedily, filling width $z$ up to one mesh slot. The selected
multiset has mean amplitude at least the overall mean, so its product satisfies
$|\prod Q_i^{k_i}|^2\ge U^{2\nu pz-\text{mesh}}$. Apply the overlap adapter to
the lists $L_{(i,c)}=L_i$ for $c\le k_i$, then Markov's inequality, as in the
one-copy `inverse_fiber_count`. $\square$

## 3. Amplitude classes get their own detector cutoff

PR #69 passes from $p=1/2$ to general $p$ through
$2pz+(1-2p)S\ge z$ for $z\le S$ (Lean `amplitude_credit`). This fails when
$z>S$. The fix uses a freedom the detector already has: its cutoff is chosen per
row class before any witness is taken (paper Prop. 4510; in Lean the witnesses
are hypotheses of `feedback_fiber_count`). An amplitude bin is such a class.

Put $w=5-6\nu$, $\xi_0=10/(3(5-2\nu))$, and let $(B_H,\Lambda_H,h_H)$ be the HIGH
parent. For $p\in[0,1/2]$ define the inverse and plain thresholds

$$I_p(\xi)=\max\Bigl(\xi-4pS,\ \frac{\xi-pQ}{1-p}\Bigr),\qquad
P_p(\xi)=\max\Bigl(\xi-2pS,\ \xi-2ph_HQ,\ \frac{\xi-2pB_HQ/\Lambda_H}{1-2p/\Lambda_H}\Bigr).$$

Let $\xi_p$ be the root of $6\nu\xi+w\,(I_p(\xi)+P_p(\xi)/2)=5Q$. Set

$$f_p(S,Q)=(1-2p)\nu S+\nu(\xi_p-\xi_0Q),\qquad \mathcal G_2(S,Q)=\min_{0\le p\le1/2}f_p(S,Q).$$

Each $f_p$ is a minimum of six affine forms in $(S,Q)$, one for each
inverse/plain branch pair.

**Lemma B (weighted mass of an amplitude class).** In class $p$, use the cutoff
$t_p=I_p(\xi_p)+P_p(\xi_p)/2$. Then

$$E_p+2\nu pS\le Q+2\nu pS-\nu\xi_p=\rho Q+\nu S-f_p(S,Q)\le\rho Q+\nu S-\mathcal G_2(S,Q).$$

*Proof.* At $\xi=\xi_p$ the cutoff equation holds with equality, which pays the
long branch: for $r>Q$, $E\le(1+5t_p)/6-\nu t_p=Q-\nu\xi_p$. The same-zero
alternative (Lean `same_zero_alternative`) gives either
$r\ge I_p(\xi_p)-\epsilon$ or $2m\ge P_p(\xi_p)$.

- Inverse case: take $z=\min(2S,(Q-r)/2)$. Then $r+2pz\ge\xi_p$, and Lemma A
  gives $E\le Q-\nu\xi_p$.
- Plain case: take $z_P=\min(S,h_HQ,(B_HQ-2m)/\Lambda_H)$ with PR #69's plain
  gate.

The cutoff is admissible: $t_p=(5Q-6\nu\xi_p)/w\in[Q,\tfrac{15}{15-6\nu}Q]$
because $\xi_0Q\le\xi_p\le Q$. $\square$

At $p=1/2$ the facets are those of HF6 with $2S$ in the inverse "available
slots" branch. With $k$ copies the leading facet is $(2k+1)\varphi S/3$.

| inverse branch | plain branch | gain at $p=1/2$ |
|---|---|---|
| doubled slots | slots | $\tfrac53\varphi S$ |
| doubled slots | parent width cap | $\tfrac43\varphi S+\tfrac{\varphi h}{3}Q$ |
| doubled slots | parent affine cap | $\dfrac{4\nu w(\Lambda-1)}{D_{13}}S+\dfrac{\nu w(Bt_\nu-10)}{t_\nu D_{13}}Q$ |
| inverse cap | any | unchanged from PR #69 |

Where the faces are used, $\mathcal G_2=f_{1/2}$ except in a small corner,
$\nu<0.53$ and $S/Q>0.058$. There an amplitude $p\in(0.4915,1/2)$ is worse,
by less than $10^{-5}$. The certificate uses the full minimum over $p$.

## 4. Side conditions

- **(C1) Common-width payment** (LD14a / HF12; Lean `common_gain_reserve`).
  We need
  $\mathcal G(S,F)-\mathcal G(L,Q)-\nu(c+d)\le-(c+d)/12$ whenever
  $S\le L+\delta$ and $F\le Q+2\delta$, with $\delta=c+d$. Take class $p$ at
  actual widths $(L,Q)$; it is enough that
  $f_p(L,Q)+(\nu-\tfrac1{12})\delta\ge\mathcal G_2(S,F)$. This follows from two
  facts, each certified per node:
  - **(i)** For $p\in[9/20,1/2]$, every branch slope satisfies
    $a+2b\le\nu-1/12$, and every branch has $a,b\ge0$.
  - **(ii)** For $p\in[0,9/20]$, $\nu\in[q,3/4]$ and $L/Q\in[0,1/4]$,
    $f_p\ge f_{1/2}$.

  If $p\ge9/20$, use (i) and monotonicity. If $p<9/20$, use (ii) and then (i)
  at $p=1/2$. Numerically, slopes exceed $\nu-1/12$ only for $p\le0.405$, and
  $f_p<f_{1/2}$ only for $p\ge0.4915$.

  HF12's crude bound $\varphi+2C_{\max}$ must be replaced by this facet-wise
  bound, because $\tfrac53\varphi+2C_{\max}>\nu$ near $\nu=1/2$.
- **(C2) Root completion** (HF11–HF14).
  - The row-width coefficients do not involve the doubled branch, so each is
    still at most $C_{\max}$.
  - $\mathcal G_2\le f_{1/2}\le C_{\max}Q$.
  - So HF13 and HF14 apply verbatim.
- **(C3) Inverse admissions.** $z\le(Q-r)/2$ and $r>Q/2$ give
  $2r+8z\le4Q-2r<3Q$.
- **(C4) HF1 floor.** Every HIGH parent used has
  $B\ge0.95704>22/23$.

## 5. The new source graph (`cchain_k2.json`)

- **Premise.** The graph starts from the natural premise
  $G(1,\tfrac{11243277}{2500000},\tfrac{11}{200})$, which PR #69 proves from its
  intermediate bound $\theta_I=0.8747759$ (NF2).
- **Nodes.** There are 59 derived faces. Their pivots are
  $b_\times=0.0135,0.0140,\dots,0.0420,0.04232$ and their caps are
  $h=\min(0.0549989,\,b_\times+0.016)$. Each face uses the previous face as
  both LOW and HIGH parent, under the schedule
  $(e,r,f)=(10^{-12},10^{-8},10^{-7})$.
- **Rational parameters.** $B$, $\Lambda$ and $q$ are given to 13 decimals.
  They were built with a floating-point reserve of $5\cdot10^{-8}$ on every
  gate, then certified exactly.
- **Exact checks per node** (`cert_chain.py`):
  - NF8 and the HF1 parent domain;
  - all 16 NF10 scalar gates and the weak guard, at $b_\times$ and $h$;
  - the three NF13 special sectors, by 1-D Bernstein on $[q,3/4]$;
  - the doubled-mark HIGH gate, for every branch pair, by 2-D Bernstein on
    $(\nu,p)\in[q,3/4]\times[0,1/2]$ with subdivision;
  - (C1)(i), and (C1)(ii) by 3-D Bernstein covers.
- **Gate model.** The model behind the construction (`ss_fb.py`) accepts all
  221 printed nodes of PR #69 with reserves of $5\cdot10^{-10}$ to $10^{-8}$
  (`check_hailey.py`).

| face | node | pivot | $B$ | $\Lambda$ | height at $s=0.0423245$ |
|---|---|---|---|---|---|
| PR #69 C | `alt_focused_g6_C` | 0.04232 | 0.962261518 | 3.148131764 | 0.829018 |
| **new C** | 58 | 0.04232 | 0.9565707676 | 2.9576608857 | **0.831389** |
| PR #69 P | `alt_focused_g7_P` | 0.03960 | 0.967390311 | 3.273079954 | 0.837776 at 0.0396 |
| **new P** | 52 | 0.0395 | 0.9629080170 | 3.1118536669 | **0.839679** at 0.0396 |

## 6. The final return

The return is PR #69's first-return FR4–FR22 and return NR1–NR14, with the new
faces C (same-zero count) and P (physical numerator). Everything else is
unchanged:

- the count candidates: the natural count, the affine and capped branches of C
  and P, and the weaker faces $B-j/4000$;
- the FR8 admission polynomials on upward windows;
- the six conductor edges;
- $s_P=1/25$, $r_0=10^{-9}$ and $\theta_I=0.8747759$.

The parameters are

$$\theta=\frac{8747514}{10^7},\qquad h=\frac{79987}{10^5},\qquad t_f=\frac1{360}.$$

**The free-shift cutoff $t_f$.** It changes from $1/400$ to $1/360$. The
flatter P face makes FR21's sufficient reserve
$(\tfrac7{18}-\tfrac1{500})t_f+\tfrac{1-B_P}{18}+(\tfrac{\Lambda_P}{18}-\tfrac14)s_P$
negative at $t_f=1/400$. $t_f$ is a free choice in PR #69: FR18–FR20 need only
the domain guards for $0\le t\le t_f$, and those are re-checked:

- physical plain upper: $0.018$;
- physical width lower: $0.0042$;
- small-width shortening: $0.003$.

**Certificate.**
- The cover is 64 closed rectangles over the six edges.
- The minimum return Bernstein coefficient is about $1.3\cdot10^{-8}$; the
  minimum admission coefficient is about $1.6\cdot10^{-5}$.
- All 34 domain and complementary reserves are positive. The smallest are:
  - conductor kink before top: $5.3\cdot10^{-6}$;
  - incumbent $2(\theta_I-\theta)$: $4.9\cdot10^{-5}$;
  - large shift: $5.0\cdot10^{-5}$;
  - short plain shortening: $7.8\cdot10^{-4}$.
- $\theta=0.87475139$ does not certify, so $0.8747514$ is optimal for these
  faces.

## 7. What remains for admission to the tracker

The tracker admits Lean proofs checked by Lean, NanoDa and con-ron against the
canonical statement. The changes are confined to:

1. **`Record1252270103Source/High`.**
   - A doubled-mark selection (`select_common_product` with multiplicity at
     most 2) and `inverse_fiber_count`, both fed by
     `overlapping_inverse_marked_energy`.
   - A per-amplitude `fiber_exponent`.
   - The facets and slopes of $\mathcal G_2$, and the (C1) payment replacing
     `common_gain_reserve`.
2. **`Record1252270103Finite`.** A `SourceValid` predicate whose HIGH check is
   two-dimensional in $(\nu,p)$, plus the 59 node certificates and the
   (C1)(ii) covers.
3. **`Record1252270103Return`.** The new faces, $t_f$, $\theta$ and the 64
   rectangles.

The analytic input, `overlapping_inverse_marked_energy`, is already proved.

## Reproducing

```
python3 test_return69.py              # return certifier reproduces PR #69 Certificate B
python3 check_hailey.py               # gate model accepts all 221 PR #69 nodes
python3 certify_all.py cchain_k2.json # full exact certificate -> certificate_doubled_marks.json
```

Other files:

- `gain_k.py`, `rep_gain.py`: the amplitude-resolved HIGH gain with $k$ copies.
- `cchain.py`: builds the rational chain.
- `build_chain*.py`, `chainp_k*.json`: floating-point chain construction.
- `lip_p.py`: the (C1) slope check.
- `model69.py`, `price_faces.py`, `pick_theta*.py`: the return model used to
  choose $(\theta,h)$.
