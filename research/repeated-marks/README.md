# Repeated marks with a capped gain in the source HIGH count

**Result.** Every Dirichlet $L$-function is nonvanishing on

$$\Re s>\theta=\frac{8747289}{10^7}=0.8747289,$$

excluding the principal pole. This is $4.40\cdot10^{-5}$ below the record
$0.874772906$ (PR #70) and $2.25\cdot10^{-5}$ below the doubled-mark result
$0.8747514$ (`../doubled-marks`).

**Status.**
- The mathematical argument is complete (§§2–6).
- Exact rational certificates, built from Bernstein expansions over
  $\mathbb Q$ with no floating point, cover:
  - the new 59-face source graph;
  - the final return, which certifies at $\theta=0.8747289$ but fails at
    $0.87472887$.

  They are in `certificate_repeated_marks.json`, produced by
  `certify_all_k.py`.
- The return certifier reproduces PR #69's own final certificate exactly
  (`test_return69.py`).
- Not yet done: the Lean formalization (§10).

This note supersedes `../doubled-marks/README.md`, which used each marked slot
at most twice. Three things change, and everything else in PR #69 is reused
unchanged:
- **Source step.** Each slot may be used up to $K$ times, with one detector
  cutoff per amplitude class.
- **Common-width payment.** A general lemma (Lemma C) replaces PR #69's slope
  check HF12 and its 1/12 slack, which is never used.
- **Return.** The physical face is applied through its global source theorem
  instead of a conservative window (Lemma D).

## 1. Where the change is

PR #69 proves a finite family of ordinary source moments $G(B,\Lambda,h)$
(sources.tex G1, feedback.tex NF1). Each new face comes from an earlier LOW
parent and an earlier HIGH parent through the gates NF8–NF13. The HIGH gate is

$$H_\nu+\mathcal G(S,F_p)>f,\qquad H_\nu=1-\rho_\nu-\nu T-a(5-6\rho_\nu),\qquad \nu\in[q,3/4]$$

(feedback.tex HF15/NF11–NF12). Here $\mathcal G$ is the gain of the same-zero
detector count of HIGH rows. In PR #69 the inverse witness of that count uses
each child marked slot at most once (feedback.tex HF3):

$$z_I=\min\Bigl(S,\frac{Q-r}{2}\Bigr).$$

At the late faces of the graph the binding facet is "available slots", with
$S\approx0.04$. The inverse capacity $(Q-r)/2\approx0.10$ is not reached.

## 2. Lemma A$_K$: repeating marked slots

**Input.** PR #69, foundations.tex Lemma 8.1 (overlap adapter): Theorem 7.3
(marked inverse moment) holds for a fixed finite number of possibly
overlapping or **repeated** prime lists with the same bounded annular
coefficients. Both admissions use the full sum of the slot widths.

In Lean this is `overlapping_annular_inverse_marked_energy`
(`Record12518109Gain/Upstream/DeletionInverseOverlap.lean`), reached from the
HIGH inverse field through `actual_free_inverse_energy`. PR #69 already routes
the HIGH count through it, because canonical pools may overlap. It never
repeats a slot.

**Lemma A$_K$.** Fix an integer $K\ge1$. Take a HIGH row fiber at density
$\nu$, with available marked width $S$, slot amplitudes of mean class
$p\in[0,1/2]$, and inverse witness length $r$. Let $z\in[0,KS]$ satisfy

$$r+2z<Q-c_1,\qquad 2r+8z<3Q-c_2.$$

Then $\#\text{fiber}\ll U^{\,Q-\nu r-2\nu pz+\text{loss}}$.

*Proof.*
1. Order the slots by amplitude bin, highest first.
2. Give the first slots multiplicity $K$ until the width $\sum_ik_i\ell_i$
   reaches $z$. One slot gets an intermediate multiplicity, which overshoots by
   at most one mesh slot.
3. The selected multiset consists of the highest slots, so its length-weighted
   mean amplitude is at least $p$. Hence
   $|\prod_iQ_i^{k_i}|^2\ge U^{2\nu pz-\text{mesh}}$.
4. Apply the overlap adapter to the at most $K\cdot\#\text{slots}$ lists
   $L_{(i,c)}=L_i$, $c\le k_i$, with widths counted with multiplicity.
5. Finish with Markov's inequality, as in the one-copy `inverse_fiber_count`.
$\square$

## 3. Lemma B$_K$: one detector cutoff per amplitude class

PR #69 passes from $p=1/2$ to general $p$ by $2pz+(1-2p)S\ge z$ for $z\le S$
(Lean `amplitude_credit`). That inequality fails for $z>S$. The detector cutoff
$t\in[1,3/2]$ is chosen per row class before any witness is taken:
- paper Prop. "Two saturated witnesses";
- PR #69 foundations Lemma 14.2;
- in Lean, the witnesses of `weighted_row_sum` are already indexed by amplitude
  bin (`binCutoff`), and PR #67 used a $p$-dependent `binCutoff`.

An amplitude bin is such a class.

**Definitions.** Put $w=5-6\nu$, $\xi_0=10/(15-6\nu)$, $\rho=1-\nu\xi_0$, and
let $(B_H,\Lambda_H,h_H)$ be the HIGH parent. For $p\in[0,1/2]$ define

$$I^K_p(\xi)=\max\Bigl(\xi-2pKS,\ \frac{\xi-pQ}{1-p}\Bigr),\qquad
P_p(\xi)=\max\Bigl(\xi-2pS,\ \xi-2ph_HQ,\ \frac{\xi-2pB_HQ/\Lambda_H}{1-2p/\Lambda_H}\Bigr).$$

Let $\xi^K_p$ be the root of $6\nu\xi+w\,(I^K_p(\xi)+P_p(\xi)/2)=5Q$. Set

$$f^K_p(S,Q)=(1-2p)\nu S+\nu(\xi^K_p-\xi_0Q).$$

Each $f^K_p$ is the minimum of six forms $A\,S+B\,Q$, one for each
inverse/plain branch pair. Their coefficients depend only on $(\nu,p)$ and the
HIGH parent.

**Lemma B$_K$.** In amplitude class $p$, use the cutoff
$t_p=I^K_p(\xi^K_p)+P_p(\xi^K_p)/2$. Then the weighted class mass satisfies

$$E_p+2\nu pS\le\rho Q+\nu S-f^K_p(S,Q).$$

*Proof.* At $\xi=\xi^K_p$ the cutoff equation holds with equality.
- **Long branch.** For $r>Q$ the sixth-power count gives
  $(Q+5t_p)/6-\nu t_p=Q-\nu\xi^K_p$.
- **Inverse branch.** If $r\ge I^K_p(\xi^K_p)$, take $z=\min(KS,(Q-r)/2)$.
  Then $r+2pz\ge\xi^K_p$, and Lemma A$_K$ applies.
- **Plain branch.** Otherwise $2m\ge P_p(\xi^K_p)$. Use PR #69's plain witness
  $z_P=\min(S,h_HQ,(B_HQ-2m)/\Lambda_H)$, which is unchanged.

The cases that PR #69's `fiber_exponent` also handles carry over:
- **Admissible cutoff.** $t_p=(5Q-6\nu\xi^K_p)/w\in[Q,15Q/(15-6\nu)]$, because
  $\xi_0Q\le\xi^K_p\le Q$.
- **Second inverse admission.** On the inverse branch,
  $I^K_p(\xi)\ge2\xi-Q$ (indeed
  $I^K_p(\xi)-(2\xi-Q)\ge(Q-\xi)(1-2p)/(1-p)\ge0$). So $r\ge2Q/3$, and
  $2r+8z\le4Q-2r\le8Q/3<3Q$.
- **Plain fallback.** When $2m>B_HQ$ we need $\xi^K_p\le B_HQ$. The left side
  of the cutoff equation dominates its inverse-cap/affine-cap branch, and that
  branch at $\xi=B_HQ$ is at least $6\nu B_H+w(5B_H/2-1)\ge5$ when
  $B_H\ge22/23$.
- **Erosion and clamping.** The erosion case $z\le\zeta$ is as in PR #69.
  Labels above $\delta/2$ are clamped to $p=1/2$; those fibers are empty.

$\square$

## 4. Lemma C: the payment for a capped gain

The gain enters PR #69's later steps only through three properties
(`gainAt_common_reserve`, `gainAt_weighted_width_mono`/`weighted_exponent_mono`,
and the root-completion bounds):

- **(P1) Common-width payment** (sources.tex LD14a, feedback.tex HF12). If
  $S\le L+\delta$ and $F\le Q+2\delta$, then
  $\mathcal G(S,F)-\mathcal G(L,Q)-\nu\delta\le0$.
  - sources.tex says this makes the residual HIGH common excess "individually
    nonpositive".
  - PR #69 states it with an extra $-\delta/12$, but no later step uses that
    term. In Lean, `modified_selected_sector_singleton_payment`
    (`High/GlobalPhysicalSectorPayment.lean`) discards
    $-(c+d+\mathrm{forced})/12$ with `linarith`, since it is $\le0$.
- **(P2) Width monotonicity.** $\nu S-\mathcal G(S,Q)$ is nondecreasing in $S$.
- **(P3) Root completion.** Every row coefficient of $\mathcal G$ is at most
  $C_{\max}=\nu(1-\xi_0)$, and $\mathcal G\le C_{\max}Q$ (HF11–HF14).

**Lemma C.** Let $\mathcal G(S,F)=\min_{j\in J}(A_jS+B_jF)$ for a family of
forms with $A_j,B_j\ge0$, and suppose $\mathcal G(S,F)\le\nu S$. Then for all
$S,F,L,Q,\delta\ge0$ with

$$2S\le F,\qquad S\le L+\delta,\qquad F\le Q+2\delta,$$

we have

$$\mathcal G(S,F)\le\mathcal G(L,Q)+\nu\delta.$$

Every source cell satisfies $2S\le F$, since $S\le0.055$ and $F_p\ge0.9$. So
(P1) holds. Only the cell needs $2S\le F$; the actual widths $(L,Q)$ are
arbitrary.

(P2) holds for all $(S,Q)$ with no condition. Take a facet $j$ that attains
$\mathcal G(S,Q)$ with $S>0$. Then $A_j\le\nu$, because otherwise
$A_jS+B_jQ>\nu S\ge\mathcal G(S,Q)$. Hence
$\mathcal G(L,Q)\le A_jL+B_jQ=\mathcal G(S,Q)+A_j(L-S)\le\mathcal G(S,Q)+\nu(L-S)$
for $L\ge S$. At $S=0$ use $\mathcal G(0,Q)=0$ and $\mathcal G(L,Q)\le\nu L$.

*Proof.* Fix $j$.
- **If $\delta\ge S$:**
  $A_jL+B_jQ+\nu\delta\ge\nu\delta\ge\nu S\ge\mathcal G(S,F)$.
- **If $\delta<S$:** then $F-2\delta>0$. By monotonicity,
  $A_jL+B_jQ+\nu\delta\ge A_jS+B_jF-(A_j+2B_j-\nu)\delta$. The right side is
  affine in $\delta\in[0,S]$, so it is at least the smaller of its two
  endpoint values:
  - at $\delta=0$: $A_jS+B_jF$;
  - at $\delta=S$: $B_j(F-2S)+\nu S\ge\nu S$, using $2S\le F$.

  Both values are at least $\mathcal G(S,F)$.

Minimize over $j$. The case $F<2S$ really is excluded: there the bound at
$\delta=F/2$ can drop below both $A_jS+B_jF$ and $\nu S$. $\square$

The lemma is formalized in Lean 4 with Mathlib (`lean/LemmaC.lean`:
`RepeatedMarks.facet_payment`, `RepeatedMarks.lemmaC`).

`lean/RepeatedGain.lean` (Mathlib only, 31 theorems) formalizes:
- the per-class thresholds, branches and roots, and the identity $f_0=\nu S$;
- the facet linearity and the coefficient bounds $A,B\ge0$, $B\le C_{\max}$;
- $\mathcal G_K=\inf_pf_p$ and its basic bounds;
- Lemma C for $\mathcal G_K$ (`gainK_payment`), width monotonicity
  (`gainK_width_mono`) and homogeneity (`gainP_smul`).

`lean/Bernstein2.lean` (Mathlib only) gives the finite-check infrastructure
for the 2-D HIGH gate:
- bicubic Bernstein positivity on a box (`bicubic_pos`), through a fixed
  polynomial identity;
- a computable rational checker `checkBox` over bisection trees, with
  soundness `checkBox_sound`. Certificates run under `decide +kernel`.

The gate numerators have bidegree at most $(3,3)$ in $(\nu,p)$.

For comparison, PR #69's HF12 bounds the loss by Lipschitz constants. It needs
every facet to satisfy $A_j+2B_j\le\nu$; for PR #69's gain this is
$\varphi_\nu+2C_{\max}\le\nu$, where $C_{\max}=\varphi_\nu/3$ exactly. It also
records a $1/12$ margin. That slope condition fails as soon as a slot is
repeated. Lemma C needs no slope condition at all: monotone facets and the
bound $\mathcal G\le\nu S$ suffice.

## 5. The new gain

$$\boxed{\ \mathcal G'_K(S,F)=\min\Bigl(\nu S,\ \min_{0\le p\le1/2}f^K_p(S,F)\Bigr)=\min_{0\le p\le1/2}f^K_p(S,F)\ }$$

**The cap is automatic.** At $p=0$ every inverse and plain threshold equals
$\xi$, so the root is $\xi_0Q$ and $f^K_0(S,Q)=\nu S$ for every branch pair. So
$\min_pf^K_p\le\nu S$ always, and the amplitude class $p=0$ supplies the facet
$\nu S$ that Lemma C needs. The same holds for $K=2$. The doubled-mark gain
therefore satisfies the common-width payment through Lemma C alone, without the
per-node checks (C1)(i)–(ii) of `../doubled-marks`. PR #69's uniform-cutoff
gain has no such class, which is why it needed HF12.

**Theorem.** For every fixed $K\ge1$, $\mathcal G'_K$ can replace the HIGH gain
in PR #69's source step. Its properties:
1. **Validity.** $\mathcal G'_K\le f^K_p$ for every class $p$, so Lemma B$_K$
   gives the class mass bound with $\mathcal G'_K$ at the actual widths.
2. **(P1) and (P2).** Every branch form has $A,B\ge0$:
   - $\partial_S$ of every root is $\ge0$, and $(1-2p)\nu\ge0$.
   - The root at $S=0$ is at least $\xi_0Q$, because each branch's left side at
     $\xi=\xi_0Q$ is at most $5Q$.
   - The extra form $\nu S$ has $A=\nu$, $B=0$.

   Lemma C then applies.
3. **(P3).** At $S=0$ and $\xi=Q$, each branch's left side is at least
   $6\nu Q+w(Q+(1-2ph_H)Q/2)\ge5Q$. So each normalized root is at most $1$, and
   each $B\le\nu(1-\xi_0)=C_{\max}$. The form $\nu S$ has $B=0$.
   $\mathcal G'_K\le C_{\max}Q$ follows from the slot-free inverse-cap branches.
   HF13–HF14 then apply verbatim.

At $p=1/2$ and $K=2$ the facets are those of `../doubled-marks`. As
$K\to\infty$ the slot branch $\xi-2pKS$ disappears, and only the inverse cap
$(Q-r)/2$ limits the inverse witness. In the chain below, $K=5$ already gives
the same faces as $K=8$.

## 6. The return: the physical face covers every shift

With the new faces, PR #69's final return no longer binds where it used to. It
binds on conservative guards that come from the old natural moment, with
coefficient $9/2$:
- **FR19.** Shortenings below the windows $2/5\le m\le11/25$ and
  $17/500\le s\le43/1000$.
- **FR21.** Shifts $t\ge t_f$.
- **Lean.** The bound $1-y/d_++t_f<264/625$ and the shift bound
  $2y/d_s-1\le9/50$ (`PhysicalSchedule`).

With PR #69's guards unchanged, the new faces gain almost nothing, because the
flatter $P$ face forces a larger $t_f$, and that collides with the plain upper
bound.

These guards exist only because the return applies the physical face on a
window. PR #69 return.tex §1: "Keep the conservative local domains … Both are
strictly below their proved global caps." The face itself is a global source
theorem. In Lean, `globalFace B Λ cap = ⟨B,Λ,0,B,0,cap⟩` has plain floor 0 and
width floor 0, so it is downward closed.

**Lemma D (shifts and shortenings through the global physical face).**
Let $P=G(B_P,\Lambda_P,h_P)$ and fix $s_P\le h_P$. For $d\in[d_s,d_+]$ put
$n_0=1-y/d$. For every shift $t\ge0$ put

$$z(t)=\max\Bigl(0,\min\Bigl(s_P,\frac{B_P-2n_0-2t}{\Lambda_P}\Bigr)\Bigr).$$

1. **Admissibility.**
   - If $2(n_0+t)\le B_P$, the shifted numerator configuration
     $(n_0+t,n_0+t,z)$ lies in the domain of $P$ for every $0\le z\le z(t)$.
   - If $B_P<2(n_0+t)\le1$, the configuration with $z=0$ lies in the natural
     moment.
   - If $2(n_0+t)>1$, PR #69's clipped branch (FR22) applies unchanged.
2. **Width loss.** $z(0)-z(t)\le2t/\Lambda_P$ for all $t\ge0$:
   - on the capped part there is no loss;
   - on the affine part the slope is $2/\Lambda_P$;
   - where $z(t)=0$, we have $2t\ge B_P-2n_0\ge\Lambda_Pz(0)$.
3. **Payment.** For $q=\delta p\le\delta/2$ and all $t\ge0$,
   $\frac{\delta t}2-\frac q2\{z(0)-z(t)\}\ge\delta t\bigl(\tfrac12-\tfrac1{2\Lambda_P}\bigr)\ge\frac{\delta t}{500}$.

So FR19, FR21, the cutoff $t_f$, and the numerator windows are not needed. The
return keeps:
- `small_shift_cost` / `large_shift_clipped`:
  $\tfrac12-\tfrac1{500}-\tfrac1{2\Lambda_P}>0$;
- $s_P\le h_P$;
- every other complementary receipt of PR #69.

**Count caps.** The same remark applies to the constant-width cap $s_+$ of the
count face $C$. PR #69 uses $11/250$, but the face is proved up to
$h_C=0.0549989$. We use $s_+=13/250$. The FR8 admission tests are unchanged
and are rechecked with the new value.

## 7. Effect of each step

These are float-model values of the final return, for the same certification
pipeline:

| step | source gain | return | θ (model) |
|---|---|---|---|
| PR #70 (record) | PR #69 ($z_I\le S$) | PR #69 | 0.874772906 |
| `../doubled-marks` (certified) | $K=2$, slack 1/12 | PR #69, $t_f=1/360$ | 0.8747514 |
| this note: gain only | $\mathcal G'_K$, $K=8$ | PR #69 guards | ≈ 0.874753 (no gain) |
| this note (certified) | $\mathcal G'_K$, $K=8$ | Lemma D, $s_+=13/250$, $s_P=9/200$, $h=401/500$ | **0.8747289** |

The new faces are flatter (Λ_C ≈ 2.897, Λ_P ≈ 3.038). With PR #69's guards
unchanged they gain almost nothing: FR21 needs $t_f\ge0.0029$, and the Lean plain
bound $264/625$ then forces $h\approx0.8$. Lemma D removes both guards. After
that, only the conductor edge $N_+$ binds, at $\delta\approx0.453$, $p=1/2$.

## 8. Independent review

An adversarial review of `../doubled-marks` returned *sound with fixes*. It
found no fatal flaw: repeating a slot is covered by the overlap adapter, and the
cutoff may depend on the amplitude bin. Its points and how this note settles
them:

1. (C1)(ii) was certified only for $L/Q\le1/4$. **Settled by Lemma C**, which
   holds for all $L,Q,\delta\ge0$.
2. (C1)(i) held only for $\nu\ge q$, not on $[1/2,3/4]$. **Settled by Lemma C**,
   which needs no slope condition.
3. Two more users of the gain need S-slope $\le\nu$ (`weighted_exponent_mono`,
   `gainAt_weighted_width_mono`). **Settled by Lemma C**: $\mathcal G'_K$ is
   $\nu$-Lipschitz in $S$.
4. The (C2) argument was wrong for $p<1/2$. **Corrected in §5(3).**
5. Lemma B omitted some cases (the $\xi_p\le B_HQ$ fallback, erosion, clamped
   bins). **Now in §3.**
6. The Lean scope was understated. See §10.
7. PR #69 already routes the HIGH inverse field through the overlap adapter, so
   the earlier wording was wrong. It never *repeats* a slot. **Corrected in §2.**

## 9. The source graph and the certificates

**Graph** (`cchain_k8b.json`, built by `cchain_k.py`).
- **Premise.** The natural premise $G(1,\tfrac{11243277}{2500000},\tfrac{11}{200})$,
  as in PR #69.
- **Nodes.** 59 derived faces, with pivots $0.0135,0.0140,\dots,0.0420,0.04232$
  and caps $\min(0.0549989,b_\times+0.016)$. Each face uses the previous face
  as both LOW and HIGH parent, under the schedule
  $(e,r,f)=(10^{-12},10^{-8},10^{-7})$.
- **Gain.** $\mathcal G'_8$, evaluated on a $p$-grid with step
  $\le0.005$ (0.001 on $[0.4,0.5]$).
- **Rational parameters.** $B,\Lambda,q$ are given to 13 decimals.

**Exact chain checks** (`cert_chain_k.py`, per node):
- NF8 and the parent domain;
- the 16 NF10 scalar gates and the weak guard, at $b_\times$ and $h$;
- the NF13 special sectors;
- the HIGH gate for every branch pair, by 2-D Bernstein on
  $(\nu,p)\in[q,3/4]\times[0,1/2]$, together with the facet $\nu S$;
- for Lemma C and (P3), on the same box: $A\ge0$, $B\ge0$ and
  $B\le C_{\max}$ for every branch form.

| face | node | pivot | $B$ | $\Lambda$ | $q$ | height at $0.0423245$ / $0.0396$ |
|---|---|---|---|---|---|---|
| PR #69 C | `alt_focused_g6_C` | 0.04232 | 0.962261518 | 3.148131764 | 0.545 | 0.829018 |
| doubled C | 58 | 0.04232 | 0.9565707676 | 2.9576608857 | 0.516 | 0.831389 |
| **new C** | 58 | 0.04232 | 0.9560923432 | 2.8966178971 | 0.505 | **0.833494** |
| PR #69 P | `alt_focused_g7_P` | 0.03960 | 0.967390311 | 3.273079954 | 0.564 | 0.837776 |
| doubled P | 52 | 0.0395 | 0.9629080170 | 3.1118536669 | 0.539 | 0.839679 |
| **new P** | 52 | 0.0395 | 0.9618940092 | 3.0377206507 | 0.527 | **0.841600** |

**Return** (`cert_return.py`, global mode):
- **Parameters.** $\theta=8747289/10^7$, $h=401/500$, $s_+(C)=13/250$,
  $s_+(P)=43/1000$, $s_P=9/200$, $r_0=10^{-9}$, $\theta_I=0.8747759$.
- **Cover.** 36 closed rectangles over the six conductor edges.
  - Minimum return Bernstein coefficient: $2.49\cdot10^{-8}$.
  - Minimum FR8 admission coefficient: $1.25\cdot10^{-3}$.
- **Receipts.** All 31 remaining scalar receipts are positive. The smallest
  are:
  - principal contour $z$: $8.7\cdot10^{-5}$;
  - incumbent $2(\theta_I-\theta)$: $9.4\cdot10^{-5}$;
  - $h_C-s_+$: $3.0\cdot10^{-3}$.
- **Binding point.** Only the top conductor edge $N_+$ binds, at
  $\delta\approx0.4539$, $p=1/2$.

**Search over parameters** (float model `return_opt.py`, `theta_of.py`):
- **Caps.** $s_+(C)=13/250$ versus $27/500$, and $s_P=9/200$ versus $1/20$, give
  the same $\theta$.
- **Density below 1/2.** Extending the HIGH density below $1/2$ lets the C
  pivot move to $0.0455$, but gains only $5\cdot10^{-7}$.
- **Older HIGH parents and smaller caps.** These gain less than
  $10^{-6}$.
- **HIGH amplifier cost.** Removing $a(5-6\rho)$ from the HIGH gate entirely
  (hypothetically) moves the faces by $5\cdot10^{-5}$ only. The pivot gate,
  inverse capacity against the parent's affine face, is what binds.

## 10. What remains for admission to the tracker

The tracker admits Lean proofs checked by Lean, NanoDa and con-ron. A
dependency map of Hailey Collet's formalization shows that the HIGH gain is
hard-coded by name (`High.gain`, `ActualGaps`, `SourceValid`) from
`feedback_fiber_count` up to `nf_step`. A fork therefore retypes about 75 files
(about 10k lines), mostly renaming. The genuinely new Lean is:

1. **Repeated-mark inverse count.** A $K$-fold selection, and
   `inverse_fiber_count` through `overlapping_annular_inverse_marked_energy`,
   which already accepts overlapping lists.
2. **Per-bin cutoffs.** `binCutoff` already indexes witnesses by amplitude bin;
   it must use the bin's $p$. `MaxWeighted` must supply one witness per
   cutoff.
3. **The gain.** $\mathcal G_K$ and Lemma C in place of
   `common_gain_reserve` and `root_reserves`'s first component.
4. **The finite check.** `SourceValid` with a 2-D $(\nu,p)$ Bernstein check,
   and the 59 node certificates (`decide +kernel`).
5. **The return.** Lemma D in `Record1252270103Return/PhysicalDirect`. This
   removes `small_plain_shortening`, `shift_bound`, `large_shift_reserve`, the
   plain/width window fields and `freeShift` from `PhysicalSchedule`; it sets
   `cap` $=9/200$ and the C count cap to $13/250$. Then the 36 rectangles and
   `Candidate.bound`.

## Reproducing

```
python3 test_return69.py                       # return certifier reproduces PR #69 Certificate B
python3 cert_chain_k.py cchain_k8b.json 8      # exact source graph (59 nodes)
python3 certify_all_k.py cchain_k8b.json 8 8747289/10000000 802/1000 13/250 9/200 certificate_repeated_marks.json
python3 cchain_k.py 8 out.json                 # rebuild the rational graph (slow)
```

Files:
- `gain_fast.py`: the amplitude-resolved gain with $K$ copies.
- `gain_k.py`: the reference gain.
- `ss_fb.py`: the source-gate model (NF10–NF13).
- `fchain2.py`: the float graph explorer.
- `model69.py`, `pick_theta2.py`, `theta_of.py`, `return_opt.py`: the float
  return model with receipts.
- `bern.py`: exact Bernstein positivity.
