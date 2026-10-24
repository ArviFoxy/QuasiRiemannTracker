# Cap induction in the source step, and where the method is pinned

**Result.** A new source-step lemma (Lemma F, cap induction) together with a finer chain search moves
the float-model chain to the exact-return value

$$\theta^*=0.8747257,$$

that is $3.2\cdot10^{-6}$ below the committed Lean value $0.8747289$ (`../repeated-marks`). This is
below the $10^{-5}$ bar, so it is **not formalized**. The rest of this note records why the current
estimates cannot give $10^{-5}$: every remaining lever has been measured, and the binding constraints
are four analytic exponents of the cubic/sextic method.

## 1. Lemma F: a node can be its own LOW parent

**Setting.** Collet's NF source step (feedback.tex NF4, NF8–NF13; sources.tex G9–G13) proves a face
$G(B,\Lambda,h)$ from a LOW parent $G(B_0,\Lambda_0,h_0)$ and a HIGH parent. On a width cell with
upper endpoint $b$ put $t=B-\Lambda(b-e)$. The LOW proof erases marked width above the parent's
capacity at price $q$ per unit, paid by the sextic amplifier:

$$a=\frac{q\{b+(t-B_0)/\Lambda_0\}+r}{1-6qB_0/\Lambda_0},\qquad F=1-6a,\qquad z_0=\frac{B_0F-t}{\Lambda_0}.$$

At the cap the child lies above the old parent line by $(h-b_\times)(\Lambda_0-\Lambda)/\Lambda_0$, and
the small denominator ($\approx3\cdot10^{-3}$) turns this into $a\approx9\cdot10^{-3}$. That is the
cap-side cost which makes the HIGH gate bind at $b=h$ on every late node of the committed chain.

**Lemma F.** Let $G(B,\Lambda,c)$ be proved, $0<c<h$, and fix $q$ with $1-6qB/\Lambda>0$. Put
$a'=(qe+r)/(1-6qB/\Lambda)$ and $\Delta=6a'(B/\Lambda-h)$. If the NF10–NF13 gates hold on every cell
$[c',c'+\Delta]\subset[c,h]$ with LOW parent $(B,\Lambda,c')$, then $G(B,\Lambda,h)$ holds.

*Proof.* Induction on the cap $c_k=c+k\Delta$. Step $k$ is Collet's step
(`uniform_squarefree_source_step`) with LOW parent $G(B,\Lambda,c_{k-1})$ and crossing $c_{k-1}$:
$\lambda\le\lambda_0$ holds with equality, the crossing equals the parent cap, and the budget identity
reads $B-B+(\Lambda-\Lambda)c_{k-1}=0\le0$. With the same line, $b+(t-B)/\Lambda=e$, so the excess
vanishes, $a=a'$ and $g=a-q\{b+(t-BF)/\Lambda\}=r$. The weak guard $z_0\le h_0F$ becomes
$b-c_{k-1}\le6a'(B/\Lambda-c_{k-1})-O(e)$, which holds on the cell. The HIGH proof does not use the
LOW parent. $\square$

**Hybrid node.** Use the old parent on $[b_\times,b_1]$ (threshold $q_1<\Lambda_0/(6B_0)$) and Lemma F
on $[b_1,h]$ (threshold $q_2<\Lambda/(6B)$); $b_1$ is the smallest point where the self cells close.
The cap side then has HIGH slack $\approx0.03$, and the binding moves to $b_1\approx b_\times$, where
the HIGH gate at $\nu=q_2$ binds.

## 2. Measured effect

All values use the exact return certifier (`../repeated-marks/cert_return.py`, global mode,
$h=401/500$, $s_+=13/250$, $s_P=9/200$) through `evalchain.py`.

| chain | $\theta^*$ |
|---|---|
| committed graph `../repeated-marks/cchain_k8b.json` (same evaluator) | 0.8747287 |
| finer $q$ search, pivots every $0.00025$ after node 40 (no new lemma) | 0.8747275 |
| Lemma F hybrid, committed pivots (`chain_hyb.json`) | 0.8747267 |
| Lemma F + fine pivots + HIGH density floor $0.45$ (`chain_h45.json`), 22/23 rule kept | 0.8747266 |
| same, $B_H\ge22/23$ replaced by a natural-moment plain fallback | 0.8747259 |
| same, also without the receipt $\Lambda_P>3$ | **0.8747257** |

The density floor: the feedback HIGH count's conditions (HF13, HF14, LD6–LD8, Lemma C) hold on
$[0.45,3/4]$; only the uniform bound $C_\nu<1/40$ (LD11) fails there, and the repeated-mark gain uses
$C_{\max}=\nu(1-\xi_0)$ instead. Alone it gains $5\cdot10^{-7}$.

## 3. Retracted: an amplitude split of LOW and HIGH

An earlier draft ("Lemma E") let rows whose cheapest marked slots have small amplitude at the detected
zero be erased as LOW rows even when their zero density is $\ge q$. This is **invalid**: the LOW erasure
(`actual_restricted_erasure_supplier`, `ActualLow`) needs the zero-free slot bound
$|\text{slot}|^2\ll Z^{qw}$ uniformly in real power and height, because source rows carry independent
heights. The amplitude at one zero says nothing at other heights. The large gains it seemed to give
are void.

## 4. Where the method is pinned

**The faces are weak levers.** At the binding point ($d=h$, $\delta\approx0.4546$, $p=1/2$):
$\partial\theta/\partial B_C\approx-4.0\cdot10^{-3}$ (count face at $z\approx0.045$) and
$\partial\theta/\partial B_P\approx-6.7\cdot10^{-3}$ (physical face at $z\approx0.041$). A gain of
$10^{-5}$ needs about $10^{-3}$ more face height; Lemma F gives about $2\cdot10^{-4}$.

**The source chain is pinned by the amplifier.** On every node the LOW/HIGH threshold sits at
$q\approx\Lambda/(6B)$, the HIGH gate binds at $\nu=q$ at the pivot, and the chain ends where
$q\to1/2$ and $B\to22/23$ meet. Multi-ancestor LOW parents, steeper virtual parents, repeated slots
in the HIGH plain witness and finer pivots were all checked (chain rebuilds or exact gate
computations) and give nothing measurable.

**The return is at its optimum.** The count is the weighted mean of the intercepts of the inverse,
long and plain lines (weights $0.505,0.303,0.193$). The fourth-moment Hölder glue, the conductor
top $h$, the caps $s_+,s_P$ and every receipt are non-binding or optimal. The class $p=1/2$ binds
because a row's own zero saturates its prime slots, so it is the generic class, not a tail.

**What binds: four exponents of the cubic/sextic method.**

| atom | source | $\theta$ value of a small change |
|---|---|---|
| slot cost 2 in the marked inverse moment ($r+2z\le m$) | reflected-energy column branch: each active slot prime becomes a cubic character of the dual index (twisted multiplicativity $a_0(pn)=a_0(p)a_0(n)\chi_n(p)^4$) and enters the conductor squared | $r+2z\le1.001$: about $1.5\cdot10^{-5}$ |
| amplifier exchange 6 | only sixth powers act trivially on every Gauss sum, $g(u,p^6h)=g(u,h)$ | $6\to5.9$: about $1.5\cdot10^{-5}$ |
| long slope $(1+5r)/6$ | the only exact row lift is $u\mapsto ua^6$ | per $10^{-3}$ in the long line: $4\cdot10^{-5}$ |
| plain slot cost $6\kappa$ (faces $\Lambda\approx2.9$) | pointwise zero-free slot bound inside the plain descent's $5/6$ structure | via the faces only |

A cross-check against the QRH catalogue found no record that lowers any of the four. The external
optimal sextic large sieve (de Faveri, arXiv 2610.04045) gives a slot-free canonical-energy bound, but
it fails at label size $V=0$, which is exactly the inverse moment's binding configuration; for pure
slot products it still forces cost 2.

## Reproducing

```sh
python3 hybchain.py chain_hyb.json                          # Lemma F hybrid, committed pivots (~45 min)
python3 hybchain2.py 0.45 0.0335 0.00025 0.050 chain_h45.json # consolidated chain (~70 min)
python3 evalchain.py chain_h45.json [relax22] [relaxLP]       # exact return value
```

## 5. Formalization route: Lemma F needs no new predicate (2026-10-24)

An earlier note said Lemma F would need a new validity predicate, because the fork's finite
predicate computes the crossing as `crossing n low = (low.B − n.B)/(low.L − n.L)` and requires
`n.L < low.L`. That is not necessary.

- **Collet's analytic step already allows it.** `uniform_squarefree_source_step`
  (`Record1252270103Source/Low/GlobalInitialAssemblyUniform.lean`) takes the crossing `cross` as a
  free parameter. Its only conditions linking child and parent are `lam ≤ lam₀` (not strict),
  `cross ≤ cap₀` and `B − B₀ + (lam₀ − lam)·cross ≤ 0`. A self step `(B, Λ, c_{k−1}) → (B, Λ, c_k)`
  with `cross = c_{k−1}` meets all three with equality.
- **The finite predicate accepts a rotated self-parent.** Take the child
  `n = (low.B − η·c_{k−1}, low.L − η, c_k)` for a tiny rational `η > 0`. Then
  `crossing n low = c_{k−1}` exactly, `n.L < low.L`, and the crossing equals the parent's cap, which
  `SourceValidC` allows (`crossing n low ≤ low.cap`). Every gate in `SourceFormulas.lean` reads the
  parent only through `sourceDen`, `sourceA`, `sourceF`, `weakCap` and `low.cap`. With the rotation
  the excess term `b + (t − low.B)/low.L` equals `(η(b − c_{k−1}) + n.L·e)/low.L`, so the amplifier
  differs from Lemma F's `a'` by `O(η)`. The child's line lies below the parent's for `z < c_{k−1}`
  and above it beyond, as an ordinary step requires.
- **Cost of the rotation.** After `K` self steps the face is `(B − ηΣc_k, Λ − Kη)`. With `η = 10⁻⁹`
  this is invisible in θ.
- **Number of cells.** The cell length is `Δ = 6a'(B/Λ − h)` with `a' = (qe + r)/(1 − 6qB/Λ)`.
  With Collet's fees (`e = 10⁻¹²`, `r = 10⁻⁸`) and the chain's thresholds (`1 − 6qB/Λ ≈ 3·10⁻⁴`),
  `a' ≈ 4·10⁻⁵` and `Δ ≈ 7·10⁻⁵`, i.e. about 200 cells per late node. The fee `r` is a per-node
  parameter of `Source` (`lowFee`). Raising it to about `3·10⁻⁷` on the self cells gives
  `a' ≈ 10⁻³` and `Δ ≈ 1.7·10⁻³`, about 9 cells per node. The price is `a'` in the gates: about
  `1.5a'` in the HIGH gate, against a cap-side HIGH slack of about 0.03 after Lemma F; `9a'` in the
  centered gate; and `F = 1 − 6a'`. The binding gate of a hybrid node is at the join `b_1`, where
  the old parent is used, so this choice does not move θ.

So a Lemma F node is a short run of ordinary source steps with nearly equal slopes and increasing
caps. Formalizing it means generating these extra nodes and their certificates (scalar gates, weak
cap, density Bernstein checks, HIGH Bernstein trees) with the existing generator and Lean
infrastructure. No new analytic statement and no new predicate are needed. With raised self-cell
fees that is several hundred extra certified nodes (about 9 per late node). A parametric
certificate in `c` plus one Lean induction lemma would avoid them, but that is a new predicate.

The density floor `0.45` (part of the 0.8747257 value) is different. It changes Collet's LD11
uniform bound and would need an edit to the imported HIGH-count code.
