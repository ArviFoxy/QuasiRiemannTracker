# A new lemma in the final return? Transfer candidates, count windows, exact prices (2026-10-26)

Written by the return-transfer agent and saved here by the orchestrator. Scripts and logs are in this
directory.

## Short answer

1. **There is a return lemma that lowers θ\*, and it is not a transfer: Lemma W.**
   - **What it changes.** The return carries three conservative count windows from Collet's
     certificate:
     - the lower plain window `m_- = 2/5`;
     - the width window `s_+ < cap`;
     - the fixed natural-tail join at `m_H`.

     With the flat mixed faces (Λ ≈ 2.1) these windows bind. Lemma W opens them to the faces' proved
     domain and moves the tail join to the crossover, where the face width equals the natural width.
   - **Value (exact certificates).** θ\* 0.8742701 → **0.8741364** (−1.337e-4) at the design point, and
     0.8741359 (−1.342e-4) with h = 803/1000.
   - **Inputs and cost.** No new analytic input. It re-instantiates Collet's generic count theorem,
     whose Lean hypotheses already allow it. About 100–150 hand-written lines in `FinalReturn`, plus
     regenerated certificates.
2. **The binding at the design point is not the capacity `C_N(d₊)`.**
   - The cover fails at δ ≈ 0.3747, p → 1/2, on `new_top`.
   - Below that δ, the count face's capped branch `Ccap` has margin +5e-4 but is not admitted, because
     its crossing plain length is `m* < m_- = 2/5`.
   - The atlas's largest item, the old branch's `(1 − δ)`, only measures this gap. It disappears with
     Lemma W.
3. **The transfer candidates are negative, for a structural reason.**
   - The return's high side never applies Poisson in the rows, so there is no Gauss sum for
     `G(D⁴k) = χ(D)²G(k)` to act on.
   - The plain and numerator moments it uses are faces, which already contain the transfer.
   - The marked inverse moment has no pointwise slot energy to pay.
   - In the long moment, fourth powers give cubic twists, not copies.
4. **After Lemma W the return is tight given its inputs.**
   - The binding is the capped count branch at the count face's proved cap: `new_top`, δ\* = 0.4311,
     p = 1/2.
   - Remaining levers:
     - the count's own inputs: inverse line weight 0.56, long line 0.30;
     - the count face's **cap**, through the plain line (weight 0.14): dθ\*/dcap ≈ −0.0078, saturating at
       −6.0e-5 by cap ≈ 0.085;
     - the physical face: dθ\*/dB_P = −0.0087, dθ\*/dC = −0.023.

## Lemma W

**Setting.**
- The count face is `(B, Λ, cap)`, proved on `m ∈ [0, 1/2]`, `0 ≤ s ≤ cap`.
- The natural plain width is `(1 − 2m)/K` (K = 9/2), with `Λ < K`.
- The crossover is `m_X = (K·B − Λ)/(2(K − Λ))`, with `w_X = (1 − 2m_X)/K = (B − 2m_X)/Λ`.
  - For C: `m_X = 0.46614`, `w_X = 0.01505`.
  - For P: `m_X = 0.46751`.
  - Collet joins at `m_H = 0.42350`, where the face width is still 0.0557 against the natural 0.034.

**Statement.** Fix `δ ∈ [0, 3/4]`, `p ∈ [0, 1/2]`, and a branch b: either affine with window
`s_+ ≤ cap`, or capped at `z* ≤ cap`. Let `(r*, m*, t*)` be its crossing (FR4/FR5) and `R = N/J`.
Suppose the following hold on the upward window `[δ₀, δ₁] × [p₀, 1/2]`:
- **(i)** the FR8 range tests: `D, A, C₀, J > 0`, `1 < t* < 12499/10000`, `23/37 < r* < 1`, and
  `UJ_p − U_pJ > 0`;
- **(ii)** the plain window:
  - affine: `(B − Λ(s_+ − η))/2 + η < m* < m_X − η`;
  - capped: `η < m* < min(m_X, (B − Λz*)/2) − η`;
- **(iii)** `N − (1 − 2δm_X − 2δp·w_X)J > 0`.

Then every buffered class `(δ, p)` has at most `U^{R+ε}` rows.

**Proof.** Run FR9's witness argument with the plain envelope

`P_env(m) = 1 − 2δm − 2δp·max(min(cap_b, (B − 2m)/Λ), (1 − 2m)/K)`.

1. On `[m*, m_X]` the face width is the larger term, and on `[m_X, 1/2)` the natural width. The two
   agree at `m_X`.
2. All slopes are negative, so `P_env` is continuous and decreasing.
3. By (ii) the branch uses exactly the face width at `m*`, so `P_env(m*) = R`.
4. Hence every plain witness at `m ≥ m*` is counted at `≤ R`: by the face up to `m_X`, and by the
   natural moment beyond it, where (iii) gives its value at the join.
5. Inverse and long witnesses are as in FR9. ∎

Collet's FR8 is the special case `m_- = 2/5`, `s_+ ≤ s_C`, join at `m_H`. There the envelope jumps up at
`m_H`, and the N-tail test exists to pay for that jump.

**Lean.** Checked by reading the statements, not by building.
- `count_from_piecewise_moments` and `count_fiber_at_window` (`Record1252270103Return/CountFromMoments.lean`,
  `WindowFiber.lean`) need only:
  - `0 ≤ mLo`;
  - `2/5 ≤ mHi < 1/2`;
  - positive widths on `[mLo, mHi]`;
  - the natural tail at `mHi` bounded by the target;
  - `cap ≤ sourceCap ≤ 7/37`.
- `AdmittedWindow` stores `mLo`/`mHi` per window.
- So the 2/5, the 11/25 and the join at `m_H` live only in the generated instance
  (`FinalReturn/FinalWindows.lean`, `ReturnFormulas.lean`).

**Exact prices.** No single relaxation helps on its own; the gain comes from the combination.

| configuration | θ\* | Δ |
|---|---|---|
| Collet windows (baseline) | 0.8742701 | — |
| `m_- = 0` only | 0.8742681 | −2.0e-6 |
| `s_+ = cap` only | 0.8742701 | 0 |
| crossover join only | 0.8742701 | 0 |
| `m_- = 0`, `s_+ = cap`, Collet join | 0.8742619 | −8.2e-6 |
| `m_- = 0`, crossover, capped branch at the cap | 0.8741541 | −1.160e-4 |
| **Lemma W** (all three; windows at cap − 1e-4) | **0.8741364** | **−1.337e-4** |
| Lemma W with h = 803/1000 | 0.8741359 | −1.342e-4 |

**Checks.**
- **Generator diff.** Collet's own candidate list gives the same value with `s_C = s_Pp = 749/10000`,
  `m_- = 0` and the crossover join. The cover uses old, Ccap, C and C-6, with 20 admission windows
  and 46 rectangles.
- **Robust** to extra branches, and across mixed face sets: published-grid faces 0.8742701 → 0.8741363.
- **Without the dMinus > 1/2 relaxation:** 0.8743734 → 0.8742093. The two stack.
- **No gain on the PR 76 faces.** Lemma W is a companion to the mixed step.
- **Independent pointwise check:** `verify_windows.py`, 198 sample points.

**Lean cost.** Everything is in `FinalReturn`; nothing changes in `ReturnD`, in Collet's tree or in the
mixed step.
- **`gen_return_lean.py`:**
  - `lowerM`: `2/5 → 0`;
  - `upperM`: `min(1/2 − η, m_X b − η, capped: (B − Lz*)/2 − η)`;
  - `naturalM := m_X b`;
  - admission guards for the N-tail at `m_X`, `1/2 − m_X − η`, `w_X > η`, and `(z* − η)·DJ`;
  - `branchCap = 749/10000`.
- **`fork_return.py`:**
  - `CountWidth`: `natural_join_bounds` per branch, and `admitted_widths`;
  - `CountDecode`: the tail identity `(1 − 2m_X)/K = w_X`;
  - `FinalWindows`: `mHi := m_X w.branch`.
- **Regenerated:** `CountWindows` and `Rows`.

## The binding after Lemma W

**The binding point.** On `new_top`, the capped C branch at `z* = 0.0749`:
- capacity `C = 0.045243`;
- δ\* = 0.4311, p = 1/2;
- R = 0.624728, r\* = 0.7410, m\* = 0.3978, t\* = 1.1388.

**Dual weights.** Inverse 0.560, plain 0.140, long 0.300.

**Sensitivities.** dθ\*/dR = 0.129, dθ\*/dE = 0.214, dθ\*/dC = −0.0231, dθ\*/dz\*_count = −0.0078.

**What no longer matters.** `s_C`, `s_P` and the count face's (B, Λ).

**Next receipts to watch.**
- `floor`: slack 8.4e-4;
- `principal_z`: slack 9.1e-5.

## Other candidates

- **Transfer in the numerator's fourth moment: no.**
  - No row Poisson on the high side.
  - The moment is face P, which is already in the transfer's chain.
  - The 1/2 in `−δpC/2` cannot be removed: faces charge doubled slots with multiplicity.
- **Old branch's `(1 − δ)`: a window artifact.** With Lemma W it has 0.0021 of slack.
- **Count face cap:** 0.080 → −3.9e-5; 0.085–0.10 → −6.0e-5.
- **Levy's (4/3, 4) Hölder step is optimal given its inputs.** A consistent adversary attains it.
- **Better count inputs, on top of Lemma W:**
  - long slope 0.82 → −7.2e-5, 0.80 → −1.82e-4;
  - inverse slot cost 1.9 → −2.17e-4, 1.8 → −3.83e-4.

## Recommendation

1. Formalize Lemma W together with the mixed-step return.
2. Point the source side at the count face's cap: ≈ 0.085 is worth up to −6.0e-5.
3. Drop the transfer-in-the-return candidates.

## Inferences not verified

- Re-choosing the physical face gains less than 1e-7.
- A doubled slot costs 2Λ in a face step.
- The dilation adds at least 4 per unit to the column branch's dual length.
- The chain can prove the count face with a cap above 3/40.
- The causal reading of why the windows bind.
- Lean feasibility of Lemma W (read, not built).
