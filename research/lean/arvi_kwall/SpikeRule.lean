import Submissions.arvi_kwall.Closure

/-!
# The spike rule breaks the amplify–reflect closure (log scale)

Research file (QRH, K-wall program). Mathlib and `Closure.lean` only.

`SexticSpikeFree.lean` reduces the selected norm at the balanced point to the graded spike-free conjecture.
- The selected rows are `W`; `x = log_B` of the source length and `n x = log_B` of the selected norm on `W`.
- The conjecture and the blockwise spike Bessel bound give the **spike rule**:
  `n 1 ≤ max (1 + ε) (n x + (1 − x + ε)/q)` for the dominant twist block `x ≤ 1 − qε`.
- The multiplicative form, with all blocks at once, is `selected_of_amplified`.

What this file proves:
- `spike_rule_forces`: with PR 93's amplification `n x ≤ n 1 − δ (1 − x)` at a slope `δ > 1/q + 1/q²` (written
  without division as `q + 1 < δ q²`), the spike rule forces `n 1 ≤ 1 + ε`.
- `nstar_violates_spike_rule`: the barrier function `nstar δ` of `Closure.lean` violates the sextic spike rule
  (`q = 6`) for every `7/36 < δ < 1/2` and `0 < ε < 1/6`. That function obeys the three closure rules with
  `n 1 = 7/6` for `1/3 ≤ δ < 1/2`. So the spike rule does not follow from the closure: it is new input, and it is
  enough to remove the `1/6` excess at the balanced point.
- `block_weight_le`, `blocks_weight_le`: the exponent count of the multiplicative recursion.
  - A twist block of size `M ≤ C B^{1−qε}` has weight `C B^{ε/q}(B/M)^{1/q}` and amplification factor `(M/B)^δ`.
  - The product is at most `C^{1+δ−1/q} B^{−ε(qδ − 1 − 1/q)}`.
  - Over the `O(log B)` dyadic blocks this gives `η → 0` exactly when `δ > 1/q + 1/q²`, which is `7/36` for the
    sextic family.
  - Then `selected_of_amplified` in `SexticSpikeFree.lean` closes the recursion.
-/

set_option autoImplicit false
namespace QRH.ArviKWall

/-- **The spike rule forces the balanced exponent down to `1 + ε`**, under amplification at slope
`δ > 1/q + 1/q²` (`q + 1 < δ q²`). -/
theorem spike_rule_forces {n : ℝ → ℝ} {δ ε q x : ℝ} (hq : 0 < q) (hε : 0 < ε) (hδ : q + 1 < δ * q ^ 2)
    (hx : x ≤ 1 - q * ε) (hamp : n x ≤ n 1 - δ * (1 - x))
    (hrule : n 1 ≤ max (1 + ε) (n x + (1 - x + ε) / q)) : n 1 ≤ 1 + ε := by
  by_contra h
  have h' : 1 + ε < n 1 := lt_of_not_ge h
  have h1 : n 1 ≤ n x + (1 - x + ε) / q := by
    rcases le_max_iff.mp hrule with h2 | h2
    · exact absurd h2 (not_le.mpr h')
    · exact h2
  have h2 : δ * (1 - x) ≤ (1 - x + ε) / q := by linarith
  have h3 : q * (δ * (1 - x)) ≤ 1 - x + ε := by
    have := mul_le_mul_of_nonneg_left h2 hq.le
    rwa [mul_div_cancel₀ _ hq.ne'] at this
  have hqd : 1 ≤ q * δ := by
    by_contra hc
    have hc' : q * δ < 1 := lt_of_not_ge hc
    have := mul_lt_mul_of_pos_left hc' hq
    linarith
  have hyq : q * ε ≤ 1 - x := by linarith
  have h4 : (q * δ - 1) * (q * ε) ≤ (q * δ - 1) * (1 - x) :=
    mul_le_mul_of_nonneg_left hyq (by linarith)
  have h5 : (q * δ - 1) * (1 - x) ≤ ε := by linarith
  have h6 : (q * δ - 1) * q * ε ≤ ε := by linarith
  have h7 : (q * δ - 1) * q ≤ 1 := by
    by_contra hc
    have hc' : 1 < (q * δ - 1) * q := lt_of_not_ge hc
    have := mul_lt_mul_of_pos_right hc' hε
    linarith
  linarith

/-- **The barrier function violates the sextic spike rule.** For `7/36 < δ < 1/2` and `0 < ε < 1/6`, the value
`nstar δ 1 = 7/6` exceeds both `1 + ε` and `nstar δ x + (1 − x + ε)/6` for every `x ≤ 1 − 6ε`. -/
theorem nstar_violates_spike_rule {δ ε : ℝ} (hδ : 7/36 < δ) (hε : 0 < ε) (hε1 : ε < 1/6) :
    1 + ε < nstar δ 1 ∧ ∀ x : ℝ, x ≤ 1 - 6 * ε → nstar δ x + (1 - x + ε) / 6 < nstar δ 1 := by
  rw [nstar_one]
  refine ⟨by linarith, fun x hx => ?_⟩
  have hx1 : x ≤ 1 := by linarith
  unfold nstar
  rw [frow_left hx1]
  rcases le_total x (7/6 + δ * (x - 1)) with h | h
  · rw [max_eq_right h]
    have h5 : 6 * ε * (δ - 1/6) ≤ (1 - x) * (δ - 1/6) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h6 : ε * (1/36) < ε * (δ - 1/6) := mul_lt_mul_of_pos_left (by linarith) hε
    linarith
  · rw [max_eq_left h]
    linarith

/-- **So the closure plus the spike rule pins the balanced exponent.** With `q = 6` and a slope `7/36 < δ`, every
function obeying amplification and the spike rule (at some dominant block `x ≤ 1 − 6ε`) has `n 1 ≤ 1 + ε`, while
`nstar δ` has `n 1 = 7/6`. -/
theorem sextic_spike_rule_forces {n : ℝ → ℝ} {δ ε x : ℝ} (hδ : 7/36 < δ) (hε : 0 < ε)
    (hx : x ≤ 1 - 6 * ε) (hamp : n x ≤ n 1 - δ * (1 - x))
    (hrule : n 1 ≤ max (1 + ε) (n x + (1 - x + ε) / 6)) : n 1 ≤ 1 + ε :=
  spike_rule_forces (by norm_num) hε (by nlinarith) hx hamp hrule

/-- **The exponent count, one block.** With the graded weight `C B^{ε/q} (B/M)^{1/q}` and the amplification factor
`(M/B)^δ`, a twist block of size `M ≤ C B^{1−qε}` contributes at most `C^{1+δ−1/q} B^{−ε(qδ − 1 − 1/q)}`. The exponent
is negative exactly when `δ > 1/q + 1/q²`. -/
theorem block_weight_le {q δ ε C B M : ℝ} (hq : 0 < q) (hδ : 1 / q < δ) (hC : 0 < C) (hB : 1 ≤ B)
    (hM0 : 0 < M) (hM : M ≤ C * B ^ (1 - q * ε)) :
    C * B ^ (ε / q) * (B / M) ^ (1 / q) * (M / B) ^ δ ≤
      C ^ (1 + δ - 1 / q) * B ^ (-(ε * (q * δ - 1 - 1 / q))) := by
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  have hMB : 0 < M / B := div_pos hM0 hB0
  have hd : 0 < δ - 1 / q := by linarith
  -- `(B/M)^{1/q} (M/B)^δ = (M/B)^{δ − 1/q}`
  have h1 : (B / M) ^ (1 / q) * (M / B) ^ δ = (M / B) ^ (δ - 1 / q) := by
    rw [show B / M = (M / B)⁻¹ by rw [inv_div], Real.inv_rpow hMB.le, ← Real.rpow_neg hMB.le,
      ← Real.rpow_add hMB]
    ring_nf
  -- `M/B ≤ C B^{−qε}`
  have h2 : M / B ≤ C * B ^ (-(q * ε)) := by
    rw [div_le_iff₀ hB0]
    calc M ≤ C * B ^ (1 - q * ε) := hM
      _ = C * B ^ (-(q * ε)) * B := by
          rw [mul_assoc, ← Real.rpow_add_one hB0.ne']
          ring_nf
  have h3 : (M / B) ^ (δ - 1 / q) ≤ (C * B ^ (-(q * ε))) ^ (δ - 1 / q) :=
    Real.rpow_le_rpow hMB.le h2 hd.le
  have h4 : (C * B ^ (-(q * ε))) ^ (δ - 1 / q) = C ^ (δ - 1 / q) * B ^ (-(q * ε) * (δ - 1 / q)) := by
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hB0.le _), ← Real.rpow_mul hB0.le]
  calc C * B ^ (ε / q) * (B / M) ^ (1 / q) * (M / B) ^ δ
      = C * B ^ (ε / q) * ((B / M) ^ (1 / q) * (M / B) ^ δ) := by ring
    _ = C * B ^ (ε / q) * (M / B) ^ (δ - 1 / q) := by rw [h1]
    _ ≤ C * B ^ (ε / q) * (C ^ (δ - 1 / q) * B ^ (-(q * ε) * (δ - 1 / q))) := by
        rw [← h4]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = C ^ (1 + δ - 1 / q) * B ^ (-(ε * (q * δ - 1 - 1 / q))) := by
        have hCe : C * C ^ (δ - 1 / q) = C ^ (1 + δ - 1 / q) := by
          rw [show (1 + δ - 1 / q) = 1 + (δ - 1 / q) by ring, Real.rpow_add hC, Real.rpow_one]
        have hBe : B ^ (ε / q) * B ^ (-(q * ε) * (δ - 1 / q)) = B ^ (-(ε * (q * δ - 1 - 1 / q))) := by
          rw [← Real.rpow_add hB0]
          congr 1
          field_simp
          ring
        calc C * B ^ (ε / q) * (C ^ (δ - 1 / q) * B ^ (-(q * ε) * (δ - 1 / q)))
            = (C * C ^ (δ - 1 / q)) * (B ^ (ε / q) * B ^ (-(q * ε) * (δ - 1 / q))) := by ring
          _ = C ^ (1 + δ - 1 / q) * B ^ (-(ε * (q * δ - 1 - 1 / q))) := by rw [hCe, hBe]

/-- **The exponent count, all blocks.** Summing the per-block bound over any finite family of blocks of sizes
`M_r ≤ C B^{1−qε}` gives `η ≤ #blocks · C^{1+δ−1/q} B^{−ε(qδ − 1 − 1/q)}`. -/
theorem blocks_weight_le {ι : Type*} (I : Finset ι) (Ms : ι → ℝ) {q δ ε C B : ℝ} (hq : 0 < q) (hδ : 1 / q < δ)
    (hC : 0 < C) (hB : 1 ≤ B) (hM0 : ∀ r ∈ I, 0 < Ms r) (hM : ∀ r ∈ I, Ms r ≤ C * B ^ (1 - q * ε)) :
    ∑ r ∈ I, C * B ^ (ε / q) * (B / Ms r) ^ (1 / q) * (Ms r / B) ^ δ ≤
      (I.card : ℝ) * (C ^ (1 + δ - 1 / q) * B ^ (-(ε * (q * δ - 1 - 1 / q)))) := by
  calc ∑ r ∈ I, C * B ^ (ε / q) * (B / Ms r) ^ (1 / q) * (Ms r / B) ^ δ
      ≤ ∑ _r ∈ I, C ^ (1 + δ - 1 / q) * B ^ (-(ε * (q * δ - 1 - 1 / q))) :=
        Finset.sum_le_sum fun r hr => block_weight_le hq hδ hC hB (hM0 r hr) (hM r hr)
    _ = (I.card : ℝ) * (C ^ (1 + δ - 1 / q) * B ^ (-(ε * (q * δ - 1 - 1 / q)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end QRH.ArviKWall

#print axioms QRH.ArviKWall.spike_rule_forces
#print axioms QRH.ArviKWall.nstar_violates_spike_rule
#print axioms QRH.ArviKWall.sextic_spike_rule_forces
#print axioms QRH.ArviKWall.block_weight_le
#print axioms QRH.ArviKWall.blocks_weight_le
