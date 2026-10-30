import Submissions.arvi_rip.Coherence

/-!
# Product certificates never beat plain Gershgorin

Research file (QRH, RIP program (4); the fresh look's §1.4, `rip/wide/FRESH_LOOK.md`).

`TensorAmplify.lean` turns an RIP bound for a product dictionary `x_z ⊗ y_z` into a selected bound for the `x_z`,
amplified by `w_z = ⟨e, y_z⟩`. With Gershgorin on the product (pairwise coherence `μ_x μ_y`) and a detection floor
`|⟨e, y_z⟩| ≥ w` on the support `S`, the certificate is

  `Σ_{z∈S} |⟨a, x_z⟩|² ≤ U_prod ‖a‖²`,  `U_prod = (1 + m μ_x μ_y) / w²`,  `m = |S| − 1`.

Plain Gershgorin on the `x_z` alone gives `U_plain = 1 + m μ_x`. Here:

* `bessel_of_gershgorin`: unit vectors of coherence `μ` on `S` have Bessel bound `1 + m μ`, so a detection floor
  obeys `(m + 1) w² ≤ 1 + m μ_y`.
* `product_ge_plain`: then `U_prod ≥ U_plain`, because `(1 − μ_x)(1 − μ_y) ≥ 0`.
* `product_certificate_ge_plain`: the two combined, for actual vectors.

So pairing the rows with other data only relabels which coherence is assumed: the binding input is the rows' own
coherence inside the support.
-/

namespace QRH.ArviRIP

open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [DecidableEq ι]

/-- Gershgorin gives the Bessel bound `Σ |⟨e, u_i⟩|² ≤ (1 + μ (|S| − 1)) ‖e‖²`. -/
theorem bessel_of_gershgorin (S : Finset ι) (hS : S.Nonempty) (u : ι → E) (e : E) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hμ : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ‖⟪u i, u j⟫_ℂ‖ ≤ μ) :
    ∑ i ∈ S, ‖⟪e, u i⟫_ℂ‖ ^ 2 ≤ (1 + μ * ((S.card : ℝ) - 1)) * ‖e‖ ^ 2 := by
  set T := ∑ i ∈ S, ‖⟪e, u i⟫_ℂ‖ ^ 2 with hT
  set K := 1 + μ * ((S.card : ℝ) - 1) with hK
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => by positivity
  -- the vector v = Σ ⟨u_i, e⟩ u_i
  set c : ι → ℂ := fun i => ⟪u i, e⟫_ℂ with hc
  set v := ∑ i ∈ S, c i • u i with hv
  have hcn : ∑ i ∈ S, ‖c i‖ ^ 2 = T := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc, ← inner_conj_symm, Complex.norm_conj]
  have hinner : ⟪e, v⟫_ℂ = (T : ℂ) := by
    rw [hv, inner_sum]
    push_cast [hT]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, ← inner_conj_symm e (u i), Complex.mul_conj', Complex.norm_conj]
  have hv2 : ‖v‖ ^ 2 ≤ K * T := by
    have h := gershgorin_rip S c u hμ0 hu hμ
    rw [hcn] at h
    have := (abs_le.mp h).2
    rw [hK]; nlinarith [this]
  -- T = ⟨e, v⟩ ≤ ‖e‖ ‖v‖, so T² ≤ ‖e‖² K T
  have hTle : T ≤ ‖e‖ * ‖v‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) e v
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0] at h
    exact h
  have hK0 : 0 ≤ K := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    rw [hK]; nlinarith [mul_nonneg hμ0 (sub_nonneg.mpr this)]
  have hsq : T ^ 2 ≤ ‖e‖ ^ 2 * (K * T) := by
    calc T ^ 2 ≤ (‖e‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ hT0 hTle 2
      _ = ‖e‖ ^ 2 * ‖v‖ ^ 2 := by ring
      _ ≤ ‖e‖ ^ 2 * (K * T) := mul_le_mul_of_nonneg_left hv2 (by positivity)
  rcases hT0.lt_or_eq with hpos | hzero
  · have : T * T ≤ (K * ‖e‖ ^ 2) * T := by nlinarith [hsq]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

/-- The certificate comparison as a real inequality. -/
theorem product_ge_plain {m μx μy w : ℝ} (hm : 0 ≤ m) (hx0 : 0 ≤ μx) (hx1 : μx ≤ 1)
    (hy1 : μy ≤ 1) (hw : 0 < w) (hcap : (m + 1) * w ^ 2 ≤ 1 + m * μy) :
    1 + m * μx ≤ (1 + m * μx * μy) / w ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have hm1 : 0 < m + 1 := by linarith
  have key : (1 + m * μx) * (1 + m * μy) ≤ (m + 1) * (1 + m * μx * μy) := by
    nlinarith [mul_nonneg hm (mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1))]
  have h1 : (m + 1) * ((1 + m * μx) * w ^ 2) ≤ (m + 1) * (1 + m * μx * μy) := by
    calc (m + 1) * ((1 + m * μx) * w ^ 2) = (1 + m * μx) * ((m + 1) * w ^ 2) := by ring
      _ ≤ (1 + m * μx) * (1 + m * μy) :=
          mul_le_mul_of_nonneg_left hcap (by nlinarith [mul_nonneg hm hx0])
      _ ≤ (m + 1) * (1 + m * μx * μy) := key
  exact le_of_mul_le_mul_left h1 hm1

/-- **Product certificates never beat plain Gershgorin.** If unit vectors `y_z` of coherence `μ_y` on `S` are
detected by a unit `e` with `|⟨e, y_z⟩| ≥ w > 0`, then the product certificate `(1 + m μ_x μ_y)/w²` is at least the
plain one `1 + m μ_x`, for every `μ_x ∈ [0, 1]` (`m = |S| − 1`). -/
theorem product_certificate_ge_plain (S : Finset ι) (hS : S.Nonempty) (y : ι → E) (e : E)
    {μx μy w : ℝ} (hx0 : 0 ≤ μx) (hx1 : μx ≤ 1) (hy0 : 0 ≤ μy) (hy1 : μy ≤ 1) (hw : 0 < w)
    (hy : ∀ i ∈ S, ‖y i‖ = 1)
    (hμ : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ‖⟪y i, y j⟫_ℂ‖ ≤ μy)
    (he : ‖e‖ = 1) (hdet : ∀ i ∈ S, w ≤ ‖⟪e, y i⟫_ℂ‖) :
    1 + ((S.card : ℝ) - 1) * μx ≤ (1 + ((S.card : ℝ) - 1) * μx * μy) / w ^ 2 := by
  have hm : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    linarith
  refine product_ge_plain hm hx0 hx1 hy1 hw ?_
  have hb := bessel_of_gershgorin S hS y e hy0 hy hμ
  rw [he, one_pow, mul_one] at hb
  have hlow : (S.card : ℝ) * w ^ 2 ≤ ∑ i ∈ S, ‖⟪e, y i⟫_ℂ‖ ^ 2 := by
    have : ∑ i ∈ S, w ^ 2 ≤ ∑ i ∈ S, ‖⟪e, y i⟫_ℂ‖ ^ 2 :=
      Finset.sum_le_sum fun i hi => pow_le_pow_left₀ hw.le (hdet i hi) 2
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  calc ((S.card : ℝ) - 1 + 1) * w ^ 2 = (S.card : ℝ) * w ^ 2 := by ring
    _ ≤ ∑ i ∈ S, ‖⟪e, y i⟫_ℂ‖ ^ 2 := hlow
    _ ≤ 1 + μy * ((S.card : ℝ) - 1) := hb
    _ = 1 + ((S.card : ℝ) - 1) * μy := by ring

end QRH.ArviRIP

#print axioms QRH.ArviRIP.product_certificate_ge_plain
