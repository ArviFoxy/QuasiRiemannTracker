import Mathlib

/-!
# Row splitting for the prime-pool face (research file, D1)

The twisted fourth moment F = Σ_z |A(z)|²|Q(z)|² (A a plain product of length Z^μ, Q a prime pool of length
Z^s with ‖a‖² = Z^s) is split by the pool's amplitude class: |Q(z)|² ≈ ‖a‖²·Z^{σ s}, σ ≤ 1. In log scale
(relative to ‖c‖²), the class σ contributes s + σ s + sel(σ), where Z^{sel(σ)} bounds the plain energy on the
rows of class σ. The diagonal is 1 + s, so the class is harmless iff σ s + sel(σ) ≤ 1.

* `class_le_of_fixPt`: if sel(σ) is the selected-norm fixed point max(μ, 1 − σ + σμ) (PR 93 proves this for
  σ > 1/2), the class is harmless on the ideal face μ + s ≤ 1.
* `ideal_face_of_fixPt`: so the fixed point at every slope (the K-wall conjecture) gives the face at Λ = 1.
* `low_class_excess`: with only the full-family bound sel = 1 below slope 1/2, the class σ carries the excess
  σ s > 0. Row-splitting proofs of D1 therefore reduce to the K-wall; a bypass must avoid splitting rows
  (dispersion in the prime variable).
-/

namespace QRH.ArviPrimeFace

/-- The selected-norm fixed point at slope `σ` and source length `μ`. -/
noncomputable def fixPt (σ μ : ℝ) : ℝ := max μ (1 - σ + σ * μ)

/-- A class at its selected-norm fixed point is harmless on the ideal face `μ + s ≤ 1`. -/
theorem class_le_of_fixPt {σ μ s : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hs : 0 ≤ s)
    (hface : μ + s ≤ 1) : σ * s + fixPt σ μ ≤ 1 := by
  unfold fixPt
  rcases le_total μ (1 - σ + σ * μ) with h | h
  · rw [max_eq_right h]
    nlinarith [mul_le_mul_of_nonneg_left hface hσ0]
  · rw [max_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_right hσ1 hs]

/-- **Fixed point at every slope ⇒ ideal face.** If every amplitude class `σ ∈ [0, 1]` has plain energy at
most the selected-norm fixed point, then on `μ + s ≤ 1` no class exceeds the diagonal. -/
theorem ideal_face_of_fixPt {μ s : ℝ} (hs : 0 ≤ s) (hface : μ + s ≤ 1) (sel : ℝ → ℝ)
    (hsel : ∀ σ, 0 ≤ σ → σ ≤ 1 → sel σ ≤ fixPt σ μ) :
    ∀ σ, 0 ≤ σ → σ ≤ 1 → σ * s + sel σ ≤ 1 := by
  intro σ h0 h1
  have := class_le_of_fixPt h0 h1 hs hface
  linarith [hsel σ h0 h1]

/-- **Low classes without the K-wall.** With only the full-family bound `sel = 1`, a class `σ > 0` exceeds
the diagonal by exactly `σ s`. -/
theorem low_class_excess (σ s : ℝ) : σ * s + 1 - 1 = σ * s := by ring

/-- At the binding K-wall slope `1/2`, the worst trivial excess is `s/2`. -/
theorem low_class_excess_le {σ s : ℝ} (hs : 0 ≤ s) (hσ : σ ≤ 1/2) : σ * s ≤ s / 2 := by
  nlinarith

end QRH.ArviPrimeFace

#print axioms QRH.ArviPrimeFace.ideal_face_of_fixPt
