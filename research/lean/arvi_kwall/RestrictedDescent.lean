/-
Research file (QRH, K-wall and target 2). Sil's sixth-power descent, restricted to the large kernels.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveRanges

/-!
# The sixth-power descent restricted to kernels above `μ`

Sil's `lambda_sixth_extraction` bounds the completed sieve `λ(A, B)` (all supported rows of norm `≤ A`) by
`Σ_D θ(A/N(D)⁶, B)`, one sixth-power-free sieve per sixth root `D`. After a Poisson step these rows are the dual
frequencies. The ones whose sixth-power-free kernel has norm `≤ μ` are the twisted source spikes of the original
problem (journal 2026-10-31, "Target 2 needs one corrected Poisson step"). With them removed, the rows are those of
`aboveRows μ A`, and:

* `aboveRows_extraction`: `‖E_{aboveRows μ A, B}‖² ≤ Σ_{D ∈ roots} θ(A/N(D)⁶, B)`, over the roots of the restricted
  rows only;
* `root_bound_of_above`: every such root has `μ · N(D)⁶ < A`. So only `(A/μ)^{1/6}` roots survive, and the theta
  multiplicity becomes `(A/μ)^{1/6}` instead of `A^{1/6}`: the corrected theta term `T (N²/(T μ))^{1/6}` after
  Poisson.
-/

set_option autoImplicit false
namespace QRH.ArviKWall.RestrictedDescent
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve Candidate.FourthPower.SexticSieve Candidate.FourthPower.SieveOperator
open Candidate.FourthPower.SixthDecomposition Candidate.FourthPower.SieveRanges
open CenteredExceptionalCount FiniteSieveOperator
local notation "Id" => Ideal ActualEisensteinCubic.O

/-- The completed rows of norm `≤ A` whose sixth-power-free kernel has norm above `μ`. -/
def aboveRows (μ A : ℝ) : Finset Id :=
  (Candidate.FourthPower.SieveRanges.fullRange A).filter (fun I => μ < (Ideal.absNorm (sixthRemainder I) : ℝ))

theorem aboveRows_subset (μ A : ℝ) : aboveRows μ A ⊆ Candidate.FourthPower.SieveRanges.fullRange A := Finset.filter_subset _ _

/-- The restricted sieve is at most the completed one. -/
theorem above_le_lambda (μ A B : ℝ) : squaredNorm (aboveRows μ A) (freeRange B) ≤ lambda A B :=
  norm_mono (aboveRows_subset μ A) (Finset.Subset.refl _)

/-- **Restricted extraction.** The large-kernel rows split into sixth-power-free sieves at the reduced scales, one
per root of the restricted rows. -/
theorem aboveRows_extraction (μ A B : ℝ) :
    squaredNorm (aboveRows μ A) (freeRange B) ≤
      ∑ D ∈ (aboveRows μ A).image sixthQuotient, theta (A / (Ideal.absNorm D : ℝ) ^ 6) B := by
  apply (bound_iff _ _ _ (Finset.sum_nonneg (fun D _ => theta_nonneg _ _))).mpr
  intro a
  have hr : ∀ R ∈ aboveRows μ A, Supported R := fun R hR =>
    (Candidate.FourthPower.SieveRanges.mem_fullRange.mp (aboveRows_subset μ A hR)).1
  rw [exact_energy_decomposition _ _ hr (fun I hI => (mem_freeRange.mp hI).1), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro D _
  have hred : ∀ R ∈ reducedRows (aboveRows μ A) D,
      Supported R ∧ PowerFree 6 R ∧ (Ideal.absNorm R : ℝ) ≤ A / (Ideal.absNorm D : ℝ) ^ 6 := by
    intro R hR
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hIA, hID⟩ := Finset.mem_filter.mp hI
    have hIfull := aboveRows_subset μ A hIA
    have hs := (Candidate.FourthPower.SieveRanges.mem_fullRange.mp hIfull).1
    refine ⟨remainder_supported I hs, remainder_powerFree I, ?_⟩
    have hn := row_scale I hs A (Candidate.FourthPower.SieveRanges.mem_fullRange.mp hIfull).2
    simpa only [hID] using hn
  apply (energy_le_theta _ B _ _ hred (fun I hI => mem_freeRange.mp hI) (maskedCoefficient a D)).trans
  exact mul_le_mul_of_nonneg_left (coefficientMass_mask_le _ a D) (theta_nonneg _ _)

/-- **Only the small roots survive.** Every root `D` of a large-kernel row has `μ · N(D)⁶ < A`. -/
theorem root_bound_of_above {μ A : ℝ} {D : Id}
    (hD : D ∈ (aboveRows μ A).image sixthQuotient) :
    μ * (Ideal.absNorm D : ℝ) ^ 6 < A := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hD
  rw [aboveRows, Finset.mem_filter] at hI
  obtain ⟨hIA, hμI⟩ := hI
  have hs := (Candidate.FourthPower.SieveRanges.mem_fullRange.mp hIA).1
  have hn := row_scale I hs A (Candidate.FourthPower.SieveRanges.mem_fullRange.mp hIA).2
  have hq : 0 < (Ideal.absNorm (sixthQuotient I) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sixthQuotient_ne_zero I)))
  have hq6 : 0 < (Ideal.absNorm (sixthQuotient I) : ℝ) ^ 6 := pow_pos hq 6
  have hlt : μ < A / (Ideal.absNorm (sixthQuotient I) : ℝ) ^ 6 := lt_of_lt_of_le hμI hn
  have := (lt_div_iff₀ hq6).mp hlt
  linarith

/-- With `μ ≥ A` nothing survives: every large-kernel row would need a kernel of norm above its own norm. -/
theorem aboveRows_eq_empty_of_le {μ A : ℝ} (hμ : 0 ≤ μ) (h : A ≤ μ) : aboveRows μ A = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro I hI
  have hD : sixthQuotient I ∈ (aboveRows μ A).image sixthQuotient := Finset.mem_image_of_mem _ hI
  have hb := root_bound_of_above hD
  have hq : 1 ≤ (Ideal.absNorm (sixthQuotient I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (sixthQuotient_ne_zero I))
  have h6 : 1 ≤ (Ideal.absNorm (sixthQuotient I) : ℝ) ^ 6 := one_le_pow₀ hq
  nlinarith

end
end QRH.ArviKWall.RestrictedDescent

#print axioms QRH.ArviKWall.RestrictedDescent.aboveRows_extraction
#print axioms QRH.ArviKWall.RestrictedDescent.root_bound_of_above
#print axioms QRH.ArviKWall.RestrictedDescent.aboveRows_eq_empty_of_le
