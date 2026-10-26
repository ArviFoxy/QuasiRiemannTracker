/- Mixed source step, collisions: the colliding prime's Gauss factor has norm at most `√N(p)` at
every frequency. Off `p` it is a unit rescaling of the Gauss sum at `1` (norm `√N(p)` for the
nonprincipal `χ_p²`); on `p` it is the character sum of a nonprincipal character, i.e. zero. -/
import Submissions.arvi_mixed_step.Collision.Polynomial
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsSharpScalar
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Collision
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve CubicEisenstein ConcreteTraceCRT
open ProbePrimePower ProbePhysical CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

/-- Unit rescaling of a prime Gauss sum. -/
theorem primeGauss_unit (p : O) (hp : p ≠ 0) [hmax : (Ideal.span {p}).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H' : O) (hH : ¬p ∣ H') :
    letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
    primeGauss p hp χ H' = χ (Ideal.Quotient.mk _ H')⁻¹ * primeGauss p hp χ 1 := by
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Finite (O ⧸ Ideal.span {p}) := finite_quotient_span hp
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  set u := Ideal.Quotient.mk (Ideal.span {p}) H' with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact hH
  unfold primeGauss
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  symm
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ u hu)]
  apply Finset.sum_congr rfl
  intro x _
  have hx : (Equiv.mulLeft₀ u hu) x = u * x := rfl
  rw [hx, map_one, one_mul, ← mul_assoc, ← map_mul, inv_mul_cancel_left₀ hu]

theorem norm_char_unit (F : Type*) [Field F] [Finite F] (χ : MulChar F ℂ) (u : F) (hu : u ≠ 0) :
    ‖χ u‖ = 1 := by
  letI : Fintype F := Fintype.ofFinite F
  have h := χ.apply_mem_rootsOfUnity (Units.mk0 u hu)
  have h1 := Complex.norm_eq_one_of_mem_rootsOfUnity h
  rw [MulChar.coe_equivToUnitHom] at h1
  simpa using h1

/-- The colliding prime's factor has norm at most `√N(p)` at every frequency. -/
theorem collisionFactor_norm_le (p : O) (hp : Prime p) (hsp : Supported (Ideal.span {p})) (H' : O) :
    ‖collisionFactor p hp hsp H'‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  letI hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Finite (O ⧸ Ideal.span {p}) := finite_quotient_span hp.ne_zero
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  obtain ⟨hg, hc⟩ := supported_prime_data p hp hsp
  set χ := actualSextic (Ideal.span {p}) hg ^ 2 with hχ
  have hχ1 : χ ≠ 1 := by
    intro h
    have := (actualSextic_pow_eq_one_iff _ hg hc 2).mp h
    omega
  unfold collisionFactor
  by_cases hH : p ∣ H'
  · -- the character sum of a nonprincipal character vanishes
    have hz : Ideal.Quotient.mk (Ideal.span {p}) H' = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hH)
    have h0 : primeGauss p hp.ne_zero χ H' = 0 := by
      unfold primeGauss
      rw [tsum_fintype]
      simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
      exact MulChar.sum_eq_zero_of_ne_one hχ1
    simp only [← hχ] at h0 ⊢
    rw [h0, norm_zero]; positivity
  · have hu := primeGauss_unit p hp.ne_zero χ H' hH
    simp only [← hχ]
    rw [hu, norm_mul]
    have hne : (Ideal.Quotient.mk (Ideal.span {p}) H')⁻¹ ≠ 0 := by
      apply inv_ne_zero
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact hH
    rw [norm_char_unit _ χ _ hne, one_mul]
    rw [primeGauss_actual_pow_norm p hp hg hc 2 (by norm_num) (by norm_num)]

end
end QRH.MixedStep.Collision
#print axioms QRH.MixedStep.Collision.collisionFactor_norm_le
