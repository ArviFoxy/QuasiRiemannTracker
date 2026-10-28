/- Adapted from Collet's Cycle61 density proof (Apache-2.0), widening only the lower zero-bin endpoint from 33/40 to 3/4. AI-assisted generalization, 2026-10-28. Conditional on the preprint seven-eighths theorem through incumbent_beta_upper. -/
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint
import Submissions.density_batch.DensityWide.ActualZeros

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical ComplexConjugate
open Set
namespace SevenEighths.LocalMoment.BatchDensity
open OAI.SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open CenteredMomentNaturalRowSource HeckeFiniteDeletion
local notation "O" => HeckeFamily.O

theorem natural_zero_to_literal_dictionary {Label : Type*}
    (base : Label → Character) (reverse : Label → Bool) (a T : ℝ)
    (ha : 3/4 ≤ a) (u : NonzeroElement)
    (hz : naturalActualZeroRow base reverse a T u) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases base).data reverse a T u := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  let χ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
  let ψ := if reverse j then ((momentData (base j)).character u).inverse else (momentData (base j)).character u
  have hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I := by
    intro I
    cases hr : reverse j
    · simpa only [χ, ψ, hr, Bool.false_eq_true, ite_false, naturalRawFamily] using natural_raw_coefficients (base j) u I
    · dsimp [χ, ψ]
      simp only [hr, ite_true]
      rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj]
      dsimp only [naturalRawFamily]
      rw [natural_raw_coefficients]
  have hh := positive_zeros_eq_of_coefficients χ ψ hc (show 0 < s.re by linarith) hpole
  exact ⟨j, s, hh.1.mp hz, hh.2, hs, ht⟩

/-- Lemma 2.1, directly for the bounded-conductor natural characters with
coefficients `c_η(I) s_{m₀⁶u}(I)`, including every raw integer row and either
whole-character orientation. The dictionary is fixed before the scale. -/
theorem fixed_natural_dictionary_raw_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 3/4 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ naturalActualZeroRow base reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_dictionary_actual_raw_zero_density
    (FixedUnmarkedDictionary.ofBases base) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  exact hb reverse a T ha ha' hT H hH rows (fun u hu =>
    ⟨(hrows u hu).1, natural_zero_to_literal_dictionary base reverse a T ha u (hrows u hu).2⟩)

#print axioms fixed_natural_dictionary_raw_density

theorem fixed_natural_dictionary_free_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 3/4 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ Y : ℝ, 1 ≤ Y → ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ Y ∧
        naturalActualZeroRow base reverse a T ⟨u.val, u.property.1⟩) →
        (rows.card : ℝ) ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_natural_dictionary_raw_density base loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT Y hY rows hrows
  let embedRow : FreeRow → NonzeroFrequency := fun u => ⟨u.val, u.property.1⟩
  have hinj : Function.Injective embedRow := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun z : NonzeroFrequency => z.val) h
  have hcard : (rows.image embedRow).card = rows.card := Finset.card_image_of_injective rows hinj
  have hr : ∀ u ∈ rows.image embedRow, rawFrequencyNorm u ≤ Y ∧ naturalActualZeroRow base reverse a T u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hrows v hv
  have hh := hb reverse a T ha ha' hT Y (zero_lt_one.trans_le hY) (rows.image embedRow) hr
  simpa only [hcard] using hh

#print axioms fixed_natural_dictionary_free_density
end SevenEighths.LocalMoment.BatchDensity
end
end OAI
