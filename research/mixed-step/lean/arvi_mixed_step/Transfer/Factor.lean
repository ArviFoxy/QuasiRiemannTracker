/- Mixed source step, L2 transfer: exact factorization of Collet's tuple
coefficient along the selected block `J`.

Under (S) (no selected prime divides the seed `L`), the invariance of the
whole-column multiplier `F` under the selected product, and on the coprime
locus `D ⊥ n` (`D` the selected product, `n` the residual column), the
original tuple coefficient is the selected weight times the residual
tuple coefficient. Off that locus it vanishes under (Col). -/
import Submissions.arvi_mixed_step.Transfer.Split
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SexticSieve

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Source.High
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Relative primality of ideals of `O` is coprimality. -/
theorem isCoprime_of_isRelPrime {I J : Ideal O} (h : IsRelPrime I J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  exact Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr le_sup_left)
    (Ideal.dvd_iff_le.mpr le_sup_right))

theorem coprime_of_prime_not_dvd {P I : Ideal O} (hP : Prime P) (h : ¬P ∣ I) :
    IsCoprime P I := by
  have hmax : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp hmax).not_le_iff_codisjoint, ← Ideal.dvd_iff_le]
  exact h

/-- (S) for one selected assignment: the seed is coprime to the selected product. -/
theorem seed_coprime (s : Input ι) (J : Finset ι) (L : Ideal O)
    (hS : ∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L) (u : J → Ideal O) (hu : u ∈ selBox s J) :
    IsCoprime L (selProduct J u) := by
  unfold selProduct
  apply IsCoprime.prod_right
  intro j _
  have hmem := Fintype.mem_piFinset.mp hu j
  exact (coprime_of_prime_not_dvd (s.prime j.val (u j) hmem) (hS j.val j.property (u j) hmem)).symm

/-- The selected slot amplitude. -/
def slotAmplitude (s : Input ι) (J : Finset ι) (u : J → Ideal O) : ℂ :=
  ∏ j : J, s.ν j.val (u j) * s.W j.val ((Ideal.absNorm (u j) : ℝ) / s.P j.val)

/-- The selected weight: slot amplitudes, the selected squarefree projector, the
selected part of the frozen-marked coprimality and the selected puncture. -/
def selWeight (s : Input ι) (J : Finset ι) (K R : Ideal O) (u : J → Ideal O) : ℂ :=
  slotAmplitude s J u * squarefreeIndicator (selProduct J u) *
    coprimalityIndicator (selProduct J u) K *
    (if IsCoprime (selProduct J u) R then 1 else 0)

theorem sourceModifier_join (J : Finset ι) (A₁ A₂ Dc : Ideal O) (F : Ideal O → ℂ)
    (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w)) :
    sourceModifier A₁ A₂ Dc F (joinTuple J u w) = sourceModifier A₁ A₂ Dc F w := by
  unfold sourceModifier coupledFactor
  rw [hF]
  rfl

theorem markedSourceModifier_join (J : Finset ι) (A₁ A₂ Dc K : Ideal O) (F : Ideal O → ℂ)
    (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w))
    (hM : IsRelPrime (selProduct J u) (markedProduct w)) :
    markedSourceModifier A₁ A₂ Dc K F (joinTuple J u w) =
      (squarefreeIndicator (selProduct J u) * coprimalityIndicator (selProduct J u) K) *
        markedSourceModifier A₁ A₂ Dc K F w := by
  unfold markedSourceModifier
  rw [sourceModifier_join J A₁ A₂ Dc F u w hF, markedProduct_join,
    show K * (selProduct J u * markedProduct w) = selProduct J u * (K * markedProduct w) by ring,
    squarefreeIndicator_mul]
  have hc : coprimalityIndicator (selProduct J u) (K * markedProduct w) =
      coprimalityIndicator (selProduct J u) K := by
    unfold coprimalityIndicator
    simp only [IsRelPrime.mul_right_iff, hM, and_true]
  rw [hc]
  ring

theorem profile_join (s : Input ι) (J : Finset ι) (R L : Ideal O)
    (u : J → Ideal O) (w : Tuple {i // i ∉ J}) (hL : IsCoprime L (selProduct J u)) :
    profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L (joinTuple J u w) =
      (slotAmplitude s J u * (if IsCoprime (selProduct J u) R then 1 else 0)) *
        profileCoefficient R (residualInput s J).ν (residualInput s J).W (residualInput s J).P
          (residualInput s J).W₁ (residualInput s J).W₂ (residualInput s J).X₁
          (residualInput s J).X₂ (residualInput s J).Y₁ (residualInput s J).Y₂ 1 1 L w := by
  have hp : (∏ i, s.ν i (joinTuple J u w (Sum.inl i)) *
      s.W i ((Ideal.absNorm (joinTuple J u w (Sum.inl i)) : ℝ) / s.P i)) =
      slotAmplitude s J u * ∏ i : {i // i ∉ J}, s.ν i.val (w (Sum.inl i)) *
        s.W i.val ((Ideal.absNorm (w (Sum.inl i)) : ℝ) / s.P i.val) :=
    join_marked_prod J u w (fun j I => s.ν j I * s.W j ((Ideal.absNorm I : ℝ) / s.P j))
  have h1 : (if IsCoprime (selProduct J u * finiteTupleProduct w) R then (1:ℂ) else 0) =
      (if IsCoprime (selProduct J u) R then 1 else 0) *
        (if IsCoprime (finiteTupleProduct w) R then 1 else 0) := by
    by_cases ha : IsCoprime (selProduct J u) R <;>
      by_cases hb : IsCoprime (finiteTupleProduct w) R <;>
      simp [IsCoprime.mul_left_iff, ha, hb]
  have h2 : (if L ∣ selProduct J u * finiteTupleProduct w then (1:ℂ) else 0) =
      (if L ∣ finiteTupleProduct w then 1 else 0) := by
    have hh : L ∣ selProduct J u * finiteTupleProduct w ↔ L ∣ finiteTupleProduct w :=
      ⟨fun h => hL.dvd_of_dvd_mul_left h, fun h => h.trans (dvd_mul_left _ _)⟩
    simp only [hh]
  unfold profileCoefficient
  rw [hp, finiteTupleProduct_join, h1, h2]
  simp only [joinTuple_inr]
  simp only [residualInput_W₁, residualInput_W₂, residualInput_X₁, residualInput_X₂,
    residualInput_Y₁, residualInput_Y₂, residualInput_ν, residualInput_W, residualInput_P]
  ring

/-- Exact factorization on the coprime locus. -/
theorem tuple_factor (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (hL : IsCoprime L (selProduct J u))
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w))
    (hcop : IsCoprime (selProduct J u) (finiteTupleProduct w)) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) =
      selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L w := by
  have hM : IsRelPrime (selProduct J u) (markedProduct w) := by
    apply IsCoprime.isRelPrime
    apply hcop.of_isCoprime_of_dvd_right
    rw [finiteTupleProduct_split w]
    exact dvd_mul_right _ _
  unfold CoupledFirst.tupleCoefficient
  rw [markedSourceModifier_join J A₁ A₂ Dc K F u w hF hM, profile_join s J R L u w hL]
  unfold selWeight
  ring

/-- Nonzero original coefficients force `D ⊥ n` under (Col). -/
theorem nonzero_coprime (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (hne : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
      (joinTuple J u w) ≠ 0)
    (hCol : IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1))) :
    IsCoprime (selProduct J u) (finiteTupleProduct w) := by
  have hmod : markedSourceModifier A₁ A₂ Dc K F (joinTuple J u w) ≠ 0 :=
    left_ne_zero_of_mul hne
  have hsq := (markedSourceModifier_nonzero A₁ A₂ Dc K F _ hmod).1
  rw [markedProduct_join] at hsq
  have hrel := (squarefree_mul_iff.mp hsq).1
  rw [finiteTupleProduct_split w]
  exact IsCoprime.mul_right (isCoprime_of_isRelPrime hrel) hCol

/-- A nonzero tuple coefficient carries its seed. -/
theorem tuple_seed_dvd {κ : Type*} [Fintype κ] (s : Input κ) (modifier : Tuple κ → ℂ)
    (R L : Ideal O) (w : Tuple κ) (hne : CoupledFirst.tupleCoefficient s modifier R L w ≠ 0) :
    L ∣ finiteTupleProduct w := by
  have hp := CoupledFirst.tuple_nonzero s modifier R L w hne
  by_contra hn
  apply hp
  simp only [profileCoefficient, hn, ↓reduceIte, mul_zero]

/-- The factorization with the coprimality mask made explicit, valid for every
pair of parts, under the tuple-level seed condition (S'): on nonzero original
tuples the seed is coprime to the selected product. (S') follows from the
pool-level (S) (`seed_coprime`); it also holds when the seed primes are
excluded from the selected slots by the projectors. -/
theorem tuple_factor_masked_gen (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (hL : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
      (joinTuple J u w) ≠ 0 → IsCoprime L (selProduct J u))
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w))
    (hCol : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
      (joinTuple J u w) ≠ 0 → IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1))) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) =
      selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0) := by
  by_cases hc : IsCoprime (selProduct J u) (finiteTupleProduct w)
  · simp only [hc, ↓reduceIte, mul_one]
    by_cases hLD : IsCoprime L (selProduct J u)
    · exact tuple_factor s J A₁ A₂ Dc K R L F u w hLD hF hc
    · have h0 : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
          (joinTuple J u w) = 0 := by
        by_contra hne
        exact hLD (hL hne)
      have h1 : CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L w = 0 := by
        by_contra hne
        exact hLD (hc.of_isCoprime_of_dvd_right (tuple_seed_dvd _ _ _ _ w hne)).symm
      rw [h0, h1, mul_zero]
  · simp only [hc, ↓reduceIte, mul_zero]
    by_contra hne
    exact hc (nonzero_coprime s J A₁ A₂ Dc K R L F u w hne (hCol hne))

/-- The factorization under the pool-level (S) for this assignment. -/
theorem tuple_factor_masked (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (hL : IsCoprime L (selProduct J u))
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w))
    (hCol : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
      (joinTuple J u w) ≠ 0 → IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1))) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) =
      selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0) :=
  tuple_factor_masked_gen s J A₁ A₂ Dc K R L F u w (fun _ => hL) hF hCol

/-- The pool-level (S) implies the tuple-level (S'). -/
theorem seed_free_of_slots (s : Input ι) (J : Finset ι) (L : Ideal O)
    (hS : ∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L) (v : Tuple ι)
    (hv : v ∈ Fintype.piFinset s.pools) : IsCoprime L (∏ j ∈ J, v (Sum.inl j)) := by
  apply IsCoprime.prod_right
  intro j hj
  have hmem : v (Sum.inl j) ∈ s.slots j := Fintype.mem_piFinset.mp hv (Sum.inl j)
  exact (coprime_of_prime_not_dvd (s.prime j _ hmem) (hS j hj _ hmem)).symm

/-- Residual columns with a nonzero residual coefficient are fifth-power free. -/
theorem residual_power_free (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (w : Tuple {i // i ∉ J})
    (hne : CoupledFirst.tupleCoefficient (residualInput s J)
      (markedSourceModifier A₁ A₂ Dc K F) R L w ≠ 0) :
    Candidate.FourthPower.SexticSieve.PowerFree 5 (finiteTupleProduct w) := by
  have hmod : markedSourceModifier A₁ A₂ Dc K F w ≠ 0 := left_ne_zero_of_mul hne
  obtain ⟨h1, h2⟩ := markedSourceModifier_nonzero A₁ A₂ Dc K F w hmod
  intro P hP hdvd
  apply no_prime_cube_dvd_two_squarefree hP h1 h2
  rw [← finiteTupleProduct_split w]
  exact (pow_dvd_pow P (by norm_num : 3 ≤ 5)).trans hdvd

end
end QRH.MixedStep.Transfer
