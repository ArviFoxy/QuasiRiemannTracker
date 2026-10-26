/- Mixed source step, L2 transfer: removing the seed hypothesis (S) by
supplier splitting.

When selected primes supply part of the (squarefree) seed `L`, the residual
seed is `L / gcd(L, D)`: `supplied J L u` is the product of the selected
primes dividing `L`, and `residualSeed J L u` its cofactor in `L`. On the
coprime locus `D ⊥ n`, `L ∣ D·n ↔ residualSeed ∣ n`, so the original tuple
coefficient factors with the assignment-dependent residual seed. -/
import Submissions.arvi_mixed_step.Transfer.Factor

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

/-- A nonzero selected weight forces distinct selected primes. -/
theorem sel_injective_of_weight (s : Input ι) (J : Finset ι) (K R : Ideal O) (u : J → Ideal O)
    (hu : u ∈ selBox s J) (hw : selWeight s J K R u ≠ 0) : Function.Injective u := by
  have hsq : Squarefree (selProduct J u) := by
    by_contra hn
    apply hw
    simp only [selWeight, squarefreeIndicator, hn, ↓reduceIte, mul_zero, zero_mul]
  intro i j hij
  by_contra hne
  have h : u i * u j ∣ selProduct J u := by
    unfold selProduct
    rw [← Finset.mul_prod_erase Finset.univ u (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) u
        (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  rw [hij] at h
  exact (s.prime j.val (u j) (Fintype.mem_piFinset.mp hu j)).not_isUnit (hsq (u j) h)

/-- The part of the seed supplied by the selected primes. -/
def supplied (J : Finset ι) (L : Ideal O) (u : J → Ideal O) : Ideal O :=
  ∏ j ∈ Finset.univ.filter (fun j => u j ∣ L), u j

/-- The residual seed `L / supplied`. -/
def residualSeed (J : Finset ι) (L : Ideal O) (u : J → Ideal O) : Ideal O :=
  if h : supplied J L u ∣ L then Classical.choose h else L

theorem residualSeed_spec (J : Finset ι) (L : Ideal O) (u : J → Ideal O)
    (h : supplied J L u ∣ L) : L = supplied J L u * residualSeed J L u := by
  have hc := Classical.choose_spec h
  unfold residualSeed
  simp only [h, ↓reduceDIte]
  exact hc

theorem supplied_dvd_sel (J : Finset ι) (L : Ideal O) (u : J → Ideal O) :
    supplied J L u ∣ selProduct J u :=
  Finset.prod_dvd_prod_of_subset _ _ u (Finset.filter_subset _ _)

theorem supplied_dvd_seed (s : Input ι) (J : Finset ι) (L : Ideal O) (u : J → Ideal O)
    (hu : u ∈ selBox s J) (hinj : Function.Injective u) : supplied J L u ∣ L := by
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    have hpi := s.prime i.val (u i) (Fintype.mem_piFinset.mp hu i)
    have hpj := s.prime j.val (u j) (Fintype.mem_piFinset.mp hu j)
    apply coprime_of_prime_not_dvd hpi
    intro hd
    exact hij (hinj ((prime_dvd_prime_iff_eq hpi hpj).mp hd))
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

theorem residualSeed_dvd (s : Input ι) (J : Finset ι) (L : Ideal O) (u : J → Ideal O)
    (hu : u ∈ selBox s J) (hinj : Function.Injective u) : residualSeed J L u ∣ L := by
  exact Dvd.intro_left (supplied J L u)
    (residualSeed_spec J L u (supplied_dvd_seed s J L u hu hinj)).symm

theorem residualSeed_coprime (s : Input ι) (J : Finset ι) (L : Ideal O) (hL : Squarefree L)
    (u : J → Ideal O) (hu : u ∈ selBox s J) (hinj : Function.Injective u) :
    IsCoprime (residualSeed J L u) (selProduct J u) := by
  have hspec := residualSeed_spec J L u (supplied_dvd_seed s J L u hu hinj)
  unfold selProduct
  apply IsCoprime.prod_right
  intro j _
  have hpj := s.prime j.val (u j) (Fintype.mem_piFinset.mp hu j)
  apply (coprime_of_prime_not_dvd hpj _).symm
  intro hd
  by_cases hj : u j ∣ L
  · have hsup : u j ∣ supplied J L u :=
      Finset.dvd_prod_of_mem u (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
    have hsq : u j * u j ∣ L := by
      rw [hspec]
      exact mul_dvd_mul hsup hd
    exact hpj.not_isUnit (hL (u j) hsq)
  · exact hj (hd.trans (residualSeed_dvd s J L u hu hinj))

/-- The seed condition moves to the residual seed. -/
theorem seed_iff (L L' S D n : Ideal O) (hS : S ∣ D) (hL : L = S * L') (hc : IsCoprime L' D) :
    L ∣ D * n ↔ L' ∣ n := by
  constructor
  · intro h
    have h' : L' ∣ D * n := (dvd_mul_left L' S).trans (hL ▸ h)
    exact hc.dvd_of_dvd_mul_left h'
  · intro h
    rw [hL]
    exact mul_dvd_mul hS h

/-- The seed mask factors out of a tuple coefficient. -/
theorem tupleCoefficient_seed {κ : Type*} [Fintype κ] (s : Input κ) (modifier : Tuple κ → ℂ)
    (R L : Ideal O) (v : Tuple κ) :
    CoupledFirst.tupleCoefficient s modifier R L v =
      CoupledFirst.tupleCoefficient s modifier R 1 v *
        (if L ∣ finiteTupleProduct v then 1 else 0) := by
  unfold CoupledFirst.tupleCoefficient profileCoefficient
  simp only [one_dvd, ↓reduceIte, mul_one]
  ring

/-- Factorization with the assignment-dependent residual seed (no (S)). -/
theorem tuple_factor_masked_supplier (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (hLsq : Squarefree L) (u : J → Ideal O) (hu : u ∈ selBox s J)
    (w : Tuple {i // i ∉ J})
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w))
    (hCol : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
      (joinTuple J u w) ≠ 0 → IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1))) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) =
      selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R (residualSeed J L u) w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0) := by
  by_cases hc : IsCoprime (selProduct J u) (finiteTupleProduct w)
  · simp only [hc, ↓reduceIte, mul_one]
    have h1 := tuple_factor s J A₁ A₂ Dc K R 1 F u w isCoprime_one_left hF hc
    rw [tupleCoefficient_seed, h1, finiteTupleProduct_join,
      tupleCoefficient_seed (residualInput s J) _ R (residualSeed J L u)]
    by_cases hw : selWeight s J K R u = 0
    · rw [hw]
      ring
    · have hinj := sel_injective_of_weight s J K R u hu hw
      have hiff := seed_iff L (residualSeed J L u) (supplied J L u) (selProduct J u)
        (finiteTupleProduct w) (supplied_dvd_sel J L u)
        (residualSeed_spec J L u (supplied_dvd_seed s J L u hu hinj))
        (residualSeed_coprime s J L hLsq u hu hinj)
      simp only [hiff]
      ring
  · simp only [hc, ↓reduceIte, mul_zero]
    by_contra hne
    exact hc (nonzero_coprime s J A₁ A₂ Dc K R L F u w hne (hCol hne))

end
end QRH.MixedStep.Transfer
