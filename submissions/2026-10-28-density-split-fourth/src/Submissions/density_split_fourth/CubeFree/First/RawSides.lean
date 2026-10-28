/- Copyright (c) 2026 Sil. Apache-2.0.
Seam 0 on the forked cube-free definitions: the per-side summed instance and the bridge from
FP's per-divisor `RawSideBounds` (moved here from `First/RawSidesContract.lean`, WP-K2a).

The step itself uses the BALANCED instance `Second.Concrete.BalancedSummedRawSideBounds`
(coordinator decision: CF (3.1)/(6.4) only bound the product of the two sides). The per-side
instance below is kept for the per-divisor bridge `RawSideBounds.toSummed`, which shows that
FP-style per-divisor bounds (budget `E/N(u)`) imply it after paying the artificial mass.
Every definition is the fork (`CubeFree.FP.*`, `Second.Concrete.concreteJointBudget`). -/
import Submissions.density_split_fourth.CubeFree.Second.Concrete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.First
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily
open FP.MixedPrincipalPair FP.MixedFirstPhysicalApplication FP.RepairedFirstRawSides
open Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Per-side summed Seam 0 on the forked definitions (the budget of each side separately). -/
def PerSideSummedRawSideBounds (s : Source ι a b) (ha : 0 < a) (η : Character)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (KL KR A Z loss : ℝ) (J : ℕ) : Prop :=
  SummedRawSideBounds (concreteArtificial s C D hD.1)
    (rawEnergy s ha D C hC) (rawEnergy s ha C D hD)
    (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).left)
    (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).right)
    (fun τ => concreteJointBudget s τ C D A Z loss) (fun τ => concreteJointBudget s τ D C A Z loss)
    KL KR J

theorem one_div_le_moebius_div {u : Id} (hu : (UniqueFactorizationMonoid.moebius u : ℂ) ≠ 0) :
    1/(u.absNorm:ℝ) ≤ ‖(UniqueFactorizationMonoid.moebius u : ℂ)‖/(u.absNorm:ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h0 : UniqueFactorizationMonoid.moebius u ≠ 0 := by exact_mod_cast hu
  rw [Complex.norm_intCast]
  have := Int.one_le_abs h0
  rw [← Int.cast_abs]
  exact_mod_cast this

/-- FP's per-divisor bounds (budget `E/N(u)`) imply the summed bounds, paying the
artificial-divisor mass `∑_u |μ(u)|/N(u) ≤ Cm Z^εm`. -/
theorem RawSideBounds.toSummed {s : Source ι a b} {ha : 0 < a} {η : Character}
    {C D : Id} {hC : Supported C} {hD : Supported D} {E : Finset (CommonIndex C D)}
    {KL KR A Z loss : ℝ} {J : ℕ} (Cm εm : ℝ)
    (h : RawSideBounds s ha η C D hC hD E KL KR A Z loss J)
    (hmass : ∑ u ∈ artificialDivisors s C D hD.1,
      ‖(UniqueFactorizationMonoid.moebius u : ℂ)‖/(u.absNorm:ℝ) ≤ Cm*Z^εm) (hA : 0 ≤ A) (hZ : 0 < Z) :
    PerSideSummedRawSideBounds s ha η C D hC hD E KL KR (A*Cm) Z (loss+εm) J := by
  have hbase : ∀ (τ : Character) (G opp : Id),
      Cm*Z^εm*concreteJointBudget s τ G opp A Z loss = concreteJointBudget s τ G opp (A*Cm) Z (loss+εm) := by
    intro τ G opp
    unfold concreteJointBudget
    rw [Real.rpow_add hZ]; ring
  have hmass' : ∑ u ∈ concreteArtificial s C D hD.1, 1/(u.absNorm:ℝ) ≤ Cm*Z^εm := by
    refine le_trans ?_ hmass
    unfold concreteArtificial
    calc ∑ u ∈ (artificialDivisors s C D hD.1).filter
            (fun u => (UniqueFactorizationMonoid.moebius u : ℂ) ≠ 0), 1/(u.absNorm:ℝ)
        ≤ ∑ u ∈ (artificialDivisors s C D hD.1).filter
            (fun u => (UniqueFactorizationMonoid.moebius u : ℂ) ≠ 0),
              ‖(UniqueFactorizationMonoid.moebius u : ℂ)‖/(u.absNorm:ℝ) :=
          Finset.sum_le_sum (fun u hu => one_div_le_moebius_div (Finset.mem_filter.mp hu).2)
      _ ≤ ∑ u ∈ artificialDivisors s C D hD.1,
              ‖(UniqueFactorizationMonoid.moebius u : ℂ)‖/(u.absNorm:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun u _ _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have hper : PerDivisorRawSideBounds (concreteArtificial s C D hD.1)
      (rawEnergy s ha D C hC) (rawEnergy s ha C D hD)
      (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).left)
      (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).right)
      (fun τ => concreteJointBudget s τ C D A Z loss) (fun τ => concreteJointBudget s τ D C A Z loss)
      (fun u => 1/(u.absNorm:ℝ)) KL KR J := by
    intro u hu χ ξ
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
    obtain ⟨h1, h2⟩ := h u hu1 hu2 χ ξ
    refine ⟨fun v => (h1 v).trans_eq ?_, fun v => (h2 v).trans_eq ?_⟩ <;>
      · unfold sideBudget concreteJointBudget; ring
  have hs := PerDivisorRawSideBounds.toSummed
    (fun τ => concreteJointBudget_nonneg s τ C D A Z loss hA hZ.le)
    (fun τ => concreteJointBudget_nonneg s τ D C A Z loss hA hZ.le) hmass' hper
  unfold PerSideSummedRawSideBounds
  refine SummedRawSideBounds.mono_budget (fun τ => ?_) (fun τ => ?_) hs
  · exact (hbase τ C D).le
  · exact (hbase τ D C).le

end
end QRH.DensitySplitThird.CubeFree.First
