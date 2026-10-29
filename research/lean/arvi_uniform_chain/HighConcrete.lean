/-
Exact differences of `σ(ν)` and `R(ν)` in the density, with crude uniform bounds on the difference quotients,
for `ν ∈ [1/2, 3/4]`, `1 < L0`, `B0 ≤ L0`.
-/
import Submissions.arvi_uniform_chain.BindingPair

set_option autoImplicit false

namespace QRH.ArviUniformChain
noncomputable section

theorem yOf_sub (q ν : ℝ) (hq : q ≤ 3/4) (hν : ν ≤ 3/4) :
    yOf q - yOf ν = (ν - q) * (60 / ((25 - 18*q) * (25 - 18*ν))) := by
  have hq' : (25:ℝ) - 18*q ≠ 0 := by linarith
  have hν' : (25:ℝ) - 18*ν ≠ 0 := by linarith
  unfold yOf
  rw [div_sub_div _ _ hq' hν', mul_div_assoc']
  congr 1
  ring

theorem yOf_bounds (ν : ℝ) (h1 : 1/2 ≤ ν) (h2 : ν ≤ 3/4) : 1/23 ≤ yOf ν ∧ yOf ν ≤ 1/8 := by
  unfold yOf
  have hd : (0:ℝ) < 25 - 18*ν := by linarith
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- `σ(q) - σ(ν) = (ν - q)·Kσ` with `Kσ = 60(L0 - B0)/((25-18q)(25-18ν)(L0-1+y_q)(L0-1+y_ν))`. -/
def Ksig (B0 L0 q ν : ℝ) : ℝ :=
  60 * (L0 - B0) / ((25 - 18*q) * (25 - 18*ν) * (L0 - 1 + yOf q) * (L0 - 1 + yOf ν))

theorem sigmaOf_sub {B0 L0 q ν : ℝ} (hL : 1 < L0) (hq1 : 1/2 ≤ q) (hq : q ≤ 3/4)
    (hν1 : 1/2 ≤ ν) (hν : ν ≤ 3/4) :
    sigmaOf B0 L0 q - sigmaOf B0 L0 ν = (ν - q) * Ksig B0 L0 q ν := by
  obtain ⟨yq1, yq2⟩ := yOf_bounds q hq1 hq
  obtain ⟨yν1, yν2⟩ := yOf_bounds ν hν1 hν
  have hAq : L0 - 1 + yOf q ≠ 0 := by linarith
  have hAν : L0 - 1 + yOf ν ≠ 0 := by linarith
  have hq' : (25:ℝ) - 18*q ≠ 0 := by linarith
  have hν' : (25:ℝ) - 18*ν ≠ 0 := by linarith
  have hy := yOf_sub q ν hq hν
  unfold sigmaOf Ksig
  rw [div_sub_div _ _ hAq hAν]
  have : (B0 - 1 + yOf q) * (L0 - 1 + yOf ν) - (L0 - 1 + yOf q) * (B0 - 1 + yOf ν) =
      (yOf q - yOf ν) * (L0 - B0) := by ring
  rw [this, hy]
  field_simp

theorem Ksig_lower {B0 L0 q ν : ℝ} (hL : 1 < L0) (hB : B0 ≤ L0) (hq1 : 1/2 ≤ q) (hq : q ≤ 3/4)
    (hν1 : 1/2 ≤ ν) (hν : ν ≤ 3/4) :
    60 * (L0 - B0) / (256 * (L0 - 7/8)^2) ≤ Ksig B0 L0 q ν := by
  obtain ⟨yq1, yq2⟩ := yOf_bounds q hq1 hq
  obtain ⟨yν1, yν2⟩ := yOf_bounds ν hν1 hν
  unfold Ksig
  have a1 : 0 < 25 - 18*q := by linarith
  have a2 : 0 < 25 - 18*ν := by linarith
  have a3 : 0 < L0 - 1 + yOf q := by linarith
  have a4 : 0 < L0 - 1 + yOf ν := by linarith
  have a5 : 0 ≤ L0 - 7/8 := by linarith
  apply div_le_div_of_nonneg_left (by nlinarith) (by positivity)
  have b1 : 25 - 18*q ≤ 16 := by linarith
  have b2 : 25 - 18*ν ≤ 16 := by linarith
  have b3 : L0 - 1 + yOf q ≤ L0 - 7/8 := by linarith
  have b4 : L0 - 1 + yOf ν ≤ L0 - 7/8 := by linarith
  calc (25 - 18*q) * (25 - 18*ν) * (L0 - 1 + yOf q) * (L0 - 1 + yOf ν)
      ≤ 16 * 16 * (L0 - 7/8) * (L0 - 7/8) := by gcongr
    _ = 256 * (L0 - 7/8)^2 := by ring

theorem Ksig_upper {B0 L0 q ν : ℝ} (hL : 1 < L0) (hB : B0 ≤ L0) (hq1 : 1/2 ≤ q) (hq : q ≤ 3/4)
    (hν1 : 1/2 ≤ ν) (hν : ν ≤ 3/4) :
    Ksig B0 L0 q ν ≤ 60 * (L0 - B0) / ((23/2)^2 * (L0 - 22/23)^2) := by
  obtain ⟨yq1, yq2⟩ := yOf_bounds q hq1 hq
  obtain ⟨yν1, yν2⟩ := yOf_bounds ν hν1 hν
  unfold Ksig
  apply div_le_div_of_nonneg_left (by nlinarith) (by nlinarith)
  have b1 : 23/2 ≤ 25 - 18*q := by linarith
  have b2 : 23/2 ≤ 25 - 18*ν := by linarith
  have b3 : L0 - 22/23 ≤ L0 - 1 + yOf q := by linarith
  have b4 : L0 - 22/23 ≤ L0 - 1 + yOf ν := by linarith
  have c3 : 0 ≤ L0 - 22/23 := by linarith
  calc (23/2:ℝ)^2 * (L0 - 22/23)^2 = (23/2) * (23/2) * (L0 - 22/23) * (L0 - 22/23) := by ring
    _ ≤ (25 - 18*q) * (25 - 18*ν) * (L0 - 1 + yOf q) * (L0 - 1 + yOf ν) := by gcongr

theorem xOf_sub (q ν : ℝ) (hq : q ≤ 3/4) (hν : ν ≤ 3/4) :
    xOf q - xOf ν = (ν - q) * (60 / ((20 - 12*q) * (20 - 12*ν))) := by
  have hq' : (20:ℝ) - 12*q ≠ 0 := by linarith
  have hν' : (20:ℝ) - 12*ν ≠ 0 := by linarith
  unfold xOf
  rw [div_sub_div _ _ hq' hν', mul_div_assoc']
  congr 1
  ring

theorem xOf_bounds (ν : ℝ) (h1 : 1/2 ≤ ν) (h2 : ν ≤ 3/4) : 1/22 ≤ xOf ν ∧ xOf ν ≤ 1/7 := by
  unfold xOf
  have hd : (0:ℝ) < 20 - 12*ν := by linarith
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- `R(ν) - R(q) = (ν - q)·KR` with `KR = 60(L0-1)(L0-B0)/((20-12q)(20-12ν)(L0-1+x_q L0)(L0-1+x_ν L0))`. -/
def KR (B0 L0 q ν : ℝ) : ℝ :=
  60 * (L0 - 1) * (L0 - B0) / ((20 - 12*q) * (20 - 12*ν) * (L0 - 1 + xOf q * L0) * (L0 - 1 + xOf ν * L0))

theorem ROf_sub {B0 L0 q ν : ℝ} (hL : 1 < L0) (hq1 : 1/2 ≤ q) (hq : q ≤ 3/4)
    (hν1 : 1/2 ≤ ν) (hν : ν ≤ 3/4) :
    ROf B0 L0 ν - ROf B0 L0 q = (ν - q) * KR B0 L0 q ν := by
  obtain ⟨xq1, xq2⟩ := xOf_bounds q hq1 hq
  obtain ⟨xν1, xν2⟩ := xOf_bounds ν hν1 hν
  have hAq : L0 - 1 + xOf q * L0 ≠ 0 := by nlinarith
  have hAν : L0 - 1 + xOf ν * L0 ≠ 0 := by nlinarith
  have hq' : (20:ℝ) - 12*q ≠ 0 := by linarith
  have hν' : (20:ℝ) - 12*ν ≠ 0 := by linarith
  have hx := xOf_sub q ν hq hν
  unfold ROf KR
  rw [div_sub_div _ _ hAν hAq]
  have : (L0 - 1 + xOf ν * B0) * (L0 - 1 + xOf q * L0) - (L0 - 1 + xOf ν * L0) * (L0 - 1 + xOf q * B0) =
      (L0 - 1) * (L0 - B0) * (xOf q - xOf ν) := by ring
  rw [this, hx]
  field_simp

theorem KR_nonneg {B0 L0 q ν : ℝ} (hL : 1 < L0) (hB : B0 ≤ L0) (hq1 : 1/2 ≤ q) (hq : q ≤ 3/4)
    (hν1 : 1/2 ≤ ν) (hν : ν ≤ 3/4) : 0 ≤ KR B0 L0 q ν := by
  obtain ⟨xq1, xq2⟩ := xOf_bounds q hq1 hq
  obtain ⟨xν1, xν2⟩ := xOf_bounds ν hν1 hν
  unfold KR
  apply div_nonneg
  · have : 0 ≤ L0 - 1 := by linarith
    have : 0 ≤ L0 - B0 := by linarith
    positivity
  · have a1 : 0 ≤ 20 - 12*q := by linarith
    have a2 : 0 ≤ 20 - 12*ν := by linarith
    have a3 : 0 ≤ L0 - 1 + xOf q * L0 := by nlinarith
    have a4 : 0 ≤ L0 - 1 + xOf ν * L0 := by nlinarith
    positivity

theorem KR_upper {B0 L0 q ν : ℝ} (hL : 1 < L0) (hB : B0 ≤ L0) (hq1 : 1/2 ≤ q) (hq : q ≤ 3/4)
    (hν1 : 1/2 ≤ ν) (hν : ν ≤ 3/4) : KR B0 L0 q ν ≤ 60 * (L0 - B0) / (121 * (L0 - 1)) := by
  obtain ⟨xq1, xq2⟩ := xOf_bounds q hq1 hq
  obtain ⟨xν1, xν2⟩ := xOf_bounds ν hν1 hν
  have hL1 : 0 < L0 - 1 := by linarith
  have b1 : 11 ≤ 20 - 12*q := by linarith
  have b2 : 11 ≤ 20 - 12*ν := by linarith
  have b3 : L0 - 1 ≤ L0 - 1 + xOf q * L0 := by nlinarith
  have b4 : L0 - 1 ≤ L0 - 1 + xOf ν * L0 := by nlinarith
  have hden : 121 * (L0 - 1) * (L0 - 1) ≤
      (20 - 12*q) * (20 - 12*ν) * (L0 - 1 + xOf q * L0) * (L0 - 1 + xOf ν * L0) := by
    calc 121 * (L0 - 1) * (L0 - 1) = 11 * 11 * (L0 - 1) * (L0 - 1) := by ring
      _ ≤ _ := by gcongr
  unfold KR
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hn : 0 ≤ 60 * (L0 - B0) := by linarith
  calc 60 * (L0 - 1) * (L0 - B0) * (121 * (L0 - 1)) = 60 * (L0 - B0) * (121 * (L0 - 1) * (L0 - 1)) := by ring
    _ ≤ 60 * (L0 - B0) * ((20 - 12*q) * (20 - 12*ν) * (L0 - 1 + xOf q * L0) * (L0 - 1 + xOf ν * L0)) :=
        mul_le_mul_of_nonneg_left hden hn

theorem ROf_le_one {B0 L0 ν : ℝ} (hL : 1 < L0) (hB : B0 ≤ L0) (hν1 : 1/2 ≤ ν) (hν : ν ≤ 3/4) :
    ROf B0 L0 ν ≤ 1 := by
  obtain ⟨x1, x2⟩ := xOf_bounds ν hν1 hν
  unfold ROf
  rw [div_le_one (by nlinarith)]
  nlinarith

theorem ROf_ge_half {B0 L0 ν : ℝ} (hL : 1 < L0) (hL3 : L0 ≤ 3) (hB0 : 22/23 ≤ B0) (hν1 : 1/2 ≤ ν)
    (hν : ν ≤ 3/4) : 1/2 ≤ ROf B0 L0 ν := by
  obtain ⟨x1, x2⟩ := xOf_bounds ν hν1 hν
  unfold ROf
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

theorem C12_nonneg {B0 L0 ν : ℝ} (hL : 1 < L0) (hL3 : L0 ≤ 3) (hB0 : 22/23 ≤ B0) (hν1 : 1/2 ≤ ν)
    (hν : ν ≤ 3/4) : 0 ≤ C12 B0 L0 ν := by
  have := ROf_ge_half hL hL3 hB0 hν1 hν
  unfold C12
  nlinarith

theorem C12_mono {B0 L0 q ν : ℝ} (hL : 1 < L0) (hL3 : L0 ≤ 3) (hB0 : 22/23 ≤ B0) (hB : B0 ≤ L0)
    (hq1 : 1/2 ≤ q) (hqν : q ≤ ν) (hν : ν ≤ 3/4) : C12 B0 L0 q ≤ C12 B0 L0 ν := by
  have hR := ROf_sub (B0 := B0) hL hq1 (le_trans hqν hν) (le_trans hq1 hqν) hν
  have hK := KR_nonneg hL hB hq1 (le_trans hqν hν) (le_trans hq1 hqν) hν
  have hRh := ROf_ge_half hL hL3 hB0 (le_trans hq1 hqν) hν
  have hd : 0 ≤ ν - q := sub_nonneg.mpr hqν
  unfold C12
  have e : 6*ν*ROf B0 L0 ν - ν - 1 - (6*q*ROf B0 L0 q - q - 1) =
      (ν - q) * (6 * ROf B0 L0 ν - 1 + 6*q*KR B0 L0 q ν) := by
    have : ROf B0 L0 q = ROf B0 L0 ν - (ν - q) * KR B0 L0 q ν := by linarith
    rw [this]; ring
  have : 0 ≤ (ν - q) * (6 * ROf B0 L0 ν - 1 + 6*q*KR B0 L0 q ν) := by
    apply mul_nonneg hd; nlinarith
  linarith

end
end QRH.ArviUniformChain
