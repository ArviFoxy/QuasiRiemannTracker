/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: third stop-rule report (the extraction gains of a second label), scalar fix.

MISMATCH. One second label `x` (genuine common factor `G = C₂ = D₂`, unit set `U`, dyadic
block `n`, second Möbius divisor `t₂ = L`, ray character) contributes to the raw C-side Gauss
energy the block `outerScalar · normalizer · normalizedBlock`. OAI bounds it
(`actual_block_from_supported_envelopes`, through `whole_kernel_restricted_child_bound`) by
the window product of the two one-sided label energies `e_L, e_R` (masked residual energies
over `residualPool G`, columns `L ∣ I`). Here
  `outerScalar = K/(√N(C₂)√N(D₂)√dyad₂√dyad₃) ≍ Z^k·N(G)/X`, `normalizer/N(G) ≤ 1/N(U)`,
and the one-sided energies carry the EXTRACTION GAINS `e ≲ X·Z^H/(N(G)·N(t₂))` (FP's
per-label budget is `rawBudget … /N(G)` and `E/N(t₂)`). So with
  `E_x := N(G)·N(t₂)·(Z^k/X²)·e_x`,  `w_x := ρ·(normalizer/N(G))/N(t₂)`
the raw nonfixed side is `≍ X·∑_x w_x √(E_{L,x} E_{R,x})`, uniformly in the labels, and
`w_x` satisfies the fibre condition (`∑_{t₂} 1/N(t₂)`, divisor-bounded `G ∣ y`).

WP-H's frame `gFrame` has the weight `gWeight = ρ‖prefactor‖/N(t₂)` but the energy
`gEnergy = (Z^k/X²)·e` WITHOUT the factor `N(G)·N(t₂)`, and `grouped_at` discards exactly
these gains (`labelMass_le`: `labelMass … (1/2) ≤ C Z^ε X`, i.e. `N(G)^{-1/2}N(t₂)^{-1/2}/pairNorm`
dropped). Seam B therefore bounds `∑ w_x·(Z^k/X²)·e_x`, which is smaller than the needed
`∑ w_x·E_x` by the non-uniform factor `N(G)·N(t₂)` per label; it cannot feed `hwindow`
(no choice of `prefactor` helps: putting `N(G)N(t₂)` into the weight breaks the fibre
condition, since `∑_{G ∣ y} N(G)` and `∑_{t₂} 1` are powers of `Z`).

FIX (for WP-H, local). Redefine `gEnergy η r x v := N(x.G)·N(x.D)·r.norm·rawEnergy` and, in
`grouped_at`, call the label reduction with a small `δ` instead of `1/2`; then
`labelMass_extracted` below gives `N(G)N(t₂)·labelMass ≤ C·Z^{ε+3δB}·X` under the mask cap
(`N(G) ≤ Z^{2B}`, `N(t₂) ≤ Z^B`, from `Fits.cap`, `G` cube-free, `t₂` squarefree), so with
`δ := ε/(48·max 1 B)` Seam B keeps its right-hand side up to `Z^{ε/16}`. -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.Label

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree.Second.Concrete
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree.Packet.Reduce

theorem one_le_absNorm' (I : Ideal OAI.SevenEighths.HeckeFamily.O) (hI : I ≠ 0) :
    (1:ℝ) ≤ (I.absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- **The extraction gains are kept by the label mass.** -/
theorem labelMass_extracted {α : Type*} [Fintype α] (C Z ε δ B : ℝ) (hC : 0 ≤ C) (hZ : 1 ≤ Z)
    (hδ : 0 ≤ δ) (w : α → ℝ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (G D : Ideal OAI.SevenEighths.HeckeFamily.O) (hG : G ≠ 0) (hD : D ≠ 0)
    (d : Ideal OAI.SevenEighths.HeckeFamily.O × Ideal OAI.SevenEighths.HeckeFamily.O)
    (hd₁ : d.1 ≠ 0) (hd₂ : d.2 ≠ 0)
    (hGB : (G.absNorm : ℝ) ≤ Z^(2*B)) (hDB : (D.absNorm : ℝ) ≤ Z^B) :
    ((G.absNorm : ℝ) * (D.absNorm : ℝ)) * labelMass C Z ε δ w X₁ X₂ G D d ≤
      C * Z^(ε + 3*δ*B) * (X₁ * X₂ * ∏ i, Z^(w i)) := by
  have hZ0 : 0 < Z := by linarith
  have hG1 := one_le_absNorm' G hG
  have hD1 := one_le_absNorm' D hD
  have hp : (1:ℝ) ≤ QRH.Record1252270103KernelMass.pairNorm d := by
    unfold QRH.Record1252270103KernelMass.pairNorm
    have := one_le_absNorm' _ hd₁
    have := one_le_absNorm' _ hd₂
    nlinarith
  have hvol : 0 < X₁ * X₂ * ∏ i, Z^(w i) :=
    mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos hZ0 _)
  have hGd : (G.absNorm : ℝ)^δ ≤ Z^(2*B*δ) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by linarith) hGB hδ
  have hDd : (D.absNorm : ℝ)^δ ≤ Z^(B*δ) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by linarith) hDB hδ
  have hval : ((G.absNorm : ℝ) * (D.absNorm : ℝ)) * labelMass C Z ε δ w X₁ X₂ G D d =
      C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) * ((G.absNorm : ℝ)^δ * (D.absNorm : ℝ)^δ) /
        QRH.Record1252270103KernelMass.pairNorm d := by
    unfold labelMass
    field_simp
  rw [hval, div_le_iff₀ (by linarith)]
  have hZe : Z^(ε + 3*δ*B) = Z^ε * (Z^(2*B*δ) * Z^(B*δ)) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; ring_nf
  have hprod : (G.absNorm : ℝ)^δ * (D.absNorm : ℝ)^δ ≤ Z^(2*B*δ) * Z^(B*δ) :=
    mul_le_mul hGd hDd (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hZ0.le _)
  have hA : 0 ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hZ0.le _)) hvol.le
  have hB0 : 0 ≤ Z^(2*B*δ) * Z^(B*δ) :=
    mul_nonneg (Real.rpow_nonneg hZ0.le _) (Real.rpow_nonneg hZ0.le _)
  calc C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) * ((G.absNorm : ℝ)^δ * (D.absNorm : ℝ)^δ)
      ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) * (Z^(2*B*δ) * Z^(B*δ)) :=
        mul_le_mul_of_nonneg_left hprod hA
    _ ≤ C * Z^ε * (X₁ * X₂ * ∏ i, Z^(w i)) * (Z^(2*B*δ) * Z^(B*δ)) *
          QRH.Record1252270103KernelMass.pairNorm d :=
        le_mul_of_one_le_right (mul_nonneg hA hB0) hp
    _ = C * Z^(ε + 3*δ*B) * (X₁ * X₂ * ∏ i, Z^(w i)) * QRH.Record1252270103KernelMass.pairNorm d := by
        rw [hZe]; ring

end
end QRH.SilDensitySplit.CubeFree.Second.Concrete
