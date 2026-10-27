/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M provider, part (a): the renormalized residual.

An allocated residual keeps the root ordinary lengths `X_i, Y_i` and carries the extracted ordinary
part of the first common factor in the prefix `d = prefixPair`. For the second-step frame the
column volume must be the EXTRACTED one, `X₁X₂/N(d₁)N(d₂)·∏P`. `renorm s` moves the prefix into the
lengths: `d' = (1,1)`, `X'_i = X_i/N(d_i)`, `Y'_i = Y_i/N(d_i)`, `U'_i = U_i/N(d_i)`,
`T' = T/N(d₁)N(d₂)`, `L' = L/N(d₁)N(d₂)`. The ordinary pools and windows depend only on
`N(d_i·v)/X_i`, so the source is literally the same:

* `tuplePools_renorm`, `sourceColumns_renorm`, `sourceCoefficient_renorm`, `S0_renorm`;
* `sourceNormCap_renorm` (the norm cap is unchanged), `sourceVolume_renorm`
  (`V' = V/N(d₁)N(d₂)`). -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteAssemblyAvgBounds2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.SilDensitySplit.CubeFree.Second.Provider
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiteralAllocation
open MixedTupleRows MixedHeightEnergy MixedOriginalNormCap MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete CenteredMomentRectangle
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The norm of an ideal as a real number. -/
def nrm (I : Id) : ℝ := (Ideal.absNorm I : ℝ)

theorem nrm_one_le {I : Id} (h : I ≠ 0) : 1 ≤ nrm I := by
  unfold nrm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h)

theorem nrm_pos {I : Id} (h : I ≠ 0) : 0 < nrm I := zero_lt_one.trans_le (nrm_one_le h)

theorem nrm_mul (I J : Id) : nrm (I * J) = nrm I * nrm J := by
  unfold nrm; rw [map_mul, Nat.cast_mul]

/-- **The renormalized source.** -/
def renorm (s : Source ι a b) : Source ι a b where
  S := s.S
  H := s.H
  pool := s.pool
  d := (1, 1)
  hd := ⟨one_ne_zero, one_ne_zero⟩
  B := s.B
  hB := s.hB
  G := s.G
  R := s.R
  Fhole := s.Fhole
  hprod := s.hprod
  hR := s.hR
  hFhole := s.hFhole
  ν := s.ν
  Wslot := s.Wslot
  P := s.P
  M := s.M
  W₁ := s.W₁
  W₂ := s.W₂
  hs₁ := s.hs₁
  hs₂ := s.hs₂
  t₁ := s.t₁
  t₂ := s.t₂
  X₁ := s.X₁ / nrm s.d.1
  X₂ := s.X₂ / nrm s.d.2
  Y₁ := s.Y₁ / nrm s.d.1
  Y₂ := s.Y₂ / nrm s.d.2
  U₁ := s.U₁ / nrm s.d.1
  U₂ := s.U₂ / nrm s.d.2
  T := s.T / (nrm s.d.1 * nrm s.d.2)
  L := s.L / (nrm s.d.1 * nrm s.d.2)
  hL := div_pos s.hL (mul_pos (nrm_pos s.hd.1) (nrm_pos s.hd.2))
  hX₁ := by
    have h1 := nrm_pos s.hd.1; have h2 := nrm_one_le s.hd.2
    rw [div_le_div_iff₀ (by positivity) h1]
    have hx : 0 ≤ s.X₁ := (s.hL.trans_le s.hX₁).le
    have e1 := mul_le_mul_of_nonneg_right s.hX₁ h1.le
    have e2 : s.X₁ * nrm s.d.1 ≤ s.X₁ * nrm s.d.1 * nrm s.d.2 :=
      le_mul_of_one_le_right (by positivity) h2
    nlinarith
  hX₂ := by
    have h1 := nrm_one_le s.hd.1; have h2 := nrm_pos s.hd.2
    rw [div_le_div_iff₀ (by positivity) h2]
    have hx : 0 ≤ s.X₂ := (s.hL.trans_le s.hX₂).le
    have e1 := mul_le_mul_of_nonneg_right s.hX₂ h2.le
    have e2 : s.X₂ * nrm s.d.2 ≤ s.X₂ * nrm s.d.2 * nrm s.d.1 :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  hY₁ := by
    have h1 := nrm_pos s.hd.1; have h2 := nrm_one_le s.hd.2
    rw [div_le_div_iff₀ (by positivity) h1]
    have hx : 0 ≤ s.Y₁ := (s.hL.trans_le s.hY₁).le
    have e1 := mul_le_mul_of_nonneg_right s.hY₁ h1.le
    have e2 : s.Y₁ * nrm s.d.1 ≤ s.Y₁ * nrm s.d.1 * nrm s.d.2 :=
      le_mul_of_one_le_right (by positivity) h2
    nlinarith
  hY₂ := by
    have h1 := nrm_one_le s.hd.1; have h2 := nrm_pos s.hd.2
    rw [div_le_div_iff₀ (by positivity) h2]
    have hx : 0 ≤ s.Y₂ := (s.hL.trans_le s.hY₂).le
    have e1 := mul_le_mul_of_nonneg_right s.hY₂ h2.le
    have e2 : s.Y₂ * nrm s.d.2 ≤ s.Y₂ * nrm s.d.2 * nrm s.d.1 :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  hXU₁ := div_le_div_of_nonneg_right s.hXU₁ (nrm_pos s.hd.1).le
  hXU₂ := div_le_div_of_nonneg_right s.hXU₂ (nrm_pos s.hd.2).le
  hYU₁ := div_le_div_of_nonneg_right s.hYU₁ (nrm_pos s.hd.1).le
  hYU₂ := div_le_div_of_nonneg_right s.hYU₂ (nrm_pos s.hd.2).le
  hpX := by
    have h1 := (nrm_pos s.hd.1).ne'; have h2 := (nrm_pos s.hd.2).ne'
    rw [← s.hpX]; field_simp
  hpY := by
    have h1 := (nrm_pos s.hd.1).ne'; have h2 := (nrm_pos s.hd.2).ne'
    rw [← s.hpY]; field_simp
  hP := s.hP
  hM := s.hM
  hpool := s.hpool
  hp := s.hp
  hpn := s.hpn
  hν := s.hν
  hWnorm := s.hWnorm
  hW := s.hW
  hS := s.hS
  hH := s.hH
  henclose := by
    intro I hI h
    apply s.henclose I hI
    have e1 : s.U₁ / nrm s.d.1 / (Ideal.absNorm ((1:Id) * s.B (Sum.inr 0)) : ℝ) =
        s.U₁ / (Ideal.absNorm (s.d.1 * s.B (Sum.inr 0)) : ℝ) := by
      rw [one_mul, map_mul, Nat.cast_mul, div_div]; rfl
    have e2 : s.U₂ / nrm s.d.2 / (Ideal.absNorm ((1:Id) * s.B (Sum.inr 1)) : ℝ) =
        s.U₂ / (Ideal.absNorm (s.d.2 * s.B (Sum.inr 1)) : ℝ) := by
      rw [one_mul, map_mul, Nat.cast_mul, div_div]; rfl
    rcases h with h | h
    · left; rw [← e1]; exact h
    · right; rw [← e2]; exact h

/-! ### The source is unchanged -/

theorem residualPool_renorm (d : Id) (hd : d ≠ 0) (X Y : ℝ) :
    residualPool 1 one_ne_zero (plainSupportPool b (X / nrm d) (Y / nrm d)) =
      residualPool d hd (plainSupportPool b X Y) := by
  have hn := nrm_pos hd
  ext J
  simp only [mem_residualPool, plainSupportPool, Finset.mem_union, mem_idealBall, one_mul]
  have hJ : J ≠ 0 ↔ d * J ≠ 0 := by
    constructor
    · intro h; exact mul_ne_zero hd h
    · intro h hJ; exact h (by rw [hJ, mul_zero])
  have hN : (Ideal.absNorm (d * J) : ℝ) = nrm d * (Ideal.absNorm J : ℝ) := by
    rw [map_mul, Nat.cast_mul]; rfl
  have key : ∀ Q : ℝ, (Ideal.absNorm J : ℝ) ≤ b * (Q / nrm d) ↔
      (Ideal.absNorm (d * J) : ℝ) ≤ b * Q := by
    intro Q
    rw [hN, mul_div_assoc', le_div_iff₀ hn, mul_comm (nrm d)]
  rw [key X, key Y, hJ]

theorem tuplePools_renorm (s : Source ι a b) : MixedPrincipalAllocations.tuplePools (renorm s) = MixedPrincipalAllocations.tuplePools s := by
  unfold MixedPrincipalAllocations.tuplePools sourcePools
  change pools s.pool (residualPool 1 one_ne_zero (plainSupportPool b (s.X₁ / nrm s.d.1)
      (s.Y₁ / nrm s.d.1))) (residualPool 1 one_ne_zero (plainSupportPool b (s.X₂ / nrm s.d.2)
      (s.Y₂ / nrm s.d.2))) = _
  rw [residualPool_renorm s.d.1 s.hd.1, residualPool_renorm s.d.2 s.hd.2]

theorem sourceColumns_renorm (s : Source ι a b) : sourceColumns (renorm s) = sourceColumns s := by
  unfold sourceColumns; rw [tuplePools_renorm]

theorem idealRectangle_renorm (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d₁ d₂ I J : Id)
    (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    idealRectangle W₁ W₂ (X₁ / nrm d₁) (X₂ / nrm d₂) (Y₁ / nrm d₁) (Y₂ / nrm d₂) (1 * I) (1 * J) =
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (d₁ * I) (d₂ * J) := by
  have n1 := (nrm_pos h₁).ne'
  have n2 := (nrm_pos h₂).ne'
  unfold idealRectangle
  have e : ∀ (d K : Id) (Q : ℝ), nrm d ≠ 0 →
      (Ideal.absNorm (1 * K) : ℝ) / (Q / nrm d) = (Ideal.absNorm (d * K) : ℝ) / Q := by
    intro d K Q hd
    rw [one_mul, map_mul, Nat.cast_mul]
    change (Ideal.absNorm K : ℝ) / (Q / nrm d) = nrm d * (Ideal.absNorm K : ℝ) / Q
    rw [div_div_eq_mul_div, mul_comm]
  rw [e d₁ I X₁ n1, e d₂ J X₂ n2, e d₁ I Y₁ n1, e d₂ J Y₂ n2]

theorem sourceCoefficient_renorm (s : Source ι a b) (ha : 0 < a) (seed : Id) :
    sourceCoefficient (renorm s) ha seed = sourceCoefficient s ha seed := by
  unfold sourceCoefficient originalColumn
  have hP := tuplePools_renorm s
  unfold MixedPrincipalAllocations.tuplePools at hP
  rw [hP]
  congr 1
  funext u
  congr 1
  unfold profileCoefficient
  change _ * _ * idealRectangle _ _ (s.X₁ / nrm s.d.1) (s.X₂ / nrm s.d.2) (s.Y₁ / nrm s.d.1)
      (s.Y₂ / nrm s.d.2) (1 * u (Sum.inr 0)) (1 * u (Sum.inr 1)) * _ = _
  rw [idealRectangle_renorm _ _ _ _ _ _ s.d.1 s.d.2 _ _ s.hd.1 s.hd.2]
  rfl

theorem S0_renorm (s : Source ι a b) (ha : 0 < a) : S0 (renorm s) ha = S0 s ha := by
  unfold S0; rw [sourceColumns_renorm, sourceCoefficient_renorm]

theorem sourceNormCap_renorm (s : Source ι a b) :
    sourceNormCap (renorm s).P b (renorm s).T (renorm s).d = sourceNormCap s.P b s.T s.d := by
  unfold sourceNormCap
  change b^2 * ((s.T / (nrm s.d.1 * nrm s.d.2)) / pairNorm ((1:Id), (1:Id))) * _ =
    b^2 * (s.T / pairNorm s.d) * _
  have hp : pairNorm ((1:Id), (1:Id)) = 1 := by simp [pairNorm]
  have hd : pairNorm s.d = nrm s.d.1 * nrm s.d.2 := rfl
  rw [hp, hd, div_one]
  rfl

theorem sourceVolume_renorm (s : Source ι a b) :
    sourceVolume (renorm s) = sourceVolume s / (nrm s.d.1 * nrm s.d.2) := by
  have n1 := (nrm_pos s.hd.1).ne'
  have n2 := (nrm_pos s.hd.2).ne'
  unfold sourceVolume
  change s.X₁ / nrm s.d.1 * (s.X₂ / nrm s.d.2) * ∏ i, s.P i = _
  field_simp

end
end QRH.SilDensitySplit.CubeFree.Second.Provider
