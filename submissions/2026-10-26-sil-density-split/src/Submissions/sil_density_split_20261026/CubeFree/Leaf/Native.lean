/- Copyright (c) 2026 Sil. Apache-2.0.
The native instance of Seam A: every retained slot is paid at its natural cost.

The packed energy (frozen factor `V`, keep `initialKeep η (internalQ Q η₀) (V*z)`, scale
`K`) is first bounded by the plain energy at scale `N(V)·K = Z^M`
(`Packet.packed_energy_le`). The plain energy is the energy of a natural state of row
width `M = log_Z (N(V)K)` and character width `ε/4` (`packedState`), to which FP's
`NativeNonfixedEnergy.canonical_energy` applies with `κ = 3/4`
(`IncumbentInput.native_kappa_bound : 2β-1 ≤ 3/4`). The ambient slot set is the whole
finite slot type, fixed before the constants; the slot data on `T` are extended by
defaults (`Reindex.extend`). The finite anchor family is fixed before `Z`, so eventually
every anchor conductor is at most `Z^(ε/4)`. -/
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Contract
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Reindex
import Submissions.sil_density_split_20261026.CubeFree.Packet.Sublattice
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.NativeNonfixedEnergy
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.IncumbentInput

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.SilDensitySplit.CubeFree
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
local notation "O" => HeckeFamily.O
local instance nativeLeafQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The natural state of the packed leaf: initial keep, profile `Φ`, scale `U = Z^M`,
row width `M`, character width `δ`, no puncture. -/
def packedState (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ)) (bΦ Z U M δ : ℝ)
    (hZ : 1 ≤ Z) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hU : 0 < U) (hUM : U = Z^M)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀ x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ Z^δ) : NaturalState Z 0 bΦ where
  character := η
  fixedModulus := Q
  puncture := 1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := hU
    nonneg := fun _ => hp _ }
  rowWidth := M
  characterWidth := δ
  base_ge_one := hZ
  row_nonneg := hM
  character_nonneg := hδ
  scale_eq := hUM
  modulus_bound := hη
  puncture_ne_zero := one_ne_zero
  puncture_bound := by simp
  radial_support := hs
  row_ne_zero := fun _ h => h.1
  nonexceptional := fun _ h => h.2

/-- The plain length cap gives the polynomial enclosure of the ordinary length. -/
theorem le_rpow_of_length_le {Z X L : ℝ} (hZ : 1 < Z) (h : length Z X ≤ L) : X ≤ Z^L := by
  have h1 : max 1 X ≤ Z^L := by
    have hpos : 0 < max 1 X := zero_lt_one.trans_le (le_max_left _ _)
    exact (Real.logb_le_iff_le_rpow hZ hpos).mp h
  exact (le_max_right _ _).trans h1

/-- The packed scale is `Z^M` with `M = log_Z (N(V)K)`. -/
theorem packed_scale_eq {Z : ℝ} (hZ : 1 < Z) (V : O) (hV : V ≠ 0) {K : ℝ} (hK : 0 < K) :
    ((Ideal.span {V}).absNorm : ℝ) * K =
      Z^(Real.logb Z (((Ideal.span {V}).absNorm : ℝ) * K)) := by
  have hN : (0:ℝ) < (Ideal.span {V}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV))
  rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (mul_pos hN hK)]

theorem packed_scale_pos (V : O) (hV : V ≠ 0) {K : ℝ} (hK : 0 < K) :
    0 < ((Ideal.span {V}).absNorm : ℝ) * K := by
  have hN : (0:ℝ) < (Ideal.span {V}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV))
  exact mul_pos hN hK

/-- **Native Seam A.** The packed leaf with the native price `κ·(∑ w)₊`, `κ = 3/4`. -/
theorem native_priced_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Mmin Mmax Lplain : ℝ) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax) :
    PricedPackedSource (nativePrice (3/4) (by norm_num)) Mmin Mmax Lplain := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ Q hQ hQ0 hQt hQ72
  have : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  have hMmax : 0 < Mmax := h0.trans_le h1
  obtain ⟨degree, control, hce⟩ := Candidate.FourthPower.NativeNonfixedEnergy.canonical_energy
    rayM H hH (Finset.univ : Finset α) W 1 2 (1/4) (9/4) bΦ (Mmax + ε/4) Lplain 1 (ε/4)
    (33/50) (33/50) (3/4) one_pos hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by positivity) zero_le_one (by positivity) hβ
    Candidate.FourthPower.IncumbentInput.native_kappa_bound (internalQ Q η₀) hQt hQ72
    (inf_le_left.trans hQ)
  obtain ⟨C, hC, hev⟩ := hce η₀ inf_le_right
  refine ⟨degree, control, C, hC, ?_⟩
  have hanch : ∀ᶠ Z : ℝ in atTop, ∀ j, ((anchors j).modulus.absNorm : ℝ) ≤ Z^(ε/4) :=
    eventually_all.mpr (fun j =>
      (tendsto_rpow_atTop (by positivity : (0:ℝ) < ε/4)).eventually (eventually_ge_atTop _))
  filter_upwards [hev, hanch] with Z hZ hZa
  intro j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  have hZ1 : 1 < Z := hZ.1
  set M := Real.logb Z (((Ideal.span {V}).absNorm : ℝ) * K) with hMdef
  have hM0 : 0 ≤ M := h0.le.trans hM₁
  have hUpos := packed_scale_pos V hV hK
  have hUM := packed_scale_eq hZ1 V hV hK
  -- sublattice packing
  have hpack := Packet.packed_energy_le (anchors j) (fixedBadMask*idealGenerator 1) V hV t
    (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
    ((p.support 0).trans Set.Icc_subset_Iic_self) ((p.support 1).trans Set.Icc_subset_Iic_self)
    hX₁ hX₂ (fun i => primePool rayM H 2 (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i => Z^(w i)) (initialKeep (anchors j) (internalQ Q η₀)) Φ hΦpos K hK
  -- the natural state at scale `N(V)K = Z^M`
  let s := packedState (anchors j) (internalQ Q η₀) Φ bΦ Z (((Ideal.span {V}).absNorm : ℝ) * K)
    M (ε/4) hZ1.le hM0 (by positivity) hUpos hUM hΦ hΦpos (hZa j)
  have hwidth : s.width ≤ Mmax + ε/4 := by
    change M + ε/4 ≤ Mmax + ε/4
    linarith
  have he := hZ.2 (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t height
    (fun i _ => extend_forall T w 0 (fun x => 0 ≤ x) hw le_rfl i)
    (fun i _ => extend_forall T w 0 (fun x => x ≤ 1) (fun i => (hwm i).trans hmesh)
      zero_le_one i)
    (fun i _ => extend_forall T σ (33/50) (fun x => 33/50 ≤ x) hσ₁ le_rfl i)
    (fun i _ => extend_forall T σ (33/50) (fun x => x ≤ 33/50) hσ₂ le_rfl i) hh
    (fun i _ => extend_forall T v 0 (fun x => |x| ≤ height) hv (by simpa using hh) i)
    s rfl rfl hwidth T (Finset.subset_univ T) p X₁ X₂ hX₁ hX₂
    (le_rpow_of_length_le hZ1 hl₁) (le_rpow_of_length_le hZ1 hl₂)
  simp only [extend_coe] at he
  rw [sum_univ_extend T w] at he
  refine hpack.trans (he.trans ?_)
  have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hbase : 0 ≤ 1+|t|+height := by positivity
  have hpre : 0 ≤ C*QuadraticInitialBound.diagonalControl Φ*(p.control control)^2*
      (1+|t|+height)^degree := by
    have := p.control_nonneg control
    positivity
  apply mul_le_mul_of_nonneg_left _ hpre
  apply Real.rpow_le_rpow_of_exponent_le hZ1.le
  rw [nativePrice_f]
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  rw [max_eq_right hs0]
  change M + ε/4 + 3/4*(∑ i, w i) + ε/4 ≤ M + 3/4*(∑ i, w i) + ε
  linarith

end
end QRH.SilDensitySplit.CubeFree
