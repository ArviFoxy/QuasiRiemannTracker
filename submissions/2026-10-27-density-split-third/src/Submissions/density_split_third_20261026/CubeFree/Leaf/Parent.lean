/- Copyright (c) 2026 Sil. Apache-2.0.
The parent instance of Seam A: paid partial deletion into the parent face (CF §5, (5.2)).

Given the parent `G(B₀,L₀,c₀)` at `M = 1` (`GlobalSource`), for `M = log_Z(N(V)K)` in a
fixed positive interval `[Mmin, Mmax]`:
* the parent is rescaled to `[Mmin, Mmax]` uniformly over the finite anchor family
  (PR69 `unit_source_finite_anchors`, loss `ε/4`, mesh `≤ unitMesh·Mmin`);
* the packed row is unpacked (`Packet.packed_energy_le`) to the plain energy at scale
  `Z^M`, i.e. the energy of the natural state `packedState`;
* if the ordinary lengths alone exceed the face (`B₀M < m₁+m₂`), the need is the whole
  slot width and the native bound (all slots paid, all lengths) is the zero-slot fallback;
* otherwise whole slots of total width in `[need, need+mesh]` are deleted greedily
  (`greedy_deletion`), each at its natural cost `κ = 3/4` (`canonical_partial_delete`),
  and the retained slots lie in the parent face (`globalFace_admissible_iff`); the one
  mesh of overshoot is paid by `mesh ≤ ε/8`.
Subunit ordinary lengths (`X < 1`) have `length = 0` and need no extra case: the parent
quantifies over all `X > 0`. -/
import Submissions.density_split_third_20261026.CubeFree.Leaf.Native
import Submissions.density_split_third_20261026.CubeFree.Leaf.PartialDeletion
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalParentSources

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.DensitySplitThird.CubeFree
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
local notation "O" => HeckeFamily.O
local instance parentLeafQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-! ### Scalar ledger of the paid deletion -/

/-- If the ordinary lengths alone leave the face, the whole slot width must be deleted. -/
theorem deletionNeed_eq_self_of_lengths {B₀ L₀ c₀ P s M : ℝ} (hL : 0 < L₀) (hs : 0 ≤ s)
    (hP : B₀*M < P) : deletionNeed B₀ L₀ c₀ P s M = s := by
  have hY : s ≤ (P + L₀*s - B₀*M)/L₀ := by
    rw [le_div_iff₀ hL]; nlinarith
  unfold deletionNeed
  rw [min_eq_left (hY.trans (le_max_right _ _)), max_eq_right hs]

/-- Deleting at least the need enters the parent face: the retained width
`s - del ≥ 0` satisfies the cap and the budget of `G(B₀,L₀,c₀)` at `M`, provided the
ordinary lengths alone fit (`P ≤ B₀M`). -/
theorem retained_in_face {B₀ L₀ c₀ P s M del : ℝ} (hL : 0 < L₀) (hc : 0 ≤ c₀) (hM : 0 ≤ M)
    (hP : P ≤ B₀*M) (hdel : deletionNeed B₀ L₀ c₀ P s M ≤ del) (hs' : 0 ≤ s - del) :
    s - del ≤ c₀*M ∧ P + L₀*(s - del) ≤ B₀*M := by
  have hneed : min s (max (s - c₀*M) ((P + L₀*s - B₀*M)/L₀)) ≤ del :=
    (le_max_right _ _).trans hdel
  have hcM : 0 ≤ c₀*M := mul_nonneg hc hM
  rcases le_total s (max (s - c₀*M) ((P + L₀*s - B₀*M)/L₀)) with h | h
  · rw [min_eq_left h] at hneed
    have h0 : s - del = 0 := by linarith
    rw [h0]; constructor <;> linarith
  · rw [min_eq_right h] at hneed
    have hX : s - c₀*M ≤ del := (le_max_left _ _).trans hneed
    have hY : (P + L₀*s - B₀*M)/L₀ ≤ del := (le_max_right _ _).trans hneed
    rw [div_le_iff₀ hL] at hY
    constructor <;> nlinarith

/-- Constants of the deletion cost times the parent bound fit the combined constants. -/
theorem combine_parent {CD CP CN dg cP cS base Z e₁ e₂ e₃ : ℝ} {degD degP degN : ℕ}
    (hCD : 0 ≤ CD) (hCP : 0 ≤ CP) (hCN : 0 ≤ CN) (hdg : 0 ≤ dg) (hcP : 0 ≤ cP)
    (hcPS : cP ≤ cS) (hbase : 1 ≤ base) (hZ : 1 ≤ Z) (he : e₁ + e₂ ≤ e₃) :
    CD*base^degD*Z^e₁*(CP*dg*cP^2*base^degP*Z^e₂) ≤
      (CN + CD*CP)*dg*cS^2*base^(degN+degP+degD)*Z^e₃ := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hb0 : 0 ≤ base := zero_le_one.trans hbase
  have e1 : CD*base^degD*Z^e₁*(CP*dg*cP^2*base^degP*Z^e₂) =
      (CD*CP)*dg*cP^2*base^(degP+degD)*Z^(e₁+e₂) := by
    rw [pow_add, Real.rpow_add hZ0]; ring
  rw [e1]
  have h1 : CD*CP ≤ CN + CD*CP := by linarith
  have h2 : cP^2 ≤ cS^2 := pow_le_pow_left₀ hcP hcPS 2
  have h3 : base^(degP+degD) ≤ base^(degN+degP+degD) :=
    pow_le_pow_right₀ hbase (by omega)
  have h4 : Z^(e₁+e₂) ≤ Z^e₃ := Real.rpow_le_rpow_of_exponent_le hZ he
  have hCDP : 0 ≤ CD*CP := mul_nonneg hCD hCP
  have hcS : 0 ≤ cS^2 := sq_nonneg _
  have hp1 : 0 ≤ base^(degP+degD) := pow_nonneg hb0 _
  have hp2 : 0 ≤ base^(degN+degP+degD) := pow_nonneg hb0 _
  have hz1 : 0 ≤ Z^(e₁+e₂) := (Real.rpow_pos_of_pos hZ0 _).le
  have hA : (CD*CP)*dg ≤ (CN + CD*CP)*dg := mul_le_mul_of_nonneg_right h1 hdg
  have hB : (CD*CP)*dg*cP^2 ≤ (CN + CD*CP)*dg*cS^2 :=
    mul_le_mul hA h2 (sq_nonneg _) (mul_nonneg (by linarith) hdg)
  have hC : (CD*CP)*dg*cP^2*base^(degP+degD) ≤ (CN + CD*CP)*dg*cS^2*base^(degN+degP+degD) :=
    mul_le_mul hB h3 hp1 (mul_nonneg (mul_nonneg (by linarith) hdg) hcS)
  exact mul_le_mul hC h4 hz1 (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hdg) hcS) hp2)

/-- The native fallback bound fits the combined constants. -/
theorem combine_native {CD CP CN dg cN cS base Z e e₃ : ℝ} {degD degP degN : ℕ}
    (hCD : 0 ≤ CD) (hCP : 0 ≤ CP) (hCN : 0 ≤ CN) (hdg : 0 ≤ dg) (hcN : 0 ≤ cN)
    (hcNS : cN ≤ cS) (hbase : 1 ≤ base) (hZ : 1 ≤ Z) (he : e ≤ e₃) :
    CN*dg*cN^2*base^degN*Z^e ≤ (CN + CD*CP)*dg*cS^2*base^(degN+degP+degD)*Z^e₃ := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hb0 : 0 ≤ base := zero_le_one.trans hbase
  have h1 : CN ≤ CN + CD*CP := by nlinarith
  have h2 : cN^2 ≤ cS^2 := pow_le_pow_left₀ hcN hcNS 2
  have h3 : base^degN ≤ base^(degN+degP+degD) := pow_le_pow_right₀ hbase (by omega)
  have h4 : Z^e ≤ Z^e₃ := Real.rpow_le_rpow_of_exponent_le hZ he
  have hT : 0 ≤ CN + CD*CP := by nlinarith
  have hA : CN*dg ≤ (CN + CD*CP)*dg := mul_le_mul_of_nonneg_right h1 hdg
  have hB : CN*dg*cN^2 ≤ (CN + CD*CP)*dg*cS^2 :=
    mul_le_mul hA h2 (sq_nonneg _) (mul_nonneg hT hdg)
  have hC : CN*dg*cN^2*base^degN ≤ (CN + CD*CP)*dg*cS^2*base^(degN+degP+degD) :=
    mul_le_mul hB h3 (pow_nonneg hb0 _) (mul_nonneg (mul_nonneg hT hdg) (sq_nonneg _))
  exact mul_le_mul hC h4 (Real.rpow_pos_of_pos hZ0 _).le
    (mul_nonneg (mul_nonneg (mul_nonneg hT hdg) (sq_nonneg _)) (pow_nonneg hb0 _))

/-! ### The parent leaf -/

/-- **Parent Seam A.** From the parent `G(B₀,L₀,c₀)` at `M = 1`, the packed leaf with the
paid-deletion price `κ·deletionNeed B₀ L₀ c₀ P s M`, `κ = 3/4`, on `[Mmin, Mmax]`. -/
theorem parent_priced_source (B₀ L₀ c₀ Mmin Mmax Lplain : ℝ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 0 < L₀ ∧ 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (parentPrice (3/4) B₀ L₀ c₀ (by norm_num) hface.1) Mmin Mmax Lplain := by
  intro ε hε
  obtain ⟨meshN, hmeshN, hnat⟩ := native_priced_source hβ Mmin Mmax Lplain h0 h1 ε hε
  have hMmax : 0 < Mmax := h0.trans_le h1
  -- parent rescaling data
  have hden : 0 < max (1:ℝ) Mmax := zero_lt_one.trans_le (le_max_left _ _)
  have hue : 0 < (ε/4)/(max 1 Mmax) := div_pos (by positivity) hden
  obtain ⟨unitMesh, hum, hu⟩ := hparent ((ε/4)/(max 1 Mmax)) hue
  have he : Mmax*((ε/4)/(max 1 Mmax)) ≤ ε/4 := by
    calc Mmax*((ε/4)/(max 1 Mmax)) ≤ (max 1 Mmax)*((ε/4)/(max 1 Mmax)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hue.le
      _ = ε/4 := mul_div_cancel₀ _ hden.ne'
  refine ⟨min (min (unitMesh*Mmin) meshN) (min (ε/8) 1), ?_, ?_⟩
  · have := mul_pos hum h0
    exact lt_min (lt_min this hmeshN) (lt_min (by positivity) one_pos)
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ Q hQ hQ0 hQt hQ72
  have hmeshPos : 0 < min (min (unitMesh*Mmin) meshN) (min (ε/8) 1) :=
    lt_min (lt_min (mul_pos hum h0) hmeshN) (lt_min (by positivity) one_pos)
  have hm' : max 0 mesh ≤ min (min (unitMesh*Mmin) meshN) (min (ε/8) 1) :=
    max_le hmeshPos.le hmesh
  have hmU : max 0 mesh ≤ unitMesh*Mmin := hm'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmN : mesh ≤ meshN := hmesh.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmE : max 0 mesh ≤ ε/8 := hm'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm1 : max 0 mesh ≤ 1 := hm'.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- native (zero-slot fallback) constants
  obtain ⟨degN, SN, CN, hCN, hevN⟩ := hnat mesh hmN α rayM H hH W hW hWs bΦ hbΦ κ anchors η₀ Q
    hQ hQ0 hQt hQ72
  -- parent constants, uniform over the anchors and over `[Mmin, Mmax]`
  obtain ⟨degP, SP, CP, hCP, hevP⟩ :=
    QRH.Record1252270103Source.PhysicalParentSources.unit_source_finite_anchors (α:=α) hu
      rayM H hH W hW hWs bΦ (max 0 mesh) Mmin Mmax (ε/4) hbΦ h0 hum.le hmU hue.le he
      anchors η₀ Q hQ hQ0 hQt hQ72
  -- natural deletion constants
  obtain ⟨degD, CD, hCD, hdel⟩ := canonical_partial_delete rayM H hH (α:=α) W 1 2 bΦ
    (Mmax + ε/8) 1 (ε/8) (33/50) (33/50) (3/4) one_pos hWs hW (by linarith) (by positivity)
    zero_le_one (by positivity) hβ Candidate.FourthPower.IncumbentInput.native_kappa_bound
  refine ⟨degN+degP+degD, SN ∪ SP, CN + CD*CP, by positivity, ?_⟩
  have hanch : ∀ᶠ Z : ℝ in atTop, ∀ j, ((anchors j).modulus.absNorm : ℝ) ≤ Z^(ε/8) :=
    eventually_all.mpr (fun j =>
      (tendsto_rpow_atTop (by positivity : (0:ℝ) < ε/8)).eventually (eventually_ge_atTop _))
  filter_upwards [hevN, hevP, hdel η₀, hanch] with Z hZN hZP hZD hZa
  intro j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  have hZ1 : 1 < Z := hZD.1
  have hbase : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hdg := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hcN : p.control SN ≤ p.control (SN ∪ SP) :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p Finset.subset_union_left
  have hcP : p.control SP ≤ p.control (SN ∪ SP) :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p Finset.subset_union_right
  rw [parentPrice_f]
  by_cases hfall : B₀ * Real.logb Z (((Ideal.span {V}).absNorm : ℝ) * K) <
      length Z X₁ + length Z X₂
  · -- zero-slot fallback: everything is deleted at the native price
    have hn := hZN j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos
      p X₁ X₂ hX₁ hX₂ hl₁ hl₂
    rw [nativePrice_f, max_eq_right hs0] at hn
    refine hn.trans (combine_native hCD.le hCP.le hCN.le hdg (p.control_nonneg SN) hcN hbase
      hZ1.le ?_)
    rw [deletionNeed_eq_self_of_lengths hface.1 hs0 hfall]
  · -- paid partial deletion into the parent face
    replace hfall := not_lt.mp hfall
    set M := Real.logb Z (((Ideal.span {V}).absNorm : ℝ) * K) with hMdef
    have hM0 : 0 ≤ M := h0.le.trans hM₁
    have hUpos := packed_scale_pos V hV hK
    have hUM : ((Ideal.span {V}).absNorm : ℝ) * K = Z^M := packed_scale_eq hZ1 V hV hK
    set need := deletionNeed B₀ L₀ c₀ (length Z X₁ + length Z X₂) (∑ i, w i) M with hneed
    have hneed0 : 0 ≤ need := deletionNeed_nonneg _ _ _ _ _ _
    have hneeds : need ≤ ∑ i, w i := deletionNeed_le_self hs0
    have hsT : ∑ i ∈ T, extend T w 0 i = ∑ i, w i := sum_extend T w 0
    have hw' : ∀ i, 0 ≤ extend T w 0 i := extend_forall T w 0 (fun x => 0 ≤ x) hw le_rfl
    have hwm' : ∀ i, extend T w 0 i ≤ max 0 mesh :=
      extend_forall T w 0 (fun x => x ≤ max 0 mesh) (fun i => (hwm i).trans (le_max_right _ _))
        (le_max_left _ _)
    have hσ₁' : ∀ i, (33/50:ℝ) ≤ extend T σ (33/50) i :=
      extend_forall T σ (33/50) (fun x => 33/50 ≤ x) hσ₁ le_rfl
    have hσ₂' : ∀ i, extend T σ (33/50) i ≤ 33/50 :=
      extend_forall T σ (33/50) (fun x => x ≤ 33/50) hσ₂ le_rfl
    have hv' : ∀ i, |extend T v 0 i| ≤ height :=
      extend_forall T v 0 (fun x => |x| ≤ height) hv (by simpa using hh)
    -- greedy choice of the deleted whole slots
    obtain ⟨F, hFT, hlo, hhi⟩ := greedy_deletion T (extend T w 0) (max 0 mesh) need
      (le_max_left _ _) hneed0 (fun i _ => hw' i) (fun i _ => hwm' i) (by rw [hsT]; exact hneeds)
    have hsplit : ∑ i ∈ F, extend T w 0 i + ∑ i ∈ T \ F, extend T w 0 i = ∑ i, w i :=
      (sum_retained_add_deleted T F hFT (extend T w 0)).trans hsT
    have hF0 : 0 ≤ ∑ i ∈ F, extend T w 0 i := Finset.sum_nonneg (fun i _ => hw' i)
    -- the retained slots are admissible for the parent face
    have hface' := retained_in_face (del := ∑ i ∈ T \ F, extend T w 0 i) hface.1
      hface.2.2.2.le hM0 hfall hlo (by linarith)
    have hsF : ∑ i : F, extend T w 0 i = ∑ i ∈ F, extend T w 0 i :=
      Finset.sum_coe_sort F (extend T w 0)
    have hadm : (QRH.Record1252270103Source.globalFace B₀ L₀ c₀).Admissible
        (length Z X₁) (length Z X₂) (∑ i : F, extend T w 0 i) M := by
      rw [QRH.Record1252270103Source.globalFace_admissible_iff (length_nonneg Z X₁ hZ1)
        (length_nonneg Z X₂ hZ1) (by rw [hsF]; exact hF0) hface.1.le, hsF]
      have e : ∑ i ∈ F, extend T w 0 i = (∑ i, w i) - ∑ i ∈ T \ F, extend T w 0 i := by
        linarith
      rw [e]
      exact hface'
    -- sublattice packing
    have hpack := Packet.packed_energy_le (anchors j) (fixedBadMask*idealGenerator 1) V hV t
      (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
      ((p.support 0).trans Set.Icc_subset_Iic_self) ((p.support 1).trans Set.Icc_subset_Iic_self)
      hX₁ hX₂ (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) (initialKeep (anchors j) (internalQ Q η₀)) Φ hΦpos K hK
    -- the natural state at scale `N(V)K = Z^M`
    let st := packedState (anchors j) (internalQ Q η₀) Φ bΦ Z
      (((Ideal.span {V}).absNorm : ℝ) * K) M (ε/8) hZ1.le hM0 (by positivity) hUpos hUM hΦ
      hΦpos (hZa j)
    have hwidth : st.width ≤ Mmax + ε/8 := by
      change M + ε/8 ≤ Mmax + ε/8
      linarith
    -- natural cost of the deleted slots `T \ F`
    have hd := hZD.2 (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t height
      hw' (fun i => (hwm' i).trans hm1) hσ₁' hσ₂' hh hv' 0 st rfl hwidth Q rfl hQ T F hFT
      (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
    simp only [extend_coe] at hd
    -- the parent at the retained slots `F`
    have hp := hZP j F (fun i : F => extend T θ 1 i) (fun i : F => extend T w 0 i)
      (fun i : F => extend T σ (33/50) i) (fun i : F => extend T v 0 i) t height
      (fun i => hw' i) (fun i => hwm' i) (fun i => hσ₁' i) (fun i => hσ₂' i) hh (fun i => hv' i)
      M hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
    rw [← hUM] at hp
    have hcost : 0 ≤ CD*(1+|t|+height)^degD*Z^(ε/8+3/4*(∑ i ∈ T \ F, extend T w 0 i)) := by
      have := (Real.rpow_pos_of_pos (zero_lt_one.trans hZ1)
        (ε/8+3/4*(∑ i ∈ T \ F, extend T w 0 i))).le
      have := pow_nonneg (zero_le_one.trans hbase) degD
      positivity
    refine hpack.trans (hd.trans ((mul_le_mul_of_nonneg_left hp hcost).trans ?_))
    apply combine_parent hCD.le hCP.le hCN.le hdg (p.control_nonneg SP) hcP hbase hZ1.le
    have : 3/4*(∑ i ∈ T \ F, extend T w 0 i) ≤ 3/4*need + 3/4*(ε/8) := by linarith
    linarith

end
end QRH.DensitySplitThird.CubeFree
