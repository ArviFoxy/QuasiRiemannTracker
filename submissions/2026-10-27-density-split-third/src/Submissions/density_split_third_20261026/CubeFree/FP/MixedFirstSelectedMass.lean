/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform actual selected-fiber masses. The constants precede the slot
type, all live restrictions, the supplier, and Z. No energy premise.

Modified by Sil (2026-10-26): reroute: the selected block is Second.SelectedBlock (no supplier characters/slot profiles); the slot-amplitude bound ‖amp i I‖ ≤ Kslot replaces FP's ‖ν‖ ≤ 1 and ‖Wslot‖ ≤ Kslot; selected_fiber_card and grouped_weight_bound are restated for SelectedBlock (FP proofs); the masses are otherwise unchanged.
-/
import Submissions.density_split_third_20261026.CubeFree.FP.MixedFirstRemainder

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.FP.MixedFirstSelectedMass
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass
open QRH.DensitySplitThird.CubeFree.Second.SelectedBlock
local notation "Id" => Ideal HeckeFamily.O


/-! Cube-free reroute: the selected block is `Second.SelectedBlock`; its slot amplitudes
`amp` replace FP's supplier characters and slot profiles. The two counting lemmas of FP
`MixedSupplierPositive` are restated for it (same proofs). -/

theorem selected_fiber_card {α : Type*} [Fintype α] (q : SelectedBlock α) (D : Id) (hD : D≠0) :
    (selectedFiber q D).card≤
      (IdealMobiusDivisorSum.idealDivisors D).card^(Fintype.card q.J) := by
  let e (y : selectedFiber q D) : q.J→IdealMobiusDivisorSum.idealDivisors D := fun j=>
    ⟨(y.val j).val,by
      apply (IdealMobiusDivisorSum.mem_idealDivisors hD).mpr
      have he : selectedProduct q y.val=D := (Finset.mem_filter.mp y.property).2
      exact (congrArg (fun I : Id=>(y.val j).val∣I) he).mp
        (Finset.dvd_prod_of_mem (fun j : q.J=>(y.val j).val) (Finset.mem_univ j))⟩
  have he : Function.Injective e := by
    intro y z h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact congrArg (fun v : IdealMobiusDivisorSum.idealDivisors D=>(v:Id)) (congrFun h j)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective e he

theorem amplitude_norm_le {α : Type*} [Fintype α] (q : SelectedBlock α) (K : ℝ) (hK : 0≤K)
    (hamp : ∀i,∀I∈q.pool i,‖q.amp i I‖≤K) (i : α) (I : Alphabet q) :
    ‖amplitude q i I‖≤K := by
  unfold amplitude
  split_ifs with h
  · exact hamp i I.val h
  · simpa only [norm_zero] using hK

theorem grouped_weight_bound {α : Type*} [Fintype α] (q : SelectedBlock α) (K : ℝ) (hK : 0≤K)
    (hamp : ∀i,∀I∈q.pool i,‖q.amp i I‖≤K) (D : Id) :
    groupedWeight q D≤((selectedFiber q D).card:ℝ)*(∏_j : q.J,K)^2 := by
  unfold groupedWeight
  have hw (y : Selected q) : ‖selectedWeight q y‖≤∏_j : q.J,K := by
    unfold selectedWeight
    rw [norm_prod]
    gcongr with j _
    exact amplitude_norm_le q K hK hamp j.val.val (y j)
  calc
    _ ≤ ∑_y∈selectedFiber q D,(∏_j : q.J,K)^2 :=
      Finset.sum_le_sum (fun y _=>pow_le_pow_left₀ (norm_nonneg _) (hw y) 2)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

/-- The divisor proof of selected_fiber_subpower, with its cardinality
parameter fixed BEFORE the type. This includes every live subtype of
an original type of cardinality at most N, with one and the same C. -/
theorem uniform_fiber_subpower (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(α : Type u) [Fintype α],∀q : SelectedBlock α,
      Fintype.card α≤N → ∀D : Id,D≠0 →
      ((selectedFiber q D).card:ℝ)≤C*(D.absNorm:ℝ)^δ := by
  let ε := δ/((N:ℝ)+1)
  have hε : 0<ε := by dsimp only [ε];positivity
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨(1+C)^N,pow_pos (by linarith) _,?_⟩
  intro α inst q hα D hD
  have hnorm : 1≤(D.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hpow : 1≤(D.absNorm:ℝ)^ε := Real.one_le_rpow hnorm hε.le
  have hcount : Fintype.card q.J≤N := (MixedSelectedVolume.selected_card_le q).trans hα
  have hb : 1≤(1+C)*(D.absNorm:ℝ)^ε := by nlinarith
  have hexp : ε*(N:ℝ)≤δ := by
    have he : ε*((N:ℝ)+1)=δ := by dsimp only [ε];field_simp
    nlinarith
  calc
    _≤((IdealMobiusDivisorSum.idealDivisors D).card:ℝ)^(Fintype.card q.J) := by
      exact_mod_cast selected_fiber_card q D hD
    _≤((1+C)*(D.absNorm:ℝ)^ε)^(Fintype.card q.J) := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact (hdiv D hD).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _≤((1+C)*(D.absNorm:ℝ)^ε)^N := pow_le_pow_right₀ hb hcount
    _=(1+C)^N*(D.absNorm:ℝ)^(ε*(N:ℝ)) := by
      rw [mul_pow,←Real.rpow_natCast ((D.absNorm:ℝ)^ε) N,
        ←Real.rpow_mul (zero_le_one.trans hnorm)]
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hnorm hexp) (by positivity)

/-- Original grouped weights, including all original coefficient zeros.
The fixed Kslot cap is scalar data; no energy bound is assumed. -/
theorem uniform_grouped_subpower (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(α : Type u) [Fintype α],∀q : SelectedBlock α,
      Fintype.card α≤N → ∀Kslot : ℝ,1≤Kslot →
      (∀i,∀I∈q.pool i,‖q.amp i I‖≤Kslot) → ∀D : Id,D≠0 →
      groupedWeight q D≤C*Kslot^(2*N)*(D.absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hfiber⟩ := uniform_fiber_subpower N δ hδ
  refine ⟨C,hC,?_⟩
  intro α inst q hα Kslot hK hamp D hD
  have hK0 : 0≤Kslot := zero_le_one.trans hK
  have hprod : (∏j : q.J,Kslot)≤Kslot^N := by
    simp only [Finset.prod_const,Finset.card_univ]
    exact pow_le_pow_right₀ hK ((MixedSelectedVolume.selected_card_le q).trans hα)
  have hprod0 : 0≤∏j : q.J,Kslot := Finset.prod_nonneg (fun _ _=>hK0)
  have hsquare : (∏j : q.J,Kslot)^2≤Kslot^(2*N) := by
    apply (pow_le_pow_left₀ hprod0 hprod 2).trans_eq
    rw [←pow_mul]
    congr 1
    omega
  have hf := hfiber α q hα D hD
  have hg := grouped_weight_bound q Kslot hK0 hamp D
  exact hg.trans ((mul_le_mul hf hsquare (sq_nonneg _)
    (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans_eq (by ring))

/-- A finite mass at a padded/dyadic width. The factor 256 is the
actual ideal-ball count 128*(2W), and the denominator is this same W. -/
theorem selected_mass_at_width {α : Type u} [Fintype α]
    (q : SelectedBlock α) (W L : ℝ) (hW : 0<W) (hL : 0≤L)
    (hDN : ∀D∈selectedProducts q,(D.absNorm:ℝ)≤2*W)
    (hw : ∀D∈selectedProducts q,groupedWeight q D≤L) :
    (∑D∈selectedProducts q,groupedWeight q D)/W≤256*L := by
  have hsub : selectedProducts q⊆idealBall (2*W) := by
    intro D hD
    exact (mem_idealBall _ _).mpr ⟨(selected_products_supported q D hD).1,hDN D hD⟩
  have hc : ((selectedProducts q).card:ℝ)≤((idealBall (2*W)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcard : ((selectedProducts q).card:ℝ)≤256*W :=
    (hc.trans (idealBall_card _ (by positivity))).trans_eq (by ring)
  have hsum : (∑D∈selectedProducts q,groupedWeight q D)≤256*W*L := by
    calc
      _≤∑_D∈selectedProducts q,L := Finset.sum_le_sum (fun D hD=>hw D hD)
      _=((selectedProducts q).card:ℝ)*L := by rw [Finset.sum_const,nsmul_eq_mul]
      _≤_ := mul_le_mul_of_nonneg_right hcard hL
  apply (div_le_div_of_nonneg_right hsum hW.le).trans_eq
  field_simp [hW.ne']
  <;> ring

/-- The only new Z exponent is Btail*δ. The constant includes 2^δ
from the literal selected-product cap N(D)≤2W. This same constant
works for every type, supplier, live subset and scalar slot cap. -/
theorem uniform_grouped_window (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(α : Type u) [Fintype α],∀q : SelectedBlock α,
      Fintype.card α≤N → ∀Kslot : ℝ,1≤Kslot →
      (∀i,∀I∈q.pool i,‖q.amp i I‖≤Kslot) →
      ∀Z W Btail : ℝ,1≤Z → 0<W → W≤Z^Btail →
      (∀D∈selectedProducts q,(D.absNorm:ℝ)≤2*W) →
      (∀D∈selectedProducts q,0≤groupedWeight q D ∧
        groupedWeight q D≤C*Kslot^(2*N)*Z^(Btail*δ)) ∧
      (∑D∈selectedProducts q,groupedWeight q D)/W≤
        256*(C*Kslot^(2*N)*Z^(Btail*δ)) := by
  obtain ⟨C,hC,hgroup⟩ := uniform_grouped_subpower N δ hδ
  have htwo : 0<(2:ℝ)^δ := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C*2^δ,mul_pos hC htwo,?_⟩
  intro α inst q hα Kslot hK hamp Z W Btail hZ hW hWcap hDN
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hK0 : 0≤Kslot := zero_le_one.trans hK
  have hweight (D : Id) (hD : D∈selectedProducts q) :
      groupedWeight q D≤(C*2^δ)*Kslot^(2*N)*Z^(Btail*δ) := by
    have he := hgroup α q hα Kslot hK hamp D
      (selected_products_supported q D hD).1
    have hp : (D.absNorm:ℝ)^δ≤(2:ℝ)^δ*Z^(Btail*δ) := by
      calc
        _≤(2*Z^Btail)^δ := Real.rpow_le_rpow (Nat.cast_nonneg _)
          ((hDN D hD).trans (mul_le_mul_of_nonneg_left hWcap (by norm_num))) hδ.le
        _=_ := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZ0.le _),
            ←Real.rpow_mul hZ0.le]
    exact he.trans ((mul_le_mul_of_nonneg_left hp
      (mul_nonneg hC.le (pow_nonneg hK0 _))).trans_eq (by ring))
  refine ⟨fun D hD=>⟨grouped_weight_nonneg q D,hweight D hD⟩,?_⟩
  exact selected_mass_at_width q W _ hW (by positivity) hDN hweight

/-- The original selected volume is NOT the padded scale. This output
keeps their exact single padding factor, then bounds it uniformly by
2^N. All slot types and live restrictions share one C chosen before Z.
No extra padding power is silently inserted in Btail*δ. -/
theorem uniform_selected_volume_mass (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(α : Type u) [Fintype α],∀q : SelectedBlock α,
      Fintype.card α≤N → ∀Kslot : ℝ,1≤Kslot →
      (∀i,∀I∈q.pool i,‖q.amp i I‖≤Kslot) →
      (∀i,0<q.P i) →
      (∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i) →
      ∀Z Btail : ℝ,1≤Z → MixedSelectedVolume.scale q≤Z^Btail →
      let L := C*Kslot^(2*N)*Z^(Btail*δ)
      (∀D∈selectedProducts q,0≤groupedWeight q D ∧ groupedWeight q D≤L) ∧
      (∑D∈selectedProducts q,groupedWeight q D)/MixedSelectedVolume.volume q≤
        128*MixedSelectedVolume.padding q*L ∧
      (∑D∈selectedProducts q,groupedWeight q D)/MixedSelectedVolume.volume q≤
        128*(2:ℝ)^N*L := by
  obtain ⟨C,hC,hwindow⟩ := uniform_grouped_window N δ hδ
  refine ⟨C,hC,?_⟩
  intro α inst q hα Kslot hK hamp hP hpool Z Btail hZ hscale
  have hK0 : 0≤Kslot := zero_le_one.trans hK
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let L := C*Kslot^(2*N)*Z^(Btail*δ)
  have hL : 0≤L := by dsimp only [L];positivity
  have hp := MixedSelectedVolume.scale_pos q hP
  have hDN (D : Id) (hD : D∈selectedProducts q) :
      (D.absNorm:ℝ)≤2*MixedSelectedVolume.scale q :=
    (MixedSelectedVolume.selected_products_norm q hpool D hD).trans (by linarith)
  have hw := (hwindow α q hα Kslot hK hamp Z
    (MixedSelectedVolume.scale q) Btail hZ hp hscale hDN).1
  have hm := MixedFirstRemainder.actual_selected_mass q hP hpool (groupedWeight q) L hL hw
  refine ⟨hw,hm,hm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (MixedSelectedVolume.padding_le q N hα) (by norm_num)) hL

end
end QRH.DensitySplitThird.CubeFree.FP.MixedFirstSelectedMass
