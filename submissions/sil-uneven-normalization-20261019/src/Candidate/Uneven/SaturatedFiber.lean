/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Target830.Marked.GenericCountAssembly
import Candidate.Uneven.SaturatedPowers

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.SaturatedAssembly
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
open Marked830Assembly
variable {Row Label Slot : Type*} [Fintype Label]

theorem fiber_count (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (χ : Row→Label→Character) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U a ε T allowance mesh binWidth Δ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤3/4)
    (hε : 0<ε) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hΔ0 : 0≤ Δ) (hΔ : Δ=0) (hC : 0<C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s)
    (witness : ∀u,SupportedWitness (χ u) U a ε
      (PR63Adaptation.cutoff (2*a-1) (∑s∈slots,widths s)) T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀u∈rows,(witness u).label=label)
    (hJ : ∀u∈rows,(witness u).left=J) (hK : ∀u∈rows,(witness u).right=K)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s)=g s)
    (hmom : RawFiberMoments rows slots χ Q widths U a ε
      (PR63Adaptation.cutoff (2*a-1) (∑s∈slots,widths s)) (3/4+2*Δ) εm C height label J K) :
    (rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(PR63Adaptation.fullCount (2*a-1) (∑s∈slots,widths s)+
        (2*a-1)*(∑s∈slots,widths s)-2*weightedMean slots widths g*(∑s∈slots,widths s)+401*ε+mesh+εm) := by
  let δ := 2*a-1
  let p := weightedMean slots widths g/δ
  let S := ∑s∈slots,widths s
  let t := PR63Adaptation.cutoff δ S
  let r := Real.logb U ((2 : ℝ)^J.val)
  let m := Real.logb U ((2 : ℝ)^K.val)
  let A := 192*(1+height)*C
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hA : 0<A := by dsimp [A]; positivity
  obtain ⟨u0,hu0⟩ := hne
  have hg (v : Slot) (hv : v∈slots) : 0≤ g v ∧ g v≤ δ/2 := by
    rw [←hbins u0 hu0 v hv]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by dsimp [δ] at hδ; linarith)
  obtain ⟨hq0,hq⟩ := weightedMean_bounds slots widths g δ (fun v hv=>(hw v hv).le) hL hg
  have hp0 : 0≤ p := div_nonneg hq0 hδ.le
  have hp : p≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hmean : δ*p=weightedMean slots widths g := by dsimp [p]; field_simp
  have hcut := Sil.Uneven.Saturated.cutoff_bounds
    (d:=δ) (S:=S) hδ.le (by dsimp [δ];linarith) hL.le
  change 1≤ t ∧ t≤3/2 at hcut
  have hlength := HeckeDetectorSupportedWitness.fiber_lengths rows ⟨u0,hu0⟩ χ U a ε t
    T allowance i hU witness J K hJ hK
  change t-r-ε≤ m ∧ r≤ t+ε ∧ m≤1/2+75*ε ∧ t-1/2-76*ε≤ r ∧ 0≤ m at hlength
  have hmono {x y : ℝ} (hxy : x≤ y) : A*U^x≤ A*U^y :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hxy) hA.le
  have hδmesh : δ*mesh≤ mesh := by nlinarith
  have hI : (rows.card : ℝ)≤ A*U^(max 1 ((1+5*r)/6)-δ*r+(400*ε+mesh+εm)) :=
    hmom.inverseUnmarked.trans (hmono (by dsimp [δ]; linarith))
  have hP0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count rows χ U a ε t T allowance i
    hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK εm C height
    hC.le hheight hfreq hmom.plainUnmarked
  have hmax : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith [hlength.2.2.1])
  have hP : (rows.card : ℝ)≤ A*U^(1-2*δ*m+(400*ε+mesh+εm)) :=
    hP0.trans (hmono (by dsimp [m,δ] at *; linarith))
  have hIM (hr : r<1) :
      (rows.card : ℝ)≤ A*U^(1-δ*r-2*δ*p*min S ((1-r)/2)+(400*ε+mesh+εm)) := by
    let si := max 0 (min S ((1-r)/2)-100*ε)
    have hrlo : 1/2-76*ε≤ r := by linarith [hlength.2.2.2.1,hcut.1]
    obtain ⟨hi0,hiL,hloss,hc1,hc2⟩ :=
      Sil.Uneven.Saturated.inverse_width_gates hL.le hε hrlo hr
    have hh := Cycle63MarkedFiber.inverse_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth si εm C height hmesh hbin hw hwm hL hi0 hiL hbins hC.le hheight hfreq
      hc1 hc2 hmom.inverseMarked
    have hc : 12*(1+height)*C≤ A := by dsimp [A];nlinarith
    have hmean0 : 0≤2*δ*p := by positivity
    have hmean1 : 2*δ*p≤1 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hp)]
    have hprod := mul_le_mul_of_nonneg_left hloss hmean0
    have hfee := mul_le_mul_of_nonneg_right hmean1 (show 0≤100*ε by positivity)
    have hpay : 2*δ*p*(min S ((1-r)/2)-si)≤100*ε := by
      dsimp only [si]
      nlinarith only [hprod,hfee]
    calc
      _ ≤ (12*(1+height)*C)*U^(1-δ*r-2*weightedMean slots widths g*si+2*ε+δ*mesh+εm) := hh
      _ ≤ A*U^(1-δ*r-2*weightedMean slots widths g*si+2*ε+δ*mesh+εm) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := hmono (by rw [←hmean];nlinarith only [hpay,hδmesh,hε])
  have hPM (hm : m≤1/2) :
      (rows.card : ℝ)≤ A*U^(1-2*δ*m-2*δ*p*min S (2*(1-2*m)/9)+(400*ε+mesh+εm)) := by
    let sp := min S (2*(1-2*m)/9)
    have hpw0 : 0≤ sp := le_min hL.le (by linarith)
    have hpL : sp≤ S := min_le_left _ _
    have hcap : 2*m+6*(3/4+2*Δ)*sp≤1 := by
      rw [hΔ]
      have hb : sp≤2*(1-2*m)/9 := min_le_right _ _
      linarith
    have hh := Cycle63MarkedFiber.plain_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth sp (3/4+2*Δ) εm C height hmesh hbin hw hwm hL hpw0 hpL hbins
      (by linarith) hC.le hheight hfreq hcap hmom.plainMarked
    exact hh.trans (hmono (by rw [←hmean];nlinarith))
  have hh := Sil.Uneven.Saturated.count_from_saturated_powers hA hU ha0 ha hp0 hp hL.le hε.le
    (show t-ε≤ r+m by linarith [hlength.1]) hlength.2.1 hI hP hIM hPM
  have he : 2*δ*p*S=2*weightedMean slots widths g*S := by rw [←hmean];ring
  rw [he] at hh
  convert hh using 1 <;> dsimp [A,δ,S] <;> congr 2 <;> ring

end OAI.SevenEighths.SaturatedAssembly
#print axioms OAI.SevenEighths.SaturatedAssembly.fiber_count
