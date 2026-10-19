/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.BootstrapFiber

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.BootstrapAssembly
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
open Marked830Assembly (RawFiberMoments)
variable {Row Label Slot : Type*} [Fintype Label]

def binMean (slots : Finset Slot) (widths : Slot → ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)

def binCutoff (slots : Finset Slot) (widths : Slot → ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  Sil.Uneven.Bootstrap.cutoff (2*a-1) (∑s∈slots,widths s)

def adaptiveKey (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (u : Row) : BinLabel slots ((2*a-1)/2) binWidth × Label ×
        Fin (dyadicLength U) × Fin (dyadicLength U) :=
  let b := amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u
  (b,(witness b u).label,(witness b u).left,(witness b u).right)

def adaptiveFiber (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => adaptiveKey slots widths Q χ U a ε T allowance binWidth i hbin witness u =
    (bin,j,J,K))

theorem adaptiveFiber_fields
    (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u ∈ adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K) :
    u ∈ rows ∧ (witness bin u).label=j ∧ (witness bin u).left=J ∧
      (witness bin u).right=K ∧ ∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s) =
        binValue slots ((2*a-1)/2) binWidth bin s := by
  obtain ⟨hrow,hkey⟩ := Finset.mem_filter.mp hu
  have hb : amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u = bin :=
    congrArg Prod.fst hkey
  have hw : (witness bin u).label=j ∧ (witness bin u).left=J ∧ (witness bin u).right=K := by
    dsimp [adaptiveKey] at hkey
    rw [hb] at hkey
    simpa only [Prod.mk.injEq,true_and] using hkey
  refine ⟨hrow,hw.1,hw.2.1,hw.2.2,?_⟩
  intro s hs
  have hv := congrArg (fun b : BinLabel slots ((2*a-1)/2) binWidth => (b ⟨s,hs⟩).val) hb
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

theorem adaptive_fiber_sum (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (f : Row → ℝ) :
    (∑u∈rows,f u) = ∑bin,∑j,∑J,∑K,
      ∑u∈adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K,f u := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=rows) (t:=Finset.univ)
    (g:=adaptiveKey slots widths Q χ U a ε T allowance binWidth i hbin witness)
    (f:=f) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,adaptiveFiber] using hh.symm



theorem weighted_bound_of_card (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (U δ binWidth A loss : ℝ) (hU : 1<U) (hδ0 : 31/50≤ δ) (hδ : δ≤33/50)
    (hbin : 0<binWidth) (hA : 0≤ A) (hw : ∀s∈slots,0<widths s)
    (hL : 0<∑s∈slots,widths s)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (δ/2) binWidth (Q u s)=g s)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^(δ/2+binWidth))
    (hcard : (rows.card : ℝ)≤ A*U^(Sil.Uneven.Bootstrap.count δ (∑s∈slots,widths s)+
      δ*(∑s∈slots,widths s)-2*weightedMean slots widths g*(∑s∈slots,widths s)+loss)) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤ A*
      U^(Sil.Uneven.Bootstrap.count δ (∑s∈slots,widths s)+δ*(∑s∈slots,widths s)+loss+
        2*binWidth*(∑s∈slots,widths s)) := by
  let S := ∑s∈slots,widths s
  let mean := weightedMean slots widths g
  have hmeanS : mean*S=∑v∈slots,widths v*g v := div_mul_cancel₀ _ hL.ne'
  have hprod (u : Row) (hu : u∈rows) : ‖∏v∈slots,Q u v‖^2≤ U^(2*mean*S+2*binWidth*S) := by
    have hh := HeckePrimeAmplitudeBins.product_upper slots widths (Q u) U (δ/2) binWidth
      hU hbin hw (hQ u hu)
    have hg' : (∑v∈slots,widths v*HeckePrimeAmplitudeBins.amplitude
        (U^(widths v)) (δ/2) binWidth (Q u v))=∑v∈slots,widths v*g v :=
      Finset.sum_congr rfl (fun v hv=>by rw [hbins u hu v hv])
    rw [hg',←hmeanS] at hh
    have hh' := (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)).mpr hh
    convert hh' using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : (0:ℝ)≤ U)]
    congr 1
    ring
  calc
    _ ≤ ∑u∈rows,U^(2*mean*S+2*binWidth*S) := Finset.sum_le_sum hprod
    _ = (rows.card : ℝ)*U^(2*mean*S+2*binWidth*S) := by simp
    _ ≤ (A*U^(Sil.Uneven.Bootstrap.count δ S+δ*S-2*mean*S+loss))*U^(2*mean*S+2*binWidth*S) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by linarith) _)
    _ = _ := by
      rw [mul_assoc,←Real.rpow_add (by linarith : 0<U)]
      congr 1
      dsimp [S]
      ring

theorem weighted_row_sum (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth Δ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤33/50)
    (hε : 0<ε) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hΔ0 : 0≤ Δ) (hΔ : Δ=0) (hC : 0<C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤ mesh)
    (hL : 0<∑s∈slots,widths s)
    (witness : ∀bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀bin j J K,RawFiberMoments
      (adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K)
      slots χ Q widths U a ε (binCutoff slots widths a binWidth bin)
        (3/4+2*Δ) εm C height j J K)
    (hauxmom : ∀bin j J K,AuxiliaryPlainMoments
      (adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K)
      slots χ Q widths U εm C height j K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈slots,widths s)+(2*a-1)*(∑s∈slots,widths s)+
        401*ε+mesh+εm+2*binWidth*(∑s∈slots,widths s)) := by
  let A := 192*(1+height)*C
  let E := Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈slots,widths s)+(2*a-1)*(∑s∈slots,widths s)+
    401*ε+mesh+εm+2*binWidth*(∑s∈slots,widths s)
  have hA : 0≤ A := by dsimp [A]; positivity
  have hf (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
      (J K : Fin (dyadicLength U)) :
      (∑u∈adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K,
        ‖∏s∈slots,Q u s‖^2)≤ A*U^E := by
    let F := adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K
    by_cases hne : F.Nonempty
    · have hfields (u : Row) (hu : u∈F) := adaptiveFiber_fields rows slots widths Q χ U a ε
        T allowance binWidth i hbin witness bin j J K u hu
      have hc := fiber_count F hne slots χ Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U a ε T allowance mesh binWidth Δ εm C height
        i hU ha0 ha hε hmesh hbin hΔ0 hΔ hC hheight hfreq hw hwm hL
        (witness bin) j J K (fun u hu=>(hfields u hu).2.1)
        (fun u hu=>(hfields u hu).2.2.1) (fun u hu=>(hfields u hu).2.2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.2) (hmom bin j J K) (hauxmom bin j J K)
      have hh := weighted_bound_of_card F hne slots Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U (2*a-1) binWidth A
        (401*ε+mesh+εm) hU ha0 ha hbin hA hw hL
        (fun u hu=>(hfields u hu).2.2.2.2)
        (fun u hu=>hQ u (hfields u hu).1) (by simpa only [A,add_assoc] using hc)
      convert hh using 1 <;> dsimp [E] <;> congr 2 <;> ring
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (∑u∈F,‖∏s∈slots,Q u s‖^2)≤ A*U^E
      rw [he,Finset.sum_empty]
      exact mul_nonneg hA (Real.rpow_nonneg (by linarith) _)
  rw [adaptive_fiber_sum rows slots widths Q χ U a ε T allowance binWidth i hbin witness]
  calc
    _ ≤ ∑(_bin : BinLabel slots ((2*a-1)/2) binWidth),∑(_j : Label),
        ∑(_J : Fin (dyadicLength U)),∑(_K : Fin (dyadicLength U)),A*U^E :=
      Finset.sum_le_sum (fun bin _=>Finset.sum_le_sum (fun j _=>
        Finset.sum_le_sum (fun J _=>Finset.sum_le_sum (fun K _=>hf bin j J K))))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem binCutoff_bounds {Slot : Type*} (slots : Finset Slot) (widths : Slot→ℝ)
    (a binWidth : ℝ) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤33/50)
    (hbin : 0<binWidth) (hbin' : binWidth≤(2*a-1)/2)
    (hw : ∀s∈slots,0≤ widths s) (hL : 0<∑s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) :
    1≤ binCutoff slots widths a binWidth bin ∧ binCutoff slots widths a binWidth bin≤3/2 := by
  exact Sil.Uneven.Bootstrap.cutoff_bounds ha0 ha
    (Finset.sum_nonneg hw)

end OAI.SevenEighths.BootstrapAssembly
#print axioms OAI.SevenEighths.BootstrapAssembly.weighted_row_sum
#print axioms OAI.SevenEighths.BootstrapAssembly.binCutoff_bounds
