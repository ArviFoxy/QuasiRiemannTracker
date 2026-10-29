/- Copyright (c) 2026 Sil, ArviFoxy. Apache-2.0.
HIGH energy of the density-split leaf with the marked class count (DS §3, final source audit §5;
PR 76 repeated marks).

The HIGH rows (kept, not LOW at the cut `q`) are classified by their q-free chosen bin
(`selectBin`) at the base height `Z^τ`. For a bin `c` with `ν = 2 b_c - 1 ∈ [q, 3/4]` and every
finite set of its rows, the sum of the squared packed rows is at most

  `K·ctl²·Z^{M + highTermM ν P s M + loss}`:

each row is bounded by its ordinary factors (`high_row_plain_factor`) times the squared slot
product; the slots of width at least `wmin` are summed over the regular rows by the repeated-mark
class count (`high_class_sum_marked`), the slots below `wmin` and the exceptional rows (finitely
many cores, `high_exceptional_count`) at full amplitude (`high_slot_bound`). By
`energy_le_class_sums` and `le_highSupM` the HIGH energy is at most
`K·diag·ctl²·Z^{M + highSupM q P s M + Lfix + τJ}`.

Fork of Sil's `Density/LeafHighEnergy` (PR 83) of this package: the unmarked class count times the
pointwise bound is replaced by the marked class sum, the price `highSup` by `highSupM`, and the bounded
height regime is `1 + |t| + height ≤ Z^τ` (the buffered bins at base height `Z^τ`, `h = 0`), where
the polynomial height factor is absorbed in `Z^{τJ}`. -/
import Submissions.arvi_density.Density.LeafHighEnergy
import Submissions.arvi_density.Density.PriceMarked
import Submissions.arvi_density.Density.LeafHighMarked
import Submissions.arvi_density.Density.LeafHighRowMarked
import Submissions.arvi_density.Density.LeafRowsMarked

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QRH.ArviDensity.Density
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open QRH.SilDensitySplit.Density QRH.SilDensitySplit.CubeFree
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedProfile
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open LocalMoment HeckeDetectorZeros ProbePhysical
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open Record12518109Natural Record12518109GainWholeGeometry Record12518109GainExceptional
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

/-- `1 - ρ(ν) = 10ν/(15-6ν)`. -/
theorem one_sub_density (ν : ℝ) : 10 * ν / (15 - 6 * ν) = 1 - unmarkedDensity ν := by
  have e : (15 - 6 * ν) = 3 * (5 - 2 * ν) := by ring
  unfold unmarkedDensity
  rw [e]; ring

/-- `cmax ν = ν + ρ(ν) - 1`. -/
theorem cmax_eq_density (ν : ℝ) :
    QRH.Record1252270103Source.High.cmax ν = ν + unmarkedDensity ν - 1 := by
  rw [QRH.RepeatedMarks.Source.cmax_eq]
  simp only [QRH.RepeatedMarks.baseXi, QRH.RepeatedMarks.densityDenom]
  have h : ν * (1 - 10 / (15 - 6 * ν)) = ν - 10 * ν / (15 - 6 * ν) := by ring
  rw [h, one_sub_density ν]; ring

/-- The exponent of a regular row of a HIGH class: the plain factor, the small slots at full
amplitude and the pivot sum over the large slots fit the marked price. -/
theorem marked_regular_exponent {B₀ L₀ c₀ ν M F S SL SS Pl εb A1 B1 L0 nw Lfix τJ : ℝ}
    (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1) (hL : 1 < L₀)
    (hc0 : 0 ≤ c₀) (hc1 : c₀ ≤ 1) (hMF : M ≤ F) (hFM : F ≤ M + εb) (hS : S = SL + SS)
    (hSS : SS ≤ nw) (hSS0 : 0 ≤ SS)
    (hLfix : A1 + B1 + εb + nw + L0 ≤ Lfix) :
    ν * Pl + A1 + (B1 + ν * SS) + (unmarkedDensity ν * F + ν * SL -
        QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ SL F + L0) + τJ ≤
      M + highTermM B₀ L₀ c₀ ν Pl S M + (Lfix + τJ) := by
  have hρ1 : unmarkedDensity ν ≤ 1 := unmarkedDensity_le_one' (by linarith) hν1
  have hG1 := QRH.Record1252270103Source.High.gain_mono_rm (S := S) (L := S) (Q := M) (F := F)
    hν0 hν1 hB0 hB1 hL hc0 hc1 le_rfl hMF
  have hG2 := QRH.Record1252270103Source.High.weighted_exponent_mono_rm (B := B₀) (h := c₀)
    (Q := F) hν0 hν1 hL (show SL ≤ S by linarith)
  have hk := one_sub_density ν
  have hHT : highTermM B₀ L₀ c₀ ν Pl S M = ν * (Pl + S) - (1 - unmarkedDensity ν) * M -
      QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ S M := by
    rw [highTermM_eq, hk]
  rw [hHT]
  have hρF : unmarkedDensity ν * F ≤ unmarkedDensity ν * M + εb := by
    have : unmarkedDensity ν * (F - M) ≤ 1 * (F - M) :=
      mul_le_mul_of_nonneg_right hρ1 (by linarith)
    nlinarith
  subst hS
  nlinarith

/-- The exponent of an exceptional row (all slots at full amplitude, count `Z^{F/6}`). -/
theorem marked_exceptional_exponent {B₀ L₀ c₀ ν M F S Pl εb A1 B1 Lfix : ℝ}
    (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1) (hL : 1 < L₀)
    (hc0 : 0 ≤ c₀) (hc1 : c₀ ≤ 1) (hM0 : 0 ≤ M) (hFM : F ≤ M + εb) (hεb : 0 ≤ εb)
    (hLfix : A1 + B1 + εb ≤ Lfix) :
    ν * Pl + A1 + (B1 + ν * S) + F / 6 ≤ M + highTermM B₀ L₀ c₀ ν Pl S M + Lfix := by
  have hG := QRH.Record1252270103Source.High.gain_le_cmax_rm (S := S) hν0 hν1 hB0 hB1 hL hc0 hc1 hM0
  rw [cmax_eq_density ν] at hG
  have hk := one_sub_density ν
  have hHT : highTermM B₀ L₀ c₀ ν Pl S M = ν * (Pl + S) - (1 - unmarkedDensity ν) * M -
      QRH.RepeatedMarks.Source.gainC ν B₀ L₀ c₀ S M := by
    rw [highTermM_eq, hk]
  rw [hHT]
  nlinarith

/-- A product of nonnegative factors, each at most `Cs·Z^{e s}` with `Cs ≥ 1`. -/
theorem prod_le_const_rpow {α : Type*} (A : Finset α) {Z Cs : ℝ} (hZ : 0 < Z)
    (g e : α → ℝ) (hg : ∀ s ∈ A, g s ≤ Cs * Z^(e s)) (hg0 : ∀ s ∈ A, 0 ≤ g s) :
    ∏ s ∈ A, g s ≤ Cs^A.card * Z^(∑ s ∈ A, e s) := by
  calc ∏ s ∈ A, g s ≤ ∏ s ∈ A, (Cs * Z^(e s)) := Finset.prod_le_prod₀ hg0 hg
    _ = Cs^A.card * Z^(∑ s ∈ A, e s) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Real.rpow_sum_of_pos hZ]


section
variable (rayM : Ideal O) [NeZero rayM]
local instance l4aQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

theorem high_branch_marked {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ : ℝ) (hbΦ : 0 ≤ bΦ) {κ : Type} [Fintype κ] [Nonempty κ] (anchors : κ → Character)
    (η₀ : Character) (qf : ℝ) (hqf : 1/2 ≤ qf)
    (B₀ L₀ c₀ sourceMesh : ℝ) (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1) (hL : 1 < L₀) (hc0 : 0 ≤ c₀)
    (hc1 : c₀ < 1) (PP : PivotParams sourceMesh)
    (hparentSource : QRH.Record12518109Existence.UnitFaceSource
      ⟨B₀, L₀, 0, B₀, 0, c₀⟩ sourceMesh PP.εm)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hβ' : HeckeZeroSupremum.beta ≤ 7/8)
    (hRw : PP.Rwidth = 1) (hbin : PP.binWidth ≤ 1/4)
    (Mmin Mmax Mcap Lplain d ε₁ εb Lfix : ℝ) (hqlo : PP.qlo ≤ Mmin) (hQ : Mmax + εb ≤ PP.Q)
    (hεb : 0 < εb) (hMcap : 0 ≤ Mcap) (hd : 0 < d) (hdsupply : Mcap + 0 + 1 ≤ d)
    (hLp : 0 ≤ Lplain) (hε₁ : 0 < ε₁)
    (hplainBudget : 12*PP.e*(Lplain/d+2) + 8*PP.κ + 2*(ε₁/8) ≤ ε₁)
    (hLfix : 2*ε₁*d + 2*PP.εslot*d*(Fintype.card α : ℝ) +
      (PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) + PP.δ +
        2*PP.binWidth*(Fintype.card α : ℝ)) + εb + (Fintype.card α : ℝ)*PP.wmin ≤ Lfix) :
    ∃ J : ℕ, ∀ τ : ℝ, 0 < τ → τ < PP.dmin/2 → 4*τ < PP.dmin*PP.ηw → 2*τ < PP.dmin*PP.ηslot →
      128*τ ≤ d*ε₁ → ∃ K : ℝ, 0 < K ∧ ∃ S : Finset (ℕ×ℕ),
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 2 < Z^τ ∧
      ∀ (j : κ) (q : ℝ), qf ≤ q → q ≤ 3/4 →
      ∀ st : NaturalState Z 0 bΦ, st.character = anchors j → st.puncture = 1 →
        Mmin ≤ st.rowWidth → st.rowWidth ≤ Mmax → st.width ≤ Mcap →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
        (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t height : ℝ),
      (∀ k, 0 ≤ w k) → (∀ k, w k ≤ 1) → (∀ k, w k ≤ PP.mesh * PP.dmin) →
      (∀ k, (33/50:ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) → 0 ≤ height → (∀ k, |v' k| ≤ height) →
      1 + |t| + height ≤ Z^τ →
      ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun k => primePool rayM H 2 (Z^(w k)))
        (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
        (fun k => Z^(w k)) X₁ X₂
        (fun z => st.radial.keep z ∧
          ¬ lowRow rayM H hH st η₀ hQM hQη PP.e (Z^τ) q z)
        st.radial.profile st.radial.scale ≤
      K * QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
        Z^(st.rowWidth + highSupM B₀ L₀ c₀ q (length Z X₁ + length Z X₂) (∑ k, w k)
          st.rowWidth + (Lfix + τ*J)) := by
  classical
  set N : ℕ := Fintype.card α with hNdef
  obtain ⟨J, C1, hC1, hpiv⟩ := high_class_sum_marked (Slot := α) rayM H hH anchors η₀ B₀ L₀ c₀
    sourceMesh hB0 hB1 hL hc0 hc1 W hWs hW hβ PP bΦ (N:ℝ)
    (PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) + PP.δ + 2*PP.binWidth*(N:ℝ))
    le_rfl hparentSource
  obtain ⟨Cex, hCex, hexc⟩ := high_exceptional_count rayM H hH anchors η₀
  refine ⟨J, fun τ hτ hτ1 hτ2 hτ3 hτd => ?_⟩
  have hslotB : 8*PP.e*1 + PP.κ ≤ PP.εslot := by
    have := PP.hslotBudget; rw [hRw] at this; exact this
  obtain ⟨Kp, hKp, Sp, hplain⟩ := high_row_plain_factor rayM H hH W hWs hW bΦ Mcap Lplain d τ
    PP.εslot ε₁ PP.e PP.κ hbΦ hLp hd hdsupply hτ PP.hεslot hε₁ PP.he PP.he' PP.hκ PP.hκ' hslotB
    hplainBudget hτd
  obtain ⟨Cs, hCs, hslot⟩ := high_slot_bound rayM H hH W hWs hW bΦ Mcap d τ PP.εslot ε₁ PP.e
    PP.κ hbΦ hMcap hd hdsupply hτ PP.hεslot hε₁ PP.he PP.he' PP.hκ hslotB (by linarith)
  let nb : ℕ := Fintype.card (BufferIndex PP.e)
  have hnb : 0 < nb := Fintype.card_pos
  let Kc : ℝ := Kp * Cs^N * (C1 + Cex)
  have hKc : 0 < Kc := by
    have : 0 < Cs := zero_lt_one.trans_le hCs
    positivity
  refine ⟨nb * Kc, by positivity, Sp, ?_⟩
  filter_upwards [hpiv τ hτ hτ1 hτ2 hτ3, hplain η₀, hslot η₀,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    (tendsto_rpow_atTop hεb).eventually (eventually_ge_atTop bΦ),
    (tendsto_rpow_atTop hτ).eventually (eventually_ge_atTop ((bufferCount PP.e : ℕ) : ℝ))]
    with Z hZP hZpl hZsl hZτ hZb hZI
  refine ⟨hZP.1, hZτ, ?_⟩
  intro j q hq hq' st hchar hpun hMlo hMhi hwidth hQM hQη T θ w σ v' t height hw hw1 hwm hσ hσ' hh0
    hv' hx p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hZ1 : 1 < Z := hZP.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hZτ0 : 0 ≤ Z^τ := Real.rpow_nonneg hZ0.le _
  have hZτ1 : 1 ≤ Z^τ := by linarith
  set M : ℝ := st.rowWidth with hMdef
  set Pl : ℝ := length Z X₁ + length Z X₂ with hPl
  have hM0 : 0 ≤ M := st.row_nonneg
  have hmesh0 : 0 ≤ PP.mesh * PP.dmin := mul_nonneg PP.hmesh PP.hdmin.le
  -- extended slot data
  let w' : α → ℝ := extend T w 0
  let σ' : α → ℝ := extend T σ (33/50)
  let v'' : α → ℝ := extend T v' 0
  let θ' : α → RayQuotient.Characters rayM H := extend T θ 1
  have hw'0 : ∀ s, 0 ≤ w' s := extend_forall T w 0 (fun x => 0 ≤ x) hw le_rfl
  have hw'1 : ∀ s, w' s ≤ 1 := extend_forall T w 0 (fun x => x ≤ 1) hw1 zero_le_one
  have hw'm : ∀ s, w' s ≤ PP.mesh * PP.dmin :=
    extend_forall T w 0 (fun x => x ≤ PP.mesh * PP.dmin) hwm hmesh0
  have hσ'1 : ∀ s, (33/50:ℝ) ≤ σ' s := extend_forall T σ (33/50) (fun x => 33/50 ≤ x) hσ le_rfl
  have hσ'2 : ∀ s, σ' s ≤ 33/50 := extend_forall T σ (33/50) (fun x => x ≤ 33/50) hσ' le_rfl
  have hv'' : ∀ s, |v'' s| ≤ height := extend_forall T v' 0 (fun x => |x| ≤ height) hv' (by simpa using hh0)
  have hsumT : ∑ k : T, w k = ∑ s ∈ T, w' s := (sum_extend T w 0).symm
  -- the slot factors
  let f : α → O → ℝ := fun s z => max 1 ‖normalizedSlot st.character st.mask 1 z
    (primePool rayM H 2 (Z^(w' s)))
    (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ' s)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w' s)) (σ' s) (v'' s) I) t (Z^(w' s))‖
  have hprodT : ∀ z, ∏ k : T, max 1 ‖normalizedSlot st.character st.mask 1 z
      (primePool rayM H 2 (Z^(w k)))
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I) t (Z^(w k))‖ =
      ∏ s ∈ T, f s z := by
    intro z
    rw [← Finset.prod_coe_sort T (fun s => f s z)]
    apply Finset.prod_congr rfl
    intro k _
    simp only [f, w', σ', v'', θ', extend_coe]
  -- the large and small slots
  let TL : Finset α := T.filter (fun s => PP.wmin ≤ w' s)
  let TS : Finset α := T.filter (fun s => ¬ PP.wmin ≤ w' s)
  have hTL_sub : TL ⊆ T := Finset.filter_subset _ _
  have hTS_sub : TS ⊆ T := Finset.filter_subset _ _
  have hprod_split : ∀ z, ∏ s ∈ T, f s z = (∏ s ∈ TL, f s z) * ∏ s ∈ TS, f s z :=
    fun z => (Finset.prod_filter_mul_prod_filter_not T _ _).symm
  have hS_split : ∑ s ∈ T, w' s = ∑ s ∈ TL, w' s + ∑ s ∈ TS, w' s :=
    (Finset.sum_filter_add_sum_filter_not T _ _).symm
  have hSS : ∑ s ∈ TS, w' s ≤ (N:ℝ) * PP.wmin := by
    have h1 : ∑ s ∈ TS, w' s ≤ TS.card • PP.wmin :=
      Finset.sum_le_card_nsmul TS _ _ (fun s hs => (not_le.mp (Finset.mem_filter.mp hs).2).le)
    have h2 : (TS.card : ℝ) ≤ N := by
      exact_mod_cast Finset.card_le_univ TS
    rw [nsmul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 PP.hwmin.le)
  have hSL0 : 0 ≤ ∑ s ∈ TL, w' s := Finset.sum_nonneg (fun s _ => hw'0 s)
  have hSS0 : 0 ≤ ∑ s ∈ TS, w' s := Finset.sum_nonneg (fun s _ => hw'0 s)
  have hSLmax : ∑ s ∈ TL, w' s ≤ N := by
    calc ∑ s ∈ TL, w' s ≤ ∑ s ∈ T, w' s := Finset.sum_le_sum_of_subset_of_nonneg hTL_sub
          (fun s _ _ => hw'0 s)
      _ ≤ ∑ s ∈ T, (1:ℝ) := Finset.sum_le_sum (fun s _ => hw'1 s)
      _ = T.card := by simp
      _ ≤ N := by exact_mod_cast Finset.card_le_univ T
  -- the height windows
  have hwinP : ∀ i : ℕ, |t| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
    intro i
    have : (0:ℝ) ≤ i := Nat.cast_nonneg _
    push_cast
    nlinarith [abs_nonneg t, mul_nonneg this hZτ0]
  have hwinS : ∀ (i : ℕ) (s : α), |t + v'' s| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
    intro i s
    have : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have h1 := abs_add_le t (v'' s)
    have h2 := hv'' s
    push_cast
    nlinarith [abs_nonneg t, mul_nonneg this hZτ0]
  -- the row norm bound
  have hnormF : ∀ z, st.radial.keep z → st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
      ((Ideal.span {z}).absNorm : ℝ) ≤ Z^(M + εb) := by
    intro z hk hp
    have hs := st.radial_support hp
    have h1 : ‖eisEmbedding z‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h1
    calc ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ * Z^st.rowWidth := h1
      _ ≤ Z^εb * Z^st.rowWidth := mul_le_mul_of_nonneg_right hZb (Real.rpow_nonneg hZ0.le _)
      _ = Z^(M + εb) := by rw [← Real.rpow_add hZ0, add_comm]
  have hq12 : 1/2 ≤ q := hqf.trans hq
  have hq0 : 0 ≤ q := by linarith
  have hLroot0 : 0 ≤ PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) + PP.δ +
      2*PP.binWidth*(N:ℝ) := by
    have hdm : 0 ≤ PP.dmax := PP.hdmin.le.trans PP.hdmax
    have := PP.hεm; have := PP.hζ; have := PP.hη; have := PP.hε; have := PP.hmesh
    have := PP.hbin; have := PP.hδ
    positivity
  have hLfixA : 2*ε₁*d + 2*PP.εslot*d*(N:ℝ) + εb ≤ Lfix := by
    have : 0 ≤ (N:ℝ)*PP.wmin := mul_nonneg (Nat.cast_nonneg _) PP.hwmin.le
    linarith
  have hτJ : 0 ≤ τ*J := mul_nonneg hτ.le (Nat.cast_nonneg _)
  let sel := selectBin rayM H hH st η₀ hQM hQη PP.e (Z^τ)
  let ctl : ℝ := (p.control Sp)^2
  have hctl : 0 ≤ ctl := sq_nonneg _
  let Rc : BufferIndex PP.e → ℝ := fun c =>
    if (q+1)/2 ≤ bufferValue PP.e c ∧ bufferValue PP.e c ≤ 7/8 then
      Kc * ctl * Z^(M + highTermM B₀ L₀ c₀ (2*bufferValue PP.e c-1) Pl (∑ s ∈ T, w' s) M +
        (Lfix + τ*J))
    else 0
  have hclass : ∀ c : BufferIndex PP.e, ∀ rows : Finset O,
      (∀ z ∈ rows, (st.radial.keep z ∧ ¬ lowRow rayM H hH st η₀ hQM hQη PP.e (Z^τ) q z) ∧
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧ sel z = c) →
      ∑ z ∈ rows, ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        (fun k : T => primePool rayM H 2 (Z^(w k)))
        (fun (k : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
        (fun k : T => Z^(w k)) t X₁ X₂‖^2 ≤ Rc c := by
    intro c rows hrows
    by_cases hc : (q+1)/2 ≤ bufferValue PP.e c ∧ bufferValue PP.e c ≤ 7/8
    swap
    · have hempty : rows = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨⟨hk, hnl⟩, hp, hsel⟩ := hrows z hz
        have hbin := selectBin_spec rayM H hH st η₀ hQM hQη PP.e (Z^τ) PP.he hZτ hβ hβ' z hk
        have hhigh := selectBin_high rayM H hH st η₀ hQM hQη PP.e (Z^τ) q PP.he hZτ hβ hβ' z hk hnl
        change OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
          z hk PP.e (Z^τ) (sel z) at hbin
        change (q+1)/2 ≤ bufferValue PP.e (sel z) at hhigh
        rw [hsel] at hbin hhigh
        exact hc ⟨hhigh, hbin.2.2.2.2.1⟩
      rw [hempty, Finset.sum_empty]
      simp only [Rc, if_neg hc, le_refl]
    · obtain ⟨hc1', hc2'⟩ := hc
      set a : ℝ := bufferValue PP.e c with ha
      set i : ℕ := c.1.val with hi_def
      have hνq : q ≤ 2*a-1 := by linarith
      have hν34 : 2*a-1 ≤ 3/4 := by linarith
      have ha34 : 3/4 ≤ a := by linarith
      have hν12 : 1/2 ≤ 2*a-1 := by linarith
      have hiB : i ≤ bufferCount PP.e := Nat.lt_succ_iff.mp c.1.isLt
      have hiZ : (i:ℝ) ≤ Z^τ := (Nat.cast_le.mpr hiB).trans hZI
      have hrow : ∀ z ∈ rows, ∃ hk : st.radial.keep z,
          st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
          OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη z hk
            PP.e (Z^τ) c := by
        intro z hz
        obtain ⟨⟨hk, hnl⟩, hp, hsel⟩ := hrows z hz
        have hbin := selectBin_spec rayM H hH st η₀ hQM hQη PP.e (Z^τ) PP.he hZτ hβ hβ' z hk
        change OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
          z hk PP.e (Z^τ) (sel z) at hbin
        rw [hsel] at hbin
        exact ⟨hk, hp, hbin⟩
      have hpl : ∀ z ∈ rows, ‖positiveSlotRow st.character st.mask 1 z (p.profile 0)
          (p.profile 1) (fun k : T => primePool rayM H 2 (Z^(w k)))
          (fun (k : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
          (fun k : T => Z^(w k)) t X₁ X₂‖^2 ≤
          Kp * ctl * Z^((2*a-1)*Pl + 2*ε₁*d) * (∏ s ∈ T, f s z)^2 := by
        intro z hz
        obtain ⟨hk, hp, hbin⟩ := hrow z hz
        have hb := hZpl.2 st hwidth hQM hQη z hk hp a i hbin.2.2.1
          (by linarith [hbin.2.2.2.2.1]) hiZ hbin.2.2.2.2.2.2.2.2
          (fun k : T => primePool rayM H 2 (Z^(w k)))
          (fun (k : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
          (fun k : T => Z^(w k)) (fun k => Real.rpow_pos_of_pos hZ0 _) p X₁ X₂ t hX₁ hX₂ hl₁ hl₂
          (hwinP i)
        rw [hprodT z] at hb
        exact hb
      have hsl : ∀ z ∈ rows, ∀ s ∈ T,
          (f s z)^2 ≤ Cs * Z^(2*PP.εslot*d + (2*a-1) * w' s) := by
        intro z hz s hs
        obtain ⟨hk, hp, hbin⟩ := hrow z hz
        exact hZsl.2 st hwidth hQM hQη z hk hp a i hbin.2.2.1 (by linarith [hbin.2.2.2.2.1]) hiZ
          hbin.2.2.2.2.2.2.2.2 (w' s) (σ' s) t (v'' s) (θ' s) (hw'0 s) (hw'1 s) (hσ'1 s) (hσ'2 s)
          (hwinS i s)
      have hCs0 : 0 ≤ Cs := zero_le_one.trans hCs
      have hall : ∀ z ∈ rows, ∀ A ⊆ T, (∏ s ∈ A, f s z)^2 ≤
          Cs^N * Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ A, w' s) := by
        intro z hz A hA
        rw [← Finset.prod_pow]
        have h1 := prod_le_const_rpow A hZ0 (fun s => (f s z)^2)
          (fun s => 2*PP.εslot*d + (2*a-1) * w' s) (fun s hs => hsl z hz s (hA hs))
          (fun s _ => sq_nonneg _)
        refine h1.trans ?_
        have hcard : (A.card : ℝ) ≤ N := by exact_mod_cast Finset.card_le_univ A
        have hexp : ∑ s ∈ A, (2*PP.εslot*d + (2*a-1) * w' s) ≤
            2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ A, w' s := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          have : 0 ≤ 2*PP.εslot*d := by have := PP.hεslot; positivity
          nlinarith
        exact mul_le_mul (pow_le_pow_right₀ hCs (Finset.card_le_univ A))
          (Real.rpow_le_rpow_of_exponent_le hZ1.le hexp) (Real.rpow_nonneg hZ0.le _) (by positivity)
      let rowv : O → ℝ := fun z => ‖positiveSlotRow st.character st.mask 1 z (p.profile 0)
          (p.profile 1) (fun k : T => primePool rayM H 2 (Z^(w k)))
          (fun (k : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
          (fun k : T => Z^(w k)) t X₁ X₂‖^2
      let exc : O → Prop := fun z => ∃ hz0 : z ≠ 0,
        (wholeRegularDictionary rayM H hH (anchors j) η₀).exceptionalCore
          (sixthFrequencyEquiv.symm ⟨z, hz0⟩).1
      let Bp : ℝ := Kp * ctl * Z^((2*a-1)*Pl + 2*ε₁*d)
      have hBp : 0 ≤ Bp := by positivity
      let Eall : ℝ := Cs^N * Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ T, w' s)
      have hEall : 0 ≤ Eall := by positivity
      -- exceptional rows: count times the full-amplitude pointwise bound
      have hexcB : ∑ z ∈ rows.filter exc, rowv z ≤ (Cex * Z^((M+εb)/6)) * (Bp * Eall) := by
        have hcard : ((rows.filter exc).card : ℝ) ≤ Cex * Z^((M+εb)/6) := by
          have h := hexc j (Z^(M+εb)) (Real.one_le_rpow hZ1.le (by linarith)) (rows.filter exc) (by
            intro z hz
            obtain ⟨hzr, hzexc⟩ := Finset.mem_filter.mp hz
            obtain ⟨hk, hp, hbin⟩ := hrow z hzr
            obtain ⟨hz0, hz'⟩ := hzexc
            exact ⟨hz0, hnormF z hk hp, hz'⟩)
          rw [← Real.rpow_mul hZ0.le] at h
          have e : (M + εb) * (1/6:ℝ) = (M+εb)/6 := by ring
          rwa [e] at h
        calc ∑ z ∈ rows.filter exc, rowv z ≤ ∑ z ∈ rows.filter exc, (Bp * Eall) := by
              apply Finset.sum_le_sum
              intro z hz
              have hzr := (Finset.mem_filter.mp hz).1
              exact (hpl z hzr).trans (mul_le_mul_of_nonneg_left (hall z hzr T le_rfl) hBp)
          _ = (rows.filter exc).card * (Bp * Eall) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Cex * Z^((M+εb)/6)) * (Bp * Eall) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
      -- regular rows: the repeated-mark class sum on the large slots
      let Lroot : ℝ := PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) + PP.δ +
        2*PP.binWidth*(N:ℝ)
      have hLr : Lroot = PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) + PP.δ +
          2*PP.binWidth*(N:ℝ) := rfl
      let Bq : ℝ := Bp * (Cs^N * Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ TS, w' s))
      have hBq : 0 ≤ Bq := by positivity
      let Rreg : ℝ := C1 * Z^(τ*J) * Z^(unmarkedDensity (2*a-1) * (M+εb) +
        (2*a-1) * ∑ s ∈ TL, w' s -
        QRH.RepeatedMarks.Source.gainC (2*a-1) B₀ L₀ c₀ (∑ s ∈ TL, w' s) (M+εb) + Lroot)
      have hregB : ∑ z ∈ rows.filter (fun z => ¬ exc z), rowv z ≤ Bq * Rreg := by
        have hrowsreg : ∀ z ∈ rows.filter (fun z => ¬ exc z), ∃ hz : st.radial.keep z,
            OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη z hz
              PP.e (Z^τ) c ∧
            ((Ideal.span {z}).absNorm : ℝ) ≤ Z^(M+εb) ∧
            ¬ (wholeRegularDictionary rayM H hH (anchors j) η₀).exceptionalCore
              (sixthFrequencyEquiv.symm ⟨z, st.row_ne_zero z hz⟩).1 := by
          intro z hz
          obtain ⟨hzr, hnexc⟩ := Finset.mem_filter.mp hz
          obtain ⟨hk, hp, hbin⟩ := hrow z hzr
          exact ⟨hk, hbin, hnormF z hk hp, fun h => hnexc ⟨st.row_ne_zero z hk, h⟩⟩
        have hL1 := hZP.2 j st hchar hpun hQM hQη c (M+εb) ha34 (by linarith) (by linarith)
          (by linarith) (by linarith) (rows.filter (fun z => ¬ exc z)) TL w' σ' v'' t θ' hrowsreg
          (fun s hs => (Finset.mem_filter.mp hs).2) (fun s _ => hσ'1 s) (fun s _ => hσ'2 s)
          (fun s _ => hw'm s) hSLmax (hwinP i) (fun s _ => hwinS i s)
        have hL1' : ∑ z ∈ rows.filter (fun z => ¬ exc z), (∏ s ∈ TL, f s z)^2 ≤ Rreg := hL1
        calc ∑ z ∈ rows.filter (fun z => ¬ exc z), rowv z
            ≤ ∑ z ∈ rows.filter (fun z => ¬ exc z), Bq * (∏ s ∈ TL, f s z)^2 := by
              apply Finset.sum_le_sum
              intro z hz
              have hzr := (Finset.mem_filter.mp hz).1
              calc rowv z ≤ Bp * (∏ s ∈ T, f s z)^2 := hpl z hzr
                _ = Bp * ((∏ s ∈ TL, f s z)^2 * (∏ s ∈ TS, f s z)^2) := by
                    rw [hprod_split z, mul_pow]
                _ ≤ Bp * ((∏ s ∈ TL, f s z)^2 *
                      (Cs^N * Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ TS, w' s))) := by
                    apply mul_le_mul_of_nonneg_left _ hBp
                    exact mul_le_mul_of_nonneg_left (hall z hzr TS hTS_sub) (sq_nonneg _)
                _ = Bq * (∏ s ∈ TL, f s z)^2 := by simp only [Bq]; ring
          _ = Bq * ∑ z ∈ rows.filter (fun z => ¬ exc z), (∏ s ∈ TL, f s z)^2 := by
              rw [Finset.mul_sum]
          _ ≤ Bq * Rreg := mul_le_mul_of_nonneg_left hL1' hBq
      -- combine the exceptional and regular rows
      have hsplit := Finset.sum_filter_add_sum_filter_not rows exc (fun z => rowv z)
      have hRc : Rc c = Kc * ctl * Z^(M + highTermM B₀ L₀ c₀ (2*a-1) Pl (∑ s ∈ T, w' s) M +
          (Lfix + τ*J)) := by
        simp only [Rc]
        rw [if_pos ⟨hc1', hc2'⟩]
      rw [hRc]
      refine le_trans (le_of_eq hsplit.symm) ?_
      refine (add_le_add hexcB hregB).trans ?_
      have hX1 : Z^((M+εb)/6) * (Z^((2*a-1)*Pl + 2*ε₁*d) *
          Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ T, w' s)) ≤
          Z^(M + highTermM B₀ L₀ c₀ (2*a-1) Pl (∑ s ∈ T, w' s) M + (Lfix + τ*J)) := by
        rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        apply Real.rpow_le_rpow_of_exponent_le hZ1.le
        have := marked_exceptional_exponent (B₀ := B₀) (L₀ := L₀) (c₀ := c₀) (ν := 2*a-1)
          (M := M) (F := M+εb) (S := ∑ s ∈ T, w' s) (Pl := Pl) (εb := εb) (A1 := 2*ε₁*d)
          (B1 := 2*PP.εslot*d*N) (Lfix := Lfix) hν12 hν34 hB0 hB1 hL hc0 hc1.le hM0 le_rfl
          hεb.le hLfixA
        linarith
      have hX2 : Z^((2*a-1)*Pl + 2*ε₁*d) *
          Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ TS, w' s) *
          (Z^(τ*J) * Z^(unmarkedDensity (2*a-1) * (M+εb) + (2*a-1) * ∑ s ∈ TL, w' s -
            QRH.RepeatedMarks.Source.gainC (2*a-1) B₀ L₀ c₀ (∑ s ∈ TL, w' s) (M+εb) + Lroot)) ≤
          Z^(M + highTermM B₀ L₀ c₀ (2*a-1) Pl (∑ s ∈ T, w' s) M + (Lfix + τ*J)) := by
        rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
        apply Real.rpow_le_rpow_of_exponent_le hZ1.le
        have := marked_regular_exponent (B₀ := B₀) (L₀ := L₀) (c₀ := c₀) (ν := 2*a-1) (M := M)
          (F := M+εb) (S := ∑ s ∈ T, w' s) (SL := ∑ s ∈ TL, w' s) (SS := ∑ s ∈ TS, w' s)
          (Pl := Pl) (εb := εb) (A1 := 2*ε₁*d) (B1 := 2*PP.εslot*d*N) (L0 := Lroot)
          (nw := (N:ℝ)*PP.wmin) (Lfix := Lfix) (τJ := τ*J) hν12 hν34 hB0 hB1 hL hc0 hc1.le
          (by linarith) le_rfl hS_split hSS hSS0 (by linarith [hLfix, hLr])
        linarith
      calc (Cex * Z^((M+εb)/6)) * (Bp * Eall) + Bq * Rreg
          = Kp * Cs^N * ctl * (Cex * (Z^((M+εb)/6) * (Z^((2*a-1)*Pl + 2*ε₁*d) *
              Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ T, w' s))) +
            C1 * (Z^((2*a-1)*Pl + 2*ε₁*d) * Z^(2*PP.εslot*d*N + (2*a-1) * ∑ s ∈ TS, w' s) *
              (Z^(τ*J) * Z^(unmarkedDensity (2*a-1) * (M+εb) + (2*a-1) * ∑ s ∈ TL, w' s -
                QRH.RepeatedMarks.Source.gainC (2*a-1) B₀ L₀ c₀ (∑ s ∈ TL, w' s) (M+εb) +
                Lroot)))) := by
            simp only [Bp, Bq, Eall, Rreg]; ring
        _ ≤ Kp * Cs^N * ctl *
            (Cex * Z^(M + highTermM B₀ L₀ c₀ (2*a-1) Pl (∑ s ∈ T, w' s) M + (Lfix + τ*J)) +
             C1 * Z^(M + highTermM B₀ L₀ c₀ (2*a-1) Pl (∑ s ∈ T, w' s) M + (Lfix + τ*J))) := by
            have hCs1 : 0 ≤ Kp * Cs^N * ctl := by positivity
            apply mul_le_mul_of_nonneg_left _ hCs1
            exact add_le_add (mul_le_mul_of_nonneg_left hX1 hCex.le)
              (mul_le_mul_of_nonneg_left hX2 hC1.le)
        _ = Kc * ctl * Z^(M + highTermM B₀ L₀ c₀ (2*a-1) Pl (∑ s ∈ T, w' s) M + (Lfix + τ*J)) := by
            simp only [Kc]; ring
  -- sum over the classes
  have hE := energy_le_class_sums st.character st.mask 1 t (p.profile 0) (p.profile 1)
    (fun k : T => primePool rayM H 2 (Z^(w k)))
    (fun (k : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
    (fun k : T => Z^(w k)) X₁ X₂
    (fun z => st.radial.keep z ∧ ¬ lowRow rayM H hH st η₀ hQM hQη PP.e (Z^τ) q z)
    st.radial.profile st.radial.scale bΦ st.radial.scale_pos st.radial_support sel Rc hclass
  refine hE.trans ?_
  have hsumRc : ∑ c, Rc c ≤ nb * (Kc * ctl * Z^(M + highSupM B₀ L₀ c₀ q Pl (∑ s ∈ T, w' s) M +
      (Lfix + τ*J))) := by
    calc ∑ c, Rc c ≤ ∑ _c : BufferIndex PP.e, (Kc * ctl * Z^(M + highSupM B₀ L₀ c₀ q Pl
          (∑ s ∈ T, w' s) M + (Lfix + τ*J))) := by
          apply Finset.sum_le_sum
          intro c _
          by_cases hc : (q+1)/2 ≤ bufferValue PP.e c ∧ bufferValue PP.e c ≤ 7/8
          · simp only [Rc, if_pos hc]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.rpow_le_rpow_of_exponent_le hZ1.le
            have := le_highSupM B₀ L₀ c₀ hq0 (ν := 2*bufferValue PP.e c-1)
              (by linarith [hc.1]) (by linarith [hc.2]) Pl (∑ s ∈ T, w' s) M
            linarith
          · simp only [Rc, if_neg hc]; positivity
      _ = nb * (Kc * ctl * Z^(M + highSupM B₀ L₀ c₀ q Pl (∑ s ∈ T, w' s) M + (Lfix + τ*J))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsumT]
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  calc QuadraticInitialBound.diagonalControl st.radial.profile * ∑ c, Rc c
      ≤ QuadraticInitialBound.diagonalControl st.radial.profile * (nb * (Kc * ctl *
        Z^(M + highSupM B₀ L₀ c₀ q Pl (∑ s ∈ T, w' s) M + (Lfix + τ*J)))) :=
        mul_le_mul_of_nonneg_left hsumRc hdiag
    _ = _ := by simp only [ctl, M, Pl]; ring


end
end
end QRH.ArviDensity.Density
