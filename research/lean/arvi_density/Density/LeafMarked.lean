/- Copyright (c) 2026 Sil, ArviFoxy. Apache-2.0.
The density-split instance of Seam A with the marked HIGH count (DS §§3–4, final source audit
§§2–5, 7; PR 76 repeated marks).

`density_priced_source_marked`: from the parent `G(B₀,L₀,c₀)` (at `M = 1`, on the range
`22/23 ≤ B₀ ≤ 1`, `1 < L₀`, `0 ≤ c₀ < 1`), the packed leaf with the marked density price
`max (q(w₀)·deletionNeed) (sup_{ν∈[q(w₀),3/4]} highTermM ν)`, `q = densQ` (clipped to `[qf,3/4]`),
on `[Mmin, Mmax]`, uniformly in the live width `w₀` (quantified after `∀ᶠ Z`). The HIGH term is
the unmarked `highTerm` reduced by PR 76's repeated-mark gain `gainC`.

Quantifier order (all choices before `∀ᶠ Z`, none depending on `q`):
1. `ε`; the parent unit mesh at loss `ε/(4·max 1 Mmax)`; the native mesh; the master loss `θ` of the
   marked HIGH branch and the parent source mesh at loss `θ`; `meshMax`.
2. `α, rayM, H, W, bΦ`, the anchors, `η₀`, `Q`; native, parent and zero-slot constants.
3. Scalars after `N = card α`: `Mcap = Mmax+ε/8`, `d = Mcap+1`, `ε₁ = ε/(16d(N+1))`, the pivot
   parameters `PP = highParams …` (bin buffer `e`, `κ`, slot floor `wmin = θ/(N+1)`, …).
4. The density degree `J` of the marked class count (`high_branch_marked`); then the height scale
   `τ ≤ ε/(16(J+1))` (and the pivot's bounds); then the HIGH and LOW (uniform-in-`q`) constants.
5. `∀ᶠ Z`; then the anchor index, `w₀` (hence `q`), the packed data.
Rows: the packed energy is the energy of `packedState`; it splits by the q-free buffered selector at
base height `Z^τ` into LOW rows (greedy erasure of whole slots of width `∈ [need, need+mesh]` at cost
`Z^{q·w}` per slot, then the parent at the retained slots, or the zero-slot energy when the ordinary
lengths alone leave the face) and HIGH rows (the marked class sums per bin). Heights above `Z^τ`
use the native bound with the polynomial height factor.

Fork of the density-split leaf `Density/Leaf` of this package (Sil's PR 83 with the floor `qf`): the
HIGH branch is `high_branch_marked`, the price `markedDensityPrice`; the bounded-height regime is cut
at `Z^τ` (`h = 0`, the pivot's bin heights) instead of `Z^{dvg/16}`, the native branch absorbing
`Z^{3/4 N}` with `k = ⌈(3/4)N/τ⌉`; the mesh is further bounded by `θ·Mmin/2` and
`sourceMesh·Mmin/2`; the parent face needs `22/23 ≤ B₀`, `1 < L₀`, `c₀ < 1`. -/
import Submissions.sil_density_split_20261026.Density.LeafLow
import Submissions.arvi_density.Density.Leaf
import Submissions.arvi_density.Density.LeafHighEnergyMarked
import Submissions.arvi_density.Density.PriceMarked
import Submissions.arvi_density.Density.HighParams
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Parent

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QRH.ArviDensity.Density
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open LocalMoment
local notation "O" => HeckeFamily.O
local instance densityLeafMarkedQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-! ### The density leaf -/

/-- **Density Seam A with the floor `qf` and the marked HIGH count.** From the parent `G(B₀,L₀,c₀)`
at `M = 1` on the range `22/23 ≤ B₀ ≤ 1`, `1 < L₀`, `0 ≤ c₀ < 1`, the packed leaf with the marked
density-split price (cut `q = densQ qf …`, `1/2 ≤ qf ≤ 3/4`) on `[Mmin, Mmax]`. -/
theorem density_priced_source_marked (qf B₀ L₀ c₀ L A D s₀ Mmin Mmax Lplain : ℝ) (hL : 1 < L₀)
    (hqf : 1/2 ≤ qf) (hqf' : qf ≤ 3/4)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hface : 22/23 ≤ B₀ ∧ B₀ ≤ 1 ∧ 0 ≤ c₀ ∧ c₀ < 1) (h0 : 0 < Mmin) (h1 : Mmin ≤ Mmax)
    (hparent : QRH.Record1252270103Source.GlobalSource B₀ L₀ c₀) :
    PricedPackedSource (markedDensityPrice qf B₀ L₀ c₀ L A D s₀ hL hface hqf hqf') Mmin Mmax
      Lplain := by
  obtain ⟨hB0, hB1, hc0, hc1⟩ := hface
  have hL0 : 0 < L₀ := zero_lt_one.trans hL
  intro ε hε
  have hβ' : HeckeZeroSupremum.beta ≤ 7/8 := by
    have := Candidate.FourthPower.IncumbentInput.native_kappa_bound
    linarith
  obtain ⟨meshN, hmeshN, hnat⟩ := native_priced_source hβ Mmin Mmax Lplain h0 h1 ε hε
  have hMmax : 0 < Mmax := h0.trans_le h1
  have hden : 0 < max (1:ℝ) Mmax := zero_lt_one.trans_le (le_max_left _ _)
  have hue : 0 < (ε/4)/(max 1 Mmax) := div_pos (by positivity) hden
  obtain ⟨unitMesh, hum, hu⟩ := hparent ((ε/4)/(max 1 Mmax)) hue
  have he4 : Mmax*((ε/4)/(max 1 Mmax)) ≤ ε/4 := by
    calc Mmax*((ε/4)/(max 1 Mmax)) ≤ (max 1 Mmax)*((ε/4)/(max 1 Mmax)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hue.le
      _ = ε/4 := mul_div_cancel₀ _ hden.ne'
  -- the master loss of the marked HIGH branch and the parent source mesh at that loss
  set θm : ℝ := min (1/100000) (ε/(16*(159*(Mmax+1)+5))) with hθmdef
  have hθm : 0 < θm := lt_min (by norm_num) (by positivity)
  have hθm1 : θm ≤ 1/100000 := min_le_left _ _
  have hθmε : (159*(Mmax+1)+5)*θm ≤ ε/16 := by
    have h := min_le_right (1/100000:ℝ) (ε/(16*(159*(Mmax+1)+5)))
    rw [← hθmdef, le_div_iff₀ (by positivity)] at h
    nlinarith
  obtain ⟨sourceMesh, hsm, hparentH⟩ := hparent θm hθm
  have hmeshPos : 0 < min (min (min (unitMesh*Mmin) meshN) (min (ε/8) 1))
      (min (θm*(Mmin/2)) (sourceMesh*(Mmin/2))) :=
    lt_min (lt_min (lt_min (mul_pos hum h0) hmeshN) (lt_min (by positivity) one_pos))
      (lt_min (by positivity) (by positivity))
  refine ⟨min (min (min (unitMesh*Mmin) meshN) (min (ε/8) 1))
    (min (θm*(Mmin/2)) (sourceMesh*(Mmin/2))), hmeshPos, ?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ Q hQ hQ0 hQt hQ72
  -- an empty anchor family makes the statement vacuous
  rcases isEmpty_or_nonempty κ with hκe | hκn
  · exact ⟨0, ∅, 1, one_pos, Filter.Eventually.of_forall (fun _ j => isEmptyElim j)⟩
  have hκn' := hκn
  have hm' : max 0 mesh ≤ min (min (min (unitMesh*Mmin) meshN) (min (ε/8) 1))
      (min (θm*(Mmin/2)) (sourceMesh*(Mmin/2))) := max_le hmeshPos.le hmesh
  have hmA : max 0 mesh ≤ min (min (unitMesh*Mmin) meshN) (min (ε/8) 1) :=
    hm'.trans (min_le_left _ _)
  have hmU : max 0 mesh ≤ unitMesh*Mmin :=
    hmA.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmN : mesh ≤ meshN :=
    (le_max_right 0 mesh).trans (hmA.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hmE : max 0 mesh ≤ ε/8 := hmA.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm1 : max 0 mesh ≤ 1 := hmA.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmθ : max 0 mesh ≤ θm*(Mmin/2) := hm'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmS : max 0 mesh ≤ sourceMesh*(Mmin/2) :=
    hm'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmesh1 : mesh ≤ 1 := (le_max_right 0 mesh).trans hm1
  -- native (large heights) and parent constants
  obtain ⟨degN, SN, CN, hCN, hevN⟩ := hnat mesh hmN α rayM H hH W hW hWs bΦ hbΦ κ anchors η₀ Q
    hQ hQ0 hQt hQ72
  obtain ⟨degP, SP, CP, hCP, hevP⟩ :=
    QRH.Record1252270103Source.PhysicalParentSources.unit_source_finite_anchors (α:=α) hu
      rayM H hH W hW hWs bΦ (max 0 mesh) Mmin Mmax (ε/4) hbΦ h0 hum.le hmU hue.le he4
      anchors η₀ Q hQ hQ0 hQt hQ72
  -- scalars
  set N : ℕ := Fintype.card α with hNdef
  set Mcap : ℝ := Mmax + ε/8 with hMcap
  set d : ℝ := Mcap + 1 with hddef
  set Lp : ℝ := max Lplain 0 with hLp
  have hd : 0 < d := by rw [hddef, hMcap]; positivity
  have hLp0 : 0 ≤ Lp := le_max_right _ _
  have hN1 : (0:ℝ) < (N:ℝ) + 1 := by positivity
  set ε₁ : ℝ := ε/(16*d*((N:ℝ)+1)) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  have hε₁d : 2*ε₁*d*((N:ℝ)+1) = ε/8 := by
    rw [hε₁def]; field_simp; ring
  have hd1 : 1 ≤ d := by rw [hddef, hMcap]; linarith
  have hMcap0 : 0 ≤ Mcap := by rw [hMcap]; positivity
  have hdinv : 0 ≤ 1/d := by positivity
  have hLd : 0 ≤ Lp/d := div_nonneg hLp0 hd.le
  -- the pivot parameters of the marked HIGH branch
  set PP : PivotParams sourceMesh := highParams Mmin Mmax θm sourceMesh ε₁ (Lp/d) (max 0 mesh) N
    hθm hθm1 h0 h1 hε₁ hLd (le_max_left _ _) hmθ hmS with hPPdef
  obtain ⟨hRw, hbinPP, hqloPP, hQPP, hplainPP, hslotleε₁, hηwPP, hηslotPP, hmeshmul, hεpPP, hεmPP,
      hδPP, hlossPP⟩ := highParams_facts Mmin Mmax θm sourceMesh ε₁ (Lp/d) (max 0 mesh) d N hθm hθm1
    h0 h1 hε₁ hLd (le_max_left _ _) hmθ hmS hd.le
  set kap : ℝ := PP.κ with hkapdef
  have hkap : 0 < kap := PP.hκ
  have hkap1 : kap ≤ 1 := PP.hκ'
  set vg : ℝ := ε₁/8 with hvg
  have hvg0 : 0 < vg := by positivity
  set e : ℝ := PP.e with hedef
  have he : 0 < e := PP.he
  have he' : e < 1/1000 := PP.he'
  have hslotB : 8*e*(1/d)+kap ≤ ε₁ := by
    have h1' := PP.hslotBudget
    rw [hRw] at h1'
    have : 8*PP.e*(1/d) ≤ 8*PP.e*1 :=
      mul_le_mul_of_nonneg_left (by rw [div_le_one hd]; exact hd1) (by positivity)
    linarith
  have hplainB : 12*e*(Lp/d+2)+8*kap+2*vg ≤ ε₁ := hplainPP
  -- zero-slot energy (all slots erased)
  haveI : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  obtain ⟨degZ, SZ, hceZ⟩ := Candidate.FourthPower.NativeNonfixedEnergy.canonical_energy
    rayM H hH (∅ : Finset α) W 1 2 (1/4) (9/4) bΦ Mcap Lplain 1 (ε/4)
    (33/50) (33/50) (3/4) one_pos hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by positivity) zero_le_one (by positivity) hβ
    Candidate.FourthPower.IncumbentInput.native_kappa_bound (internalQ Q η₀) hQt hQ72
    (inf_le_left.trans hQ)
  obtain ⟨CZ, hCZ, hevZ⟩ := hceZ η₀ inf_le_right
  -- HIGH: the marked class count; the density degree, then the height scale
  have hLfixPP : 2*ε₁*d + 2*PP.εslot*d*(N:ℝ) + (PP.dmax*(155*PP.εp + PP.mesh + PP.εm +
      (3/4)*PP.ζ + PP.η) + PP.δ + 2*PP.binWidth*(N:ℝ)) + θm + (N:ℝ)*PP.wmin ≤ ε/8 + ε/16 := by
    have := hlossPP
    linarith
  obtain ⟨J, hJ⟩ := high_branch_marked rayM H hH (α := α) W hWs hW bΦ (by linarith) anchors η₀ qf
    hqf B₀ L₀ c₀ sourceMesh hB0 hB1 hL hc0 hc1 PP hparentH hβ hβ' hRw hbinPP Mmin Mmax Mcap Lp d
    ε₁ θm (ε/8 + ε/16) hqloPP hQPP hθm hMcap0 hd (by linarith) hLp0 hε₁ hplainPP hLfixPP
  set τ : ℝ := min (min (ε/(16*((J:ℝ)+1))) (d*ε₁/128))
    (min (PP.dmin/4) (min (PP.dmin*PP.ηw/8) (PP.dmin*PP.ηslot/4))) with hτdef
  have hτ : 0 < τ := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by have := PP.hdmin; positivity) (lt_min (by have := PP.hdmin; have := hηwPP; positivity)
      (by have := PP.hdmin; have := hηslotPP; positivity)))
  have hτJ : τ*J ≤ ε/16 := by
    have h1 : τ ≤ ε/(16*((J:ℝ)+1)) := (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have : (0:ℝ) ≤ J := Nat.cast_nonneg _
    linarith
  have hτd : τ ≤ d*ε₁/128 := (min_le_left _ _).trans (min_le_right _ _)
  have hτ1 : τ < PP.dmin/2 := by
    have h1 : τ ≤ PP.dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
    have := PP.hdmin
    linarith
  have hτ2 : 4*τ < PP.dmin*PP.ηw := by
    have h1 : τ ≤ PP.dmin*PP.ηw/8 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have := mul_pos PP.hdmin hηwPP
    linarith
  have hτ3 : 2*τ < PP.dmin*PP.ηslot := by
    have h1 : τ ≤ PP.dmin*PP.ηslot/4 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have := mul_pos PP.hdmin hηslotPP
    linarith
  obtain ⟨KH, hKH, SH, hevH⟩ := hJ τ hτ hτ1 hτ2 hτ3 (by linarith)
  -- LOW: uniform in the cut
  obtain ⟨CL, hCL, hevL⟩ := low_branch rayM H hH (α := α) W hWs hW (1/d) d τ ε₁ e kap vg
    (33/50) (33/50) bΦ Mcap d hdinv hd.le hτ hε₁ he he' hkap hvg0.le hslotB (by linarith)
    hd (by linarith) le_rfl
  -- large heights
  have hcτ : 4*τ + 4*τ ≤ d*vg/2 := by
    have : τ ≤ d*vg/16 := by rw [hvg]; linarith
    linarith
  set k : ℕ := ⌈(3/4*(N:ℝ))/τ⌉₊ with hkdef
  have hck : 3/4*(N:ℝ) ≤ τ*k := by
    have := Nat.le_ceil ((3/4*(N:ℝ))/τ)
    rw [← hkdef, div_le_iff₀ hτ] at this
    linarith
  set B : ℕ := bufferCount e with hBdef
  refine ⟨degN + k + degP + degZ, SN ∪ SP ∪ SZ ∪ SH,
    CN + (max 1 CL)^N*(CP + CZ) + KH, by positivity, ?_⟩
  have hanch : ∀ᶠ Z : ℝ in atTop, ∀ j, ((anchors j).modulus.absNorm : ℝ) ≤ Z^(ε/8) :=
    eventually_all.mpr (fun j =>
      (tendsto_rpow_atTop (by positivity : (0:ℝ) < ε/8)).eventually (eventually_ge_atTop _))
  have hgateE : ∀ᶠ Z : ℝ in atTop, (9*((B:ℝ)+1))^4 ≤ Z^(d*vg/2) :=
    (tendsto_rpow_atTop (by positivity : (0:ℝ) < d*vg/2)).eventually (eventually_ge_atTop _)
  filter_upwards [hevN, hevP, hevZ, hevL η₀, hevH, hanch, hgateE]
    with Z hZN hZP hZZ hZL hZH hZa hZg
  clear hevN hevP hevZ hevL hevH hanch hgateE hJ hceZ hnat hu hparent
  have hmaxN : 0 ≤ (max 1 CL)^N := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hAP : 0 ≤ (max 1 CL)^N*CP := mul_nonneg hmaxN hCP.le
  have hAZ : 0 ≤ (max 1 CL)^N*CZ := mul_nonneg hmaxN hCZ.le
  have hAsplit : (max 1 CL)^N*(CP + CZ) = (max 1 CL)^N*CP + (max 1 CL)^N*CZ := mul_add _ _ _
  have hε₁dN : 2*ε₁*d*(N:ℝ) ≤ ε/8 := by
    have h2 : 0 ≤ 2*ε₁*d := by positivity
    have : 2*ε₁*d*((N:ℝ)+1) = 2*ε₁*d*N + 2*ε₁*d := by ring
    linarith
  intro j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  rw [markedDensityPrice_f]
  have hZ1 : 1 < Z := hZL.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hbase : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hdg := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  set S := SN ∪ SP ∪ SZ ∪ SH with hSdef
  have hcN : p.control SN ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_left.trans (Finset.subset_union_left.trans
        Finset.subset_union_left))
  have hcP : p.control SP ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_right.trans (Finset.subset_union_left.trans
        Finset.subset_union_left))
  have hcZ : p.control SZ ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p
      (Finset.subset_union_right.trans Finset.subset_union_left)
  have hcH : p.control SH ≤ p.control S :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p Finset.subset_union_right
  set M := Real.logb Z (((Ideal.span {V}).absNorm : ℝ) * K) with hMdef
  set q : ℝ := densQ qf B₀ L₀ L A D s₀ w₀ with hqdef
  have hq0 : qf ≤ q := densQ_ge _ _ _ _ _ _ _ _
  have hq1 : q ≤ 3/4 := densQ_le _ _ _ _ _ _ _ _ hqf'
  set Pl : ℝ := length Z X₁ + length Z X₂ with hPl
  set need := deletionNeed B₀ L₀ c₀ Pl (∑ i, w i) M with hneed
  have hlowle : q*need ≤ max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) := le_max_left _ _
  have hhighle : highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M ≤ max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) :=
    le_max_right _ _
  have hneed0 : 0 ≤ need := deletionNeed_nonneg _ _ _ _ _ _
  have hprice0 : 0 ≤ max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) :=
    (mul_nonneg (by linarith) hneed0).trans hlowle
  have hCtot : 0 ≤ CN + (max 1 CL)^N*(CP + CZ) + KH := by positivity
  by_cases hlarge : Z^τ < 1+|t|+height
  · ---------------- large heights: native bound with the height factor
    have hn := hZN j w₀ T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos
      p X₁ X₂ hX₁ hX₂ hl₁ hl₂
    rw [nativePrice_f, max_eq_right hs0, ← hMdef] at hn
    refine hn.trans ?_
    have hsN : ∑ i, w i ≤ N := by
      calc ∑ i, w i ≤ ∑ _i : T, (1:ℝ) :=
            Finset.sum_le_sum (fun i _ => (hwm i).trans hmesh1)
        _ = (Fintype.card T : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        _ ≤ N := by exact_mod_cast Fintype.card_le_of_injective _ Subtype.val_injective
    have hZk : Z^(3/4*∑ i, w i) ≤ (1+|t|+height)^k := by
      calc Z^(3/4*∑ i, w i) ≤ Z^(τ*k) :=
            Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
        _ = (Z^τ)^k := by rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
        _ ≤ (1+|t|+height)^k :=
            pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) hlarge.le k
    have hsplitZ : Z^(M + 3/4*∑ i, w i + ε) = Z^(3/4*∑ i, w i) * Z^(M + ε) := by
      rw [← Real.rpow_add hZ0]; ring_nf
    rw [hsplitZ]
    have hZ2 : Z^(M+ε) ≤ Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
    have hpc := p.control_nonneg SN
    calc CN*QuadraticInitialBound.diagonalControl Φ*(p.control SN)^2*(1+|t|+height)^degN*
          (Z^(3/4*∑ i, w i) * Z^(M + ε))
        ≤ CN*QuadraticInitialBound.diagonalControl Φ*(p.control SN)^2*(1+|t|+height)^degN*
          ((1+|t|+height)^k * Z^(M + ε)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hZk (Real.rpow_nonneg hZ0.le _)
      _ = CN*QuadraticInitialBound.diagonalControl Φ*(p.control SN)^2*
          (1+|t|+height)^(degN+k)*Z^(M + ε) := by rw [pow_add]; ring
      _ ≤ _ := scale_le hCN.le (by linarith) hdg (p.control_nonneg SN) hcN hbase
          (by omega) hZ1.le (by linarith)
  · ---------------- bounded heights: LOW/HIGH split
    replace hlarge := not_lt.mp hlarge
    have hM0 : 0 ≤ M := h0.le.trans hM₁
    have hUpos := packed_scale_pos V hV hK
    have hUM : ((Ideal.span {V}).absNorm : ℝ) * K = Z^M := packed_scale_eq hZ1 V hV hK
    have hZτ1 : 1 ≤ Z^τ := Real.one_le_rpow hZ1.le hτ.le
    set x : ℝ := |t| + height with hxdef
    have hx0 : 0 ≤ x := by rw [hxdef]; positivity
    obtain ⟨h, hh0⟩ : ∃ h : ℕ, h = 0 := ⟨0, rfl⟩
    have hT0 : (((h+1 : ℕ) : ℝ)*Z^τ) = Z^τ := by rw [hh0]; simp
    have hwin : |t| + height + Z^τ/2 ≤ (3*h+2 : ℕ)*Z^τ := by
      rw [hh0]; push_cast
      have := abs_nonneg t
      nlinarith
    have hgate4 : (3 + 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ)^4 ≤ (Z^d)^vg :=
      height_gate hZ1.le hτ.le hτ.le hcτ hZg (base := x) (by rw [hh0]; push_cast; linarith)
        (by linarith)
    have hgate2 : (3 + 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ)^2 ≤ (Z^d)^vg := by
      have h1 : (1:ℝ) ≤ 3 + 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ := by
        have : (0:ℝ) ≤ 3*(((B+1)*(h+1) : ℕ) : ℝ)*Z^τ := by positivity
        linarith
      exact (pow_le_pow_right₀ h1 (by norm_num)).trans hgate4
    -- the natural state at scale `N(V)K = Z^M`
    let st := packedState (anchors j) (internalQ Q η₀) Φ bΦ Z
      (((Ideal.span {V}).absNorm : ℝ) * K) M (ε/8) hZ1.le hM0 (by positivity) hUpos hUM hΦ
      hΦpos (hZa j)
    have hwidth : st.width ≤ Mcap := by
      change M + ε/8 ≤ Mmax + ε/8
      linarith
    have hQM : st.fixedModulus ≤ rayM := inf_le_left.trans hQ
    have hQη : st.fixedModulus ≤ η₀.modulus := inf_le_right
    -- sublattice packing
    have hpack := Packet.packed_energy_le (anchors j) (fixedBadMask*idealGenerator 1) V hV t
      (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
      ((p.support 0).trans Set.Icc_subset_Iic_self) ((p.support 1).trans Set.Icc_subset_Iic_self)
      hX₁ hX₂ (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) (initialKeep (anchors j) (internalQ Q η₀)) Φ hΦpos K hK
    let Lw := lowRow rayM H hH st η₀ hQM hQη e (Z^τ) q
    have hsplit := energy_split st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ st.radial.keep Lw st.radial.profile st.radial.scale bΦ
      st.radial.scale_pos st.radial_support
    -- HIGH rows
    have hmeshPP : mesh ≤ PP.mesh * PP.dmin := by
      rw [hmeshmul]; exact le_max_right _ _
    have hl₁' : length Z X₁ ≤ Lp := hl₁.trans (le_max_left _ _)
    have hl₂' : length Z X₂ ≤ Lp := hl₂.trans (le_max_left _ _)
    have hhigh := hZH.2.2 j q hq0 hq1 st rfl rfl hM₁ hM₂ hwidth hQM hQη T θ w σ v t height hw
      (fun i => (hwm i).trans hmesh1)
      (fun i => (hwm i).trans hmeshPP) hσ₁ hσ₂ hh hv (by linarith) p X₁ X₂ hX₁ hX₂ hl₁' hl₂'
    have hhighB : energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool rayM H 2 (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i => Z^(w i)) X₁ X₂ (fun z => st.radial.keep z ∧ ¬ Lw z)
        st.radial.profile st.radial.scale ≤
        KH*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ)*
          Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε) := by
      have h1 : KH*QuadraticInitialBound.diagonalControl Φ*(p.control SH)^2*
          Z^(M + highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M + (ε/8 + ε/16 + τ*J)) =
          KH*QuadraticInitialBound.diagonalControl Φ*(p.control SH)^2*(1+|t|+height)^0*
          Z^(M + highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M + (ε/8 + ε/16 + τ*J)) := by
        rw [pow_zero, mul_one]
      refine hhigh.trans ((le_of_eq h1).trans (scale_le hKH.le (by linarith) hdg
        (p.control_nonneg SH) hcH hbase (Nat.zero_le _) hZ1.le ?_))
      linarith
    -- LOW rows
    have hw' : ∀ i, 0 ≤ extend T w 0 i := extend_forall T w 0 (fun x => 0 ≤ x) hw le_rfl
    have hwm' : ∀ i, extend T w 0 i ≤ max 0 mesh :=
      extend_forall T w 0 (fun x => x ≤ max 0 mesh) (fun i => (hwm i).trans (le_max_right _ _))
        (le_max_left _ _)
    have hwr' : ∀ i, extend T w 0 i / d ≤ 1/d :=
      fun i => div_le_div_of_nonneg_right ((hwm' i).trans hm1) hd.le
    have hσ₁' : ∀ i, (33/50:ℝ) ≤ extend T σ (33/50) i :=
      extend_forall T σ (33/50) (fun x => 33/50 ≤ x) hσ₁ le_rfl
    have hσ₂' : ∀ i, extend T σ (33/50) i ≤ 33/50 :=
      extend_forall T σ (33/50) (fun x => x ≤ 33/50) hσ₂ le_rfl
    have hv' : ∀ i, |extend T v 0 i| ≤ height :=
      extend_forall T v 0 (fun x => |x| ≤ height) hv (by simpa using hh)
    have hwinL : ∀ i, |t + extend T v 0 i| + Z^τ/2 ≤ (3*h+2 : ℕ)*Z^τ := by
      intro i
      have := abs_add_le t (extend T v 0 i)
      have := hv' i
      linarith
    have hsT : ∑ i ∈ T, extend T w 0 i = ∑ i, w i := sum_extend T w 0
    have hlowB : energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool rayM H 2 (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i => Z^(w i)) X₁ X₂ (fun z => st.radial.keep z ∧ Lw z)
        st.radial.profile st.radial.scale ≤
        ((max 1 CL)^N*(CP + CZ))*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ)*
          Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε) := by
      by_cases hfall : B₀ * M < Pl
      · -- the ordinary lengths alone leave the face: erase every slot
        have hneedS : need = ∑ i, w i := deletionNeed_eq_self_of_lengths hL0 hs0 hfall
        have hlow := hZL.2 q (by linarith) (by linarith) st rfl hwidth hQM hQη h
          (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t T ∅
          (Finset.empty_subset _) (fun i _ => hw' i) (fun i _ => hwr' i)
          (fun i _ => hσ₁' i) (fun i _ => hσ₂' i) (fun i _ => hwinL i) hgate2
          (p.profile 0) (p.profile 1) X₁ X₂ (mul_pos hX₁ hX₂).le
        simp only [extend_coe, hT0] at hlow
        have hz := hZZ.2 (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t
          height (fun i hi => absurd hi (Finset.notMem_empty i))
          (fun i hi => absurd hi (Finset.notMem_empty i))
          (fun i hi => absurd hi (Finset.notMem_empty i))
          (fun i hi => absurd hi (Finset.notMem_empty i)) hh
          (fun i hi => absurd hi (Finset.notMem_empty i)) st rfl rfl hwidth ∅
          (Finset.Subset.refl _) p X₁ X₂ hX₁ hX₂ (le_rpow_of_length_le hZ1 hl₁)
          (le_rpow_of_length_le hZ1 hl₂)
        rw [Finset.sum_empty, mul_zero, add_zero] at hz
        have hcard : (T \ ∅).card ≤ N := (Finset.card_le_univ _)
        have hsum : ∑ i ∈ T \ ∅, extend T w 0 i = ∑ i, w i := by
          rw [Finset.sdiff_empty, hsT]
        rw [hsum] at hlow
        refine hlow.trans ?_
        have hE0 := energy_nonneg st.character st.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : (∅ : Finset α) => primePool rayM H 2 (Z^(extend T w 0 i)))
          (fun (i : (∅ : Finset α)) I =>
            idealCoeff (relativeCharacter rayM H hH η₀ (extend T θ 1 i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(extend T w 0 i))
              (extend T σ (33/50) i) (extend T v 0 i) I)
          (fun i : (∅ : Finset α) => Z^(extend T w 0 i)) X₁ X₂
          st.radial.keep st.radial.profile st.radial.scale (fun z => st.radial.nonneg z)
        refine low_total_le hCL hCZ.le hZ1.le (by positivity) hcard hdg (p.control_nonneg SZ)
          hcZ hbase (by omega) (by linarith) ?_ hE0 hz
        change 2*ε₁*d*N + q*∑ i, w i + (M + ε/8 + ε/4) ≤ _
        have e2 : q*∑ i, w i = q*need := by rw [hneedS]
        linarith
      · -- paid partial deletion into the parent face
        replace hfall := not_lt.mp hfall
        have hneeds : need ≤ ∑ i, w i := deletionNeed_le_self hs0
        obtain ⟨F, hFT, hlo, hhi⟩ := greedy_deletion T (extend T w 0) (max 0 mesh) need
          (le_max_left _ _) hneed0 (fun i _ => hw' i) (fun i _ => hwm' i)
          (by rw [hsT]; exact hneeds)
        have hsplitT : ∑ i ∈ F, extend T w 0 i + ∑ i ∈ T \ F, extend T w 0 i = ∑ i, w i :=
          (sum_retained_add_deleted T F hFT (extend T w 0)).trans hsT
        have hF0 : 0 ≤ ∑ i ∈ F, extend T w 0 i := Finset.sum_nonneg (fun i _ => hw' i)
        have hface' := retained_in_face (del := ∑ i ∈ T \ F, extend T w 0 i) hL0
          hc0 hM0 hfall hlo (by linarith)
        have hsF : ∑ i : F, extend T w 0 i = ∑ i ∈ F, extend T w 0 i :=
          Finset.sum_coe_sort F (extend T w 0)
        have hadm : (QRH.Record1252270103Source.globalFace B₀ L₀ c₀).Admissible
            (length Z X₁) (length Z X₂) (∑ i : F, extend T w 0 i) M := by
          rw [QRH.Record1252270103Source.globalFace_admissible_iff (length_nonneg Z X₁ hZ1)
            (length_nonneg Z X₂ hZ1) (by rw [hsF]; exact hF0) hL0.le, hsF]
          have e : ∑ i ∈ F, extend T w 0 i = (∑ i, w i) - ∑ i ∈ T \ F, extend T w 0 i := by
            linarith
          rw [e]
          exact hface'
        have hlow := hZL.2 q (by linarith) (by linarith) st rfl hwidth hQM hQη h
          (extend T θ 1) (extend T w 0) (extend T σ (33/50)) (extend T v 0) t T F hFT
          (fun i _ => hw' i) (fun i _ => hwr' i) (fun i _ => hσ₁' i) (fun i _ => hσ₂' i)
          (fun i _ => hwinL i) hgate2 (p.profile 0) (p.profile 1) X₁ X₂ (mul_pos hX₁ hX₂).le
        simp only [extend_coe, hT0] at hlow
        have hp := hZP j F (fun i : F => extend T θ 1 i) (fun i : F => extend T w 0 i)
          (fun i : F => extend T σ (33/50) i) (fun i : F => extend T v 0 i) t height
          (fun i => hw' i) (fun i => hwm' i) (fun i => hσ₁' i) (fun i => hσ₂' i) hh
          (fun i => hv' i) M hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
        rw [← hUM] at hp
        have hcard : (T \ F).card ≤ N := Finset.card_le_univ _
        have hE0 := energy_nonneg st.character st.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : F => primePool rayM H 2 (Z^(extend T w 0 i)))
          (fun (i : F) I =>
            idealCoeff (relativeCharacter rayM H hH η₀ (extend T θ 1 i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(extend T w 0 i))
              (extend T σ (33/50) i) (extend T v 0 i) I)
          (fun i : F => Z^(extend T w 0 i)) X₁ X₂
          st.radial.keep st.radial.profile st.radial.scale (fun z => st.radial.nonneg z)
        refine hlow.trans (low_total_le hCL hCP.le hZ1.le (by positivity) hcard hdg
          (p.control_nonneg SP) hcP hbase (by omega) (by linarith) ?_ hE0 hp)
        have e2 : q*∑ i ∈ T \ F, extend T w 0 i ≤ q*need + q*max 0 mesh := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left hhi (by linarith)
        have e3 : q*max 0 mesh ≤ ε/8 := by
          have : q*max 0 mesh ≤ 1*max 0 mesh :=
            mul_le_mul_of_nonneg_right (by linarith) (le_max_left _ _)
          linarith
        linarith
    -- assembly
    have hY0 : 0 ≤ QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^(degN + k + degP + degZ)*
        Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε) := by
      have := p.control_nonneg S
      have := Real.rpow_nonneg hZ0.le (M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε)
      positivity
    refine hpack.trans (hsplit.trans_le ?_)
    calc _ ≤ ((max 1 CL)^N*(CP + CZ))*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ)*
          Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε) +
        KH*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
          (1+|t|+height)^(degN + k + degP + degZ)*
          Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε) := add_le_add hlowB hhighB
      _ = ((max 1 CL)^N*(CP + CZ) + KH)*(QuadraticInitialBound.diagonalControl Φ*
          (p.control S)^2*(1+|t|+height)^(degN + k + degP + degZ)*
          Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε)) := by ring
      _ ≤ (CN + (max 1 CL)^N*(CP + CZ) + KH)*(QuadraticInitialBound.diagonalControl Φ*
          (p.control S)^2*(1+|t|+height)^(degN + k + degP + degZ)*
          Z^(M + max (q*need) (highSupM B₀ L₀ c₀ q Pl (∑ i, w i) M) + ε)) :=
          mul_le_mul_of_nonneg_right (by linarith) hY0
      _ = _ := by ring

end
end QRH.ArviDensity.Density
