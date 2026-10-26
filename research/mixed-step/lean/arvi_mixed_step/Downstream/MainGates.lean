/- Mixed step (L4/L5, F6): the node facts of the MAIN twins, from the ledger (new in this submission).

The F6 twins (ForkMx `Core/InitialRegularToTruncatedMainExceptional(Saving)`,
`Low/InitialRemainderScalarSumNode`, `Core/InitialRegularToTruncatedRemainderOne`) take their node
facts as plain hypotheses, collected in `MainTwinFacts K n low b a Amix F κ`:
* `centered` — the mixed centered gate `T + 9·Amix + fee < 5/6 + 0.499·Lref` (complement, `+3δ`);
* `room`, `F_nonneg`, `F_amp`, `lowB_le` — the first-layer budget at the mixed scale `F`
  (`T + 4e < B₀·F`, `0 ≤ F`, `F + 6·Amix ≤ 1`, `B₀ ≤ 1`), which gives the remainder volume gap
  `A₀ + 6·Amix + 3e ≤ 1` (zero term, `+4δ`);
* `a_pos`, `a_le` — the pool amplitude `0 < a ≤ Amix`;
* `kappa_nonneg`, `kappa_le`, `kappa_room` — the shift loss `0 ≤ κ ≤ Amix - a`,
  `e + 2κ ≤ 2·Amix - a`.
`mainTwinFacts_of_mixedGeometry` derives all of them from the ledger bundle `MixedGeometry` at the
actual width `b` (`a = r`, `Amix = r + d`, `F = F' = 1 - 6r - 6d`) for every `0 ≤ κ ≤ 6e`, the
range the ledger's grid gives (`κ = 2·mesh`, `mesh ≤ κ_ledger/2 ≤ 3e`). The only extra input is
`d ≥ r` (`mixed_d_ge_fee`), which follows from `SourceValid3X` (`6qβ > 1`) past the crossing.
The MAIN-twin gate `zero_twin` (`T + 5·Amix + fee < 1`) is not used: Collet's zero term is paid by
the parent budget, not by `first_tail`, and so is the mixed one. -/
import Submissions.arvi_mixed_step.Ledger.Geometry

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Downstream
noncomputable section
open Record1252270103Finite QRH.MixedStep.Finite QRH.MixedStep.Ledger QRH.Record1252270103Graph

/-- The node facts consumed by the F6 MAIN twins. -/
structure MainTwinFacts (K : ℚ) (n low : Source) (b a Amix F κ : ℝ) : Prop where
  centered : sourceTReal n b+b+9*Amix+(n.highFee:ℝ)<5/6+(499/1000)*(49/100-(K:ℝ)*b)
  room : sourceTReal n b+b+4*(n.allowance:ℝ)<(low.B:ℝ)*F
  F_nonneg : 0≤F
  F_amp : F+6*Amix≤1
  lowB_le : (low.B:ℝ)≤1
  a_pos : 0<a
  a_le : a≤Amix
  kappa_nonneg : 0≤κ
  kappa_le : κ≤Amix-a
  kappa_room : (n.allowance:ℝ)+2*κ≤2*Amix-a

/-- Past the crossing the transferred width is at least the pool width: `r ≤ d`. -/
theorem mixed_d_ge_fee (n low h : Source) (hv : SourceValidC3 n low h) (hX : SourceValid3X n low)
    (hlow : ParentGood low) (he : 0 ≤ (n.allowance:ℝ)) {b : ℝ}
    (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    (n.lowFee:ℝ) ≤ sourceDReal n low b := by
  have S := shape3_of n low h hv
  have hg := (scalar3_full_width n low h hv hb).1
  have g0 := hg 0
  have g2 := hg 2
  simp only [scalarGate3Real] at g0 g2
  norm_num at g0 g2
  have hL0 : 0 < (low.L:ℝ) := by
    have := hlow.2.2.1; have h1 : (1:ℝ) < low.L := by exact_mod_cast this
    linarith
  have hq0 : 0 ≤ (n.q:ℝ) := by linarith [S.q_half]
  have hdiff : 0 < (low.L:ℝ) - n.L := by linarith [S.L_lt]
  have hcross : (crossing n low:ℝ) = ((low.B:ℝ) - n.B)/((low.L:ℝ) - n.L) := by
    simp [crossing]
  have hx : (low.B:ℝ) - n.B ≤ ((low.L:ℝ) - n.L)*b := by
    have := hb.1; rw [hcross, div_le_iff₀ hdiff] at this; linarith
  have hX0 : 0 ≤ b + (sourceTReal n b - low.B)/low.L := by
    have hnum : 0 ≤ (low.L:ℝ)*b + (sourceTReal n b - low.B) := by
      simp only [sourceTReal]
      have hLe : 0 ≤ (n.L:ℝ)*(n.allowance:ℝ) := mul_nonneg (by linarith [S.L_gt]) he
      nlinarith
    have : b + (sourceTReal n b - low.B)/low.L = ((low.L:ℝ)*b + (sourceTReal n b - low.B))/low.L := by
      field_simp
    rw [this]; exact div_nonneg hnum hL0.le
  have g0' : (0:ℝ) < sourceDen3 n low := by exact_mod_cast g0
  have g2' : (0:ℝ) < n.lowFee := by exact_mod_cast g2
  -- `6 q β > 1` from `SourceValid3X`
  have hX' : (0:ℝ) < 6*(n.q:ℝ)*(low.B:ℝ) - low.L := by
    have := hX; unfold SourceValid3X at this; exact_mod_cast this
  have hβ : 1 < 6*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ)) := by
    rw [show 6*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ)) = (6*(n.q:ℝ)*(low.B:ℝ))/low.L by ring,
      lt_div_iff₀ hL0]
    linarith
  have hden3 : (sourceDen3 n low:ℝ) = 1 + n.q - 6*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ)) := by
    simp only [sourceDen3]; push_cast; ring
  simp only [sourceDReal]
  rw [le_div_iff₀ g0', hden3]
  have hq1 : (n.q:ℝ) < 1 := by linarith [S.q_lt]
  have hqX := mul_nonneg hq0 hX0
  have hr12 : (n.lowFee:ℝ)*(1 + n.q) ≤ (n.lowFee:ℝ)*(12*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) g2'.le
  nlinarith

/-- **The MAIN-twin node facts from the ledger bundle**, at the actual width `b`, with `a = r`,
`Amix = r + d`, `F = 1 - 6r - 6d`, for every shift loss `0 ≤ κ ≤ 6e`. -/
theorem mainTwinFacts_of_mixedGeometry {Kgraph : ℚ} {n low h : Source} {b : ℚ} {reserve : ℝ}
    (hg : MixedGeometry Kgraph n low h b reserve) (hv : SourceValidC3 n low h)
    (hX : SourceValid3X n low) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 6*(n.allowance:ℝ)) :
    MainTwinFacts Kgraph n low (b:ℝ) (n.lowFee:ℝ) (sourceAmp3Real n low (b:ℝ))
      (sourceF3Real n low (b:ℝ)) κ := by
  have hd := mixed_d_ge_fee n low h hv hX hg.low_parent hg.allowance_pos.le hg.width_mem
  have hfee := hg.fee_allowance
  have he := hg.allowance_pos
  have hsmall := hg.amp_small
  have hB : (low.B:ℝ) ≤ 1 := by exact_mod_cast hg.low_parent.2.1
  have hA : sourceAmp3Real n low (b:ℝ) = (n.lowFee:ℝ) + sourceDReal n low (b:ℝ) := rfl
  have hF : sourceF3Real n low (b:ℝ) = 1 - 6*sourceAmp3Real n low (b:ℝ) := by
    simp only [sourceF3Real, sourceAmp3Real]; ring
  refine ⟨hg.centered_twin, hg.parent_budget_room, ?_, ?_, hB, hg.fee_pos, ?_, hκ0, ?_, ?_⟩
  · rw [hF]; linarith
  · rw [hF]; linarith
  · rw [hA]; linarith
  · rw [hA]; linarith
  · rw [hA]; linarith

end
end QRH.MixedStep.Downstream
#print axioms QRH.MixedStep.Downstream.mixed_d_ge_fee
#print axioms QRH.MixedStep.Downstream.mainTwinFacts_of_mixedGeometry
