/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCountConcrete
import Candidate.Uneven.MainCountIdentity
import Candidate.Uneven.RoundedRowIntervals

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Sil.Uneven.RoundedRows
noncomputable section
open OAI.SevenEighths

theorem affine_numeric_identity {i : ℕ} (hi : i ≤ 7) {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    Target830.Count.affineR (planeLambda i) (planeB i) d p =
      numerator i d p/denominator i d p := by
  have hJ := (denominator_pos hi hd hp).ne'
  apply (eq_div_iff hJ).mpr
  have hJ' : Target830.Count.affineJ (planeLambda i) d p ≠ 0 := hJ
  convert Target830.Count.affine_count_mul (B:=planeB i) hJ' using 1 <;>
    dsimp [numerator,denominator,Target830.Count.affineN,Target830.Count.affineJ,
      Target830.Count.affineD,Target830.Count.affineA,Target830.Count.affineU,
      Target830.Count.affineC] <;> ring

/-- The actual finite count selector satisfies every bound used by the numerical
row certificates. No analytic source estimate is assumed in this algebraic bridge. -/
theorem actual_count_bounds {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    CountBounds (MainCount.count .final frozen_kappa d p) d p := by
  intro i hi ha
  rw [←affine_numeric_identity hi hd hp]
  rcases ha with hz | h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  · subst i
    have hc := MainCount.count_le_old .final frozen_kappa d p
    rw [MainCount.old_count_affine (by norm_num [frozen_kappa]) hd hp] at hc
    convert hc using 1 <;> norm_num [planeLambda,planeB,frozen_kappa]
  · rcases h0 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window0.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window0 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window0,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h1 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window1.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window1 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window1,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h2 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window2.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window2 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window2,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h3 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window3.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window3 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window3,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h4 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window4.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window4 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window4,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h5 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window5.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window5 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window5,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h6 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window6.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window6 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window6,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h7 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window7.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window7 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window7,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h8 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window8.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window8 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window8,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h9 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : Target830.Count.window9.Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := (MainCount.count_le_previous .final frozen_kappa d p).trans
      (Target830.Count.count_le_window9 hw)
    convert hc using 1 <;> norm_num [planeLambda,planeB,Target830.Count.window9,
      Target830.Count.Plane.lambda,Target830.Count.Plane.B,
      Target830.SourcePlane.lambda,Target830.SourcePlane.B]
  · rcases h10 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window10 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window10 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window10,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h11 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window11 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window11 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window11,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h12 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window12 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window12 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window12,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h13 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window13 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window13 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window13,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]
  · rcases h14 with ⟨rfl,hd0,hd1,hp0,hp1⟩
    have hw : (MainCount.window14 .final).Available d p := ⟨⟨hd0,hd1⟩,hp0,hp1⟩
    have hc := MainCount.count_le_window14 .final (κ:=frozen_kappa) hw
    convert hc using 1 <;> norm_num [planeLambda,planeB,MainCount.window14,
      MainCount.Stage.aPlane,MainCount.Stage.cPlane,
      MainCount.Plane.lambda,MainCount.Plane.B]

theorem actual_old_row_interval {z d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacity z) (MainCount.count .final frozen_kappa d p) d p ≤
      theta-1/20000000000000 :=
  old_row_interval hd hp hz (actual_count_bounds hd hp)

theorem actual_new_row_interval {z d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .final frozen_kappa d p) d p ≤
      theta-1/20000000000000 :=
  new_row_interval hd hp hz (actual_count_bounds hd hp)

end
end Sil.Uneven.RoundedRows
#print axioms Sil.Uneven.RoundedRows.actual_count_bounds
#print axioms Sil.Uneven.RoundedRows.actual_old_row_interval
#print axioms Sil.Uneven.RoundedRows.actual_new_row_interval
