/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.RoundedActualCountBounds
import Candidate.Uneven.MainCountMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Sil.Uneven.RoundedRows
noncomputable section
open OAI.SevenEighths

def oldCapacityAt (κ z : ℝ) : ℝ := min z (2*y-z)/(6*κ)

theorem scalar_capacity_antitone {z cap cap' count d p : ℝ}
    (hd : 0 ≤ d) (hp : 0 ≤ p) (hc : cap ≤ cap') :
    scalarRow z cap' count d p ≤ scalarRow z cap count d p := by
  have hh := mul_le_mul_of_nonneg_left hc (mul_nonneg hd hp)
  unfold scalarRow
  linarith only [hh]

theorem old_row_at_incumbent {κ z d p : ℝ} (hk : 7/10 ≤ κ) (hkhi : κ ≤ frozen_kappa)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacityAt κ z) (MainCount.count .final κ d p) d p ≤ theta-1/20000000000000 := by
  have hz0 : 0 ≤ z := (show (0:ℝ) ≤ rowHeight 0 by norm_num [rowHeight]).trans hz.1
  have htop : rowHeight 1 ≤ 2*y := by norm_num [rowHeight,y]
  have hm : 0 ≤ min z (2*y-z) := le_min hz0 (by linarith only [hz.2,htop])
  have hcap : oldCapacity z ≤ oldCapacityAt κ z := by
    exact div_le_div_of_nonneg_left hm (by linarith : 0 < 6*κ)
      (by linarith : 6*κ ≤ 6*frozen_kappa)
  have hc := MainCount.count_mono .final hk hkhi
    (show 0 ≤ d ∧ d ≤ 5/6 from ⟨hd.1,by linarith [hd.2]⟩) hp
  calc
    _ ≤ scalarRow z (oldCapacity z) (MainCount.count .final κ d p) d p :=
      scalar_capacity_antitone hd.1 hp.1 hcap
    _ ≤ scalarRow z (oldCapacity z) (MainCount.count .final frozen_kappa d p) d p :=
      scalar_row_mono hz0 hc
    _ ≤ _ := actual_old_row_interval hd hp hz

theorem new_row_at_incumbent {κ z d p : ℝ} (hk : 7/10 ≤ κ) (hkhi : κ ≤ frozen_kappa)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .final κ d p) d p ≤ theta-1/20000000000000 := by
  have hz0 : 0 ≤ z := (show (0:ℝ) ≤ rowHeight 2 by norm_num [rowHeight]).trans hz.1
  have hc := MainCount.count_mono .final hk hkhi
    (show 0 ≤ d ∧ d ≤ 5/6 from ⟨hd.1,by linarith [hd.2]⟩) hp
  exact (scalar_row_mono hz0 hc).trans (actual_new_row_interval hd hp hz)

theorem old_supremum_deficit {beta z d p : ℝ} (hb : theta < beta)
    (hbhi : beta ≤ (frozen_kappa+1)/2)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 0 ≤ z ∧ z ≤ rowHeight 1) :
    scalarRow z (oldCapacityAt (2*beta-1) z) (MainCount.count .final (2*beta-1) d p) d p-beta ≤
      -(1/20000000000000)-(beta-theta) := by
  have hk : 7/10 ≤ 2*beta-1 := by norm_num [theta] at hb; linarith only [hb]
  have hkhi : 2*beta-1 ≤ frozen_kappa := by linarith only [hbhi]
  have hh := old_row_at_incumbent hk hkhi hd hp hz
  linarith only [hh]

theorem new_supremum_deficit {beta z d p : ℝ} (hb : theta < beta)
    (hbhi : beta ≤ (frozen_kappa+1)/2)
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2)
    (hz : rowHeight 2 ≤ z ∧ z ≤ rowHeight 3) :
    scalarRow z (newCapacity z) (MainCount.count .final (2*beta-1) d p) d p-beta ≤
      -(1/20000000000000)-(beta-theta) := by
  have hk : 7/10 ≤ 2*beta-1 := by norm_num [theta] at hb; linarith only [hb]
  have hkhi : 2*beta-1 ≤ frozen_kappa := by linarith only [hbhi]
  have hh := new_row_at_incumbent hk hkhi hd hp hz
  linarith only [hh]

end
end Sil.Uneven.RoundedRows
#print axioms Sil.Uneven.RoundedRows.old_supremum_deficit
#print axioms Sil.Uneven.RoundedRows.new_supremum_deficit
