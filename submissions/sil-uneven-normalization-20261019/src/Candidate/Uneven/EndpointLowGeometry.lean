/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/
import Candidate.Uneven.EndpointProbeGeometry
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace UnevenEndpointPhysical.Assembly
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open UnevenEndpointPhysical.Arithmetic
theorem marked_tuple_margin :
    1+3*ell-2*(x+y) < 0 := by
  rcases config with ⟨stage⟩
  cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell,x,y]
theorem marked_short_margin :
    y-2*x+ell < 0 := by
  rcases config with ⟨stage⟩
  cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell,x,y]
theorem marked_subset_decreases {v:ℝ} (hv:0≤ v) :
    -v+max 0 (1+3*ell-2*(x+y)+v)/8 ≤ 0 := by
  have hn : 1+3*ell-2*(x+y)<0 := marked_tuple_margin
  have hm : max 0 (1+3*ell-2*(x+y)+v)≤8*v := max_le (by linarith) (by linarith)
  linarith
end
end UnevenEndpointPhysical.Assembly
/-! Exact low-probe geometry. All lengths refer to Cycle63, including the total ray length. -/
namespace UnevenEndpointPhysical.Assembly.LowGeometry
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open UnevenEndpointPhysical.Arithmetic

theorem x_pos : 0 < x := by linarith [ell_pos, ell_lt_x]
theorem b_pos : 0 < y-x := by linarith [x_lt_y]
theorem signal_pos : 0 < signal theta := by
  rw [signal_at_boundary]
  linarith [x_pos, b_pos]
theorem scale_square : (2*x-y)+y=2*x := by ring
theorem gram_power (δ : ℝ) :
    x+(y-x)*(1/6)+y*δ = 2*signal theta+y*δ := by
  rw [signal_at_boundary]
  ring
theorem gram_sqrt_power (δ : ℝ) :
    (2*signal theta+y*δ)*(1/2) = signal theta+(y/2)*δ := by ring
theorem dilation_gap : 0 < 2*x-y-ell := by
  linarith only [marked_short_margin]
theorem dilation_le_y : 2*x-y ≤ y := by linarith [x_lt_y]
theorem tuple_margin_neg : 1+3*ell-2*(x+y) < 0 := by
  exact marked_tuple_margin
end
end UnevenEndpointPhysical.Assembly.LowGeometry

#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.x_pos
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.b_pos
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.signal_pos
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.scale_square
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.gram_power
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.gram_sqrt_power
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.dilation_gap
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.dilation_le_y
#print axioms UnevenEndpointPhysical.Assembly.LowGeometry.tuple_margin_neg
