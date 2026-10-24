"""Semantic edits of the forked generic physical return (Lemma D), applied by fork_physical.py.

* Schedule: the numerator cap is SP; the window guards of the physical schedule (plain window,
  width window, free shift, small-plain shortening at plain length 2/5, shift bound, large-shift
  reserve) are replaced by the single small-plain bound of the global face at plain length 0.
* Geometry: replaced by lemmaD/Geometry.lean (the face at every shift).
* Input / Fourier: the physical face is the global face restricted to plain lengths in [0,1/2]
  and slot widths in [0,SP].
* Hybrid: the admitted configuration needs no window; a nonpositive plain length is paid by the
  natural moment.
* everywhere: the shift of an admitted configuration is no longer bounded by the free shift.
"""

GLOBAL = [(' t≤ freeShift ∧', ''), (" t'≤ freeShift ∧", '')]

HAND = {'PhysicalDirect.Geometry': 'lemmaD/Geometry.lean'}


def patches(sp):
    return {
        'Schedule': [
            ('def cap:ℝ := 1/25', f'def cap:ℝ := {sp}'),
            (''' physical_plain_lower:plainLower<1-y/dMinus
 physical_plain_upper:1-y/dp+freeShift<264/625
 physical_width_lower:17/500<(physicalB-2*(1-y/dp+freeShift))/physicalLambda
 small_plain_shortening:0≤1-plainLower-physicalB/2-(9/2-physicalLambda/2)*cap
 prime_supply:1/5<ell/dp
 shift_bound:2*y/dMinus-1≤9/50
 large_shift_reserve:0≤(7/18-1/500)*freeShift+(1-physicalB)/18+(physicalLambda/18-1/4)*cap
''',
             ''' small_plain_global:0≤1-physicalB/2-(9/2-physicalLambda/2)*cap
 prime_supply:1/5<ell/dp
'''),
        ],
        'PhysicalDirect.Input': [
            ('⟨GenericArithmetic.physicalB,GenericArithmetic.physicalLambda,2/5,11/25,17/500,1/25⟩',
             '⟨GenericArithmetic.physicalB,GenericArithmetic.physicalLambda,0,1/2,0,GenericArithmetic.cap⟩'),
            ('''    (hlo₁ : 2/5≤ length U X₁) (hhi₁ : length U X₁≤44/100)
    (hlo₂ : 2/5≤ length U X₂) (hhi₂ : length U X₂≤44/100)
    (hslotlo : 17/500≤∑i,width i) (hslothi : (∑i,width i)≤1/25)''',
             '''    (hlo₁ : 0≤ length U X₁) (hhi₁ : length U X₁≤1/2)
    (hlo₂ : 0≤ length U X₂) (hhi₂ : length U X₂≤1/2)
    (hslotlo : 0≤∑i,width i) (hslothi : (∑i,width i)≤GenericArithmetic.cap)'''),
        ],
        'PhysicalDirect.Fourier': [
            ('''      2/5≤ length U X₁ → length U X₁≤44/100 →
      2/5≤ length U X₂ → length U X₂≤44/100 →
      17/500≤∑i,width i → (∑i,width i)≤1/25 →''',
             '''      0≤ length U X₁ → length U X₁≤1/2 →
      0≤ length U X₂ → length U X₂≤1/2 →
      0≤∑i,width i → (∑i,width i)≤cap →'''),
        ],
        'PhysicalDirect.Hybrid': [
            ('''  rcases hcap with ⟨d,t,hd0,hd1,ht0,ht1,heq,hslots⟩ | hold
  · have hnhi:= (plainScale_interior ⟨hd0,hd1⟩ ⟨ht0,ht1⟩).2
    have hslotshi:= (clippedCapacity_interior ⟨hd0,hd1⟩ ⟨ht0,ht1⟩).2
    rw [←heq] at hnhi
    have hx1hi:length U X₁≤264/625:=hx₁.trans hnhi.le
    have hx2hi:length U X₂≤264/625:=hx₂.trans hnhi.le
    have hs40:(∑i,width i)≤widthUpper:=by
      have hh:=hslots.trans hslotshi
      have hclip : cap≤widthUpper := by norm_num [cap,widthUpper]
      exact hh.trans hclip
    have hslotsAffine := hslots.trans (min_le_right cap (affineCapacity d t))
    have hparentcone : 2*n+physicalLambda*(∑i,width i)≤physicalB := by
      have hh:=affine_shortening (le_refl (plainScale d t)) (le_refl (plainScale d t)) hslotsAffine
      simpa only [heq, two_mul] using hh
    by_cases hslo:widthLower≤∑i,width i
    · by_cases h1:plainLower≤ length U X₁
      · by_cases h2:plainLower≤ length U X₂
        · have hbound:=ha.2 rows hrows T width z height hw hmesh hzre hh him X₁ X₂ hX₁ hX₂
            (by simpa [plainLower] using h1) (by linarith) (by simpa [plainLower] using h2) (by linarith) (by simpa [widthLower] using hslo) (by simpa [widthUpper] using hs40)
            (affine_shortening (heq ▸ hx₁) (heq ▸ hx₂) hslotsAffine) j k v w
          apply hbound.trans
          gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]''',
             '''  rcases hcap with ⟨d,t,hd0,hd1,ht0,heq,hslots⟩ | hold
  · have hs40:(∑i,width i)≤cap:=hslots.trans (min_le_left _ _)
    have hslotsAffine := hslots.trans (min_le_right cap (affineCapacity d t))
    have hparentcone : 2*n+physicalLambda*(∑i,width i)≤physicalB := by
      have hh:=affine_shortening (le_refl (plainScale d t)) (le_refl (plainScale d t)) hslotsAffine
      simpa only [heq, two_mul] using hh
    have hΛ := physicalLambda_pos
    have hB1 : physicalB≤1 := PhysicalSchedule.B_bounds.2
    have hnhalf : n≤1/2 := by nlinarith [mul_nonneg hΛ.le hsum]
    · by_cases h1:0≤ length U X₁
      · by_cases h2:0≤ length U X₂
        · have hbound:=ha.2 rows hrows T width z height hw hmesh hzre hh him X₁ X₂ hX₁ hX₂
            h1 (by linarith) h2 (by linarith) hsum hs40
            (affine_shortening (heq ▸ hx₁) (heq ▸ hx₂) hslotsAffine) j k v w
          apply hbound.trans
          gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]'''),
            ('''          (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (by nlinarith only [hc,hk1,hsum]) j k v w
        apply hb'.trans
        gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · have hc:=small_slot_shortening hx1hi hx2hi (le_of_not_ge hslo)
      have hb':=hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
        (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
        (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
        (by nlinarith only [hc,hk1,hsum]) j k v w
      apply hb'.trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
''',
             '''          (hX₁max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (hX₂max.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n≤1)))
          (by nlinarith only [hc,hk1,hsum]) j k v w
        apply hb'.trans
        gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
'''),
        ],
    }
