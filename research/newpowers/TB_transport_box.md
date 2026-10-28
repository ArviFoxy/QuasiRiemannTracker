# Transport box `BoundsN`: who depends on it, what widening it costs

Date 2026-10-28. Read-only study: no `lake`/`lean`, nothing committed or pushed. Scripts, exact-rational numerics and raw
outputs are in `research/newpowers/tb/` (section 7). Paths: `P83/` = `/home/user/lean-env/qrh/Submissions/sil_density_split_20261026/`,
`P86/` = `.../density_split_fine_chain/`, `P76/` = `.../arvi_repeated_marks_on_sil_face_20261025/`, `COL/` = `.../hailey_collet_1252270103/Record1252270103Return/`.
Tags: **[L]** read in Lean (path:line), **[D]** my derivation, **[N]** exact numerics (Fractions) from `tb/`, **[I]** inference not checked by a compiler.

## 0. Bottom line

1. **Widening `ell < 171/1000` is a 3-line numeral edit [L][N]**: `P83/ReturnD/TransportGeometry.lean:23` (field), `:60` (`four_ell_lt_h`), `:95`
   (alias `ell_interval`). The upper end of `ell` has exactly one real consumer, `four_ell_lt_h` (`4*ell < h`), which holds up to
   `ell < 0.19825`; the other three uses only need `ell ≤ 1` or `x ≤ 1`. Nothing in the transport layer is proved by a certificate, only by `linarith`/`nlinarith`
   from these numerals, and the two earlier widenings changed exactly these lines (section 1.3: PR 76 -> PR 83 differs in nothing else but the unrelated `cap` field).
2. **`ell = 11/3 - 4*theta` exactly** (`TransportGeometry.lean:39`). theta = 0.8739058 needs ell = 0.1710435; theta = 0.8738 needs ell = 0.1714667.
   `ell < 175/1000` is implied by `theta > 873/1000` (ell < 0.17467), so with it the `ell` upper end is redundant and the box is cut only by the other fields.
3. **The real limits are the two functional fields and `y > 458/1000`, not the numerals.** With `fm = 1/200` and `ss = 7/100` unchanged, the (theta,h)
   polygon ends at theta = 0.873644 (ell<0.175) and the caller's example `theta > 0.8735` is not reachable. Reason: `floor_margin` is
   `h <= 1.205 - 2.34*ell - 2e-10 = 9.36*theta - 7.375` (h-coefficient of its left side cancels), while `small_saving` needs `h > 0.2755 + 3.0612*ell` and `y > 0.458` needs `h > 0.458 + 2*ell`.
4. **The models' h is the floor ceiling, not 0.806**: `h(theta) = 9.36 theta - 7.375` = 0.804758 at theta = 0.8739058, 0.803767 at 0.8738
   (`tc/best.py h_for`, `r3/pm.py pick_h`). So `h < 806/1000` needs no change; h falls 9.4e-4 per 1e-4 of theta, which costs only +3e-7 (theta 0.8739058) to +1.3e-6 (0.8738) in theta* on PR 86's faces
   (`hscan_both.log`: dtheta*/dh = -1.07e-3).
5. **No statement fails** in any of the widened boxes (ell<0.1715, ell<0.175, `theta>0.8735`, and a "future-proof" box below). Smallest margins:
   `E4` 7e-5 (`h/600 >= 1/800`, needs h_lo >= 0.75), `D2/D3` 8e-3 (`y <= 19/40`), `E5a` 8e-3 (theta >= 0.871667), `B1` 7.8e-3 (`(5x+y)/12 > 1/10`).
6. **The sharpest use of the theta lower end** is `PrincipalRemainderRegion.lean:39-40` (`4 - 6 theta - 24/25 <= -219/100`, needs theta >= 0.871667), then `:45-46` (theta >= 0.87). Everything else needs theta <= 0.85.
   Lowering `theta_lo` below 0.8717 would be a real proof edit (two exponent constants), but it is not needed for any target >= 0.8731.
7. **A new PR must fork `ReturnD/`** (119 modules, 15,080 lines): PR 86's `Return/` imports `Submissions.sil_density_split_20261026.ReturnD.*` (e.g. `P86/Return/FinalSchedule.lean:5`), so the class cannot be patched in place.
   Mechanical rename + 3-7 numeral lines; rebuild of ReturnD+Return about 15-20 min wall (precedent: 161 modules in 923 s with 2 processes, `research/mixed-step/return_cut/REGENERATE.md` section 6).
8. **Not covered by "numerals only"**: changing the floor budget `1/200` (threaded through 12 statements in 9 files), and the column-excess lever `x+y = 1-ell+e` of `r3/pm.py` (changes the identities at `TransportGeometry.lean:39-44, 69-78` and Collet's `Parameters.x_add_y`).

---------------------------------------------------------------------------------------------------------------------

## 1. The box

### 1.1 Definition, instance, proof method [L]

`class BoundsN : Prop` (`P83/ReturnD/TransportGeometry.lean:19-26`) has six fields, all on the five scalars (theta, h, y, ell) of Collet's `Geometry.Parameters` (`h := 1+ell-x`, `dPlus := h+1e-10`):

| field | line | statement |
|---|---|---|
| `theta_bounds` | 20 | `873/1000 < theta ∧ theta < 7/8` |
| `h_interval` | 21 | `793/1000 < h ∧ h < 806/1000` |
| `ly_coarse` | 22 | `458/1000 < y ∧ y < 467/1000` |
| `ell_interval` | 23 | `1672/10000 < ell ∧ ell < 171/1000` |
| `small_saving` | 24 | `7/100 < y/2 - h*(17/50-1/6) - 1/50` |
| `floor_margin` | 25 | `4/25 x - 3/20 - 51/100 y + 67/100 dPlus - 3/20 ell <= signal theta - 1/200` |

The class is a hypothesis of ~119 lemmas (`variable [Parameters] [BoundsN]`); the *only* inhabitant is `finalBounds`
(`P83/Return/TransportInstances.lean:9-12`, identical in `P86/Return/TransportInstances.lean:9-12`), proved by
`refine @BoundsN.mk finalParameters ?_ ?_ ?_ ?_ ?_ ?_ <;> dsimp +instances only [...] <;> norm_num`, i.e. six `norm_num` goals on the rational constants of `Return/Constants.lean`.
It is installed as `local instance` in `Return/EndpointFromNumerator.lean:14`, `EndpointFromSources.lean:17`, `FinalRows.lean:15`, `FinalSchedule.lean:15`.
Everything else in `Return/` (conductor edges, count windows, the Bernstein rows) never mentions the box.

### 1.2 The box is a polygon in the (theta,h) plane [D][L]

`TransportGeometry.lean:39-45`: `ell = 11/3 - 4 theta`, `x = 1 + ell - h`, `y = h - 2 ell`, `dPlus = h + 1e-10`. (Derivation: `signal_boundary` + `x+y = 1-ell` give
`theta = 2/3 + (x+y)/4 = 11/12 - ell/4`.) So a box is a polygon in (theta,h) and `ell_hi` is a *lower bound on theta*: `ell < 171/1000  <=>  theta > 0.8739167`
(the "bar raised to 5e-5" note in `LOG.md`). `signal theta = x/2 + (y-x)/12 = (5 + 3 ell - 4 h)/12`.
Vertices of the current polygon (`tb_results_polygons.txt`): theta_min = 0.8739167 at h in [0.800000, 0.804860]; PR 86's point (0.8739558, 0.8051) has slack
`ell<hi` 1.57e-4, `floor_margin` 4.2e-5 (= 1.3e-4 in h), `h<hi` 9.0e-4, `theta>lo` 9.6e-4, `small_saving` 2.2e-3, `y>lo` 5.4e-3, `y<hi` 3.6e-3.

### 1.3 Precedent: two compiled widenings were numeral-only [L]

I normalised namespaces and diffed (scratch `tbwork/`, `diff -r`): all differences between PR 76's and PR 83's `ReturnD/` (119 modules each) other than headers/`set_option` are:

* `TransportGeometry.lean`: fields `theta_bounds` 874->873, `h_interval` 803->806, `ell_interval` 1690/10000->171/1000; `four_ell_lt_h`'s `have he : ell<…`; aliases `ell_interval`, `theta_lower`, `theta_bounds`, `h_interval` (8 code lines plus the docstring);
* `Transport/FinalFixedHigh.lean:72,115`: `h<803/1000` -> `h<806/1000`;
* (unrelated) `Schedule.lean`/`PhysicalDirect/Geometry.lean`: the physical cap `9/200` becomes the schedule field `cap`.

The numerals of the Collet -> PR 76 widening sit on the same lines of the same two files (`h<802->803`, `y<466->467`, `ell<1677/10000->1690/10000`), and the mixed-step build 3 (`h<807/1000`, `ell<1710/10000`, generated by `research/repeated-marks/fork_transport.py` with `QRH_RELAXED`) rebuilt all 119 modules ALL-OK
(`research/mixed-step/return_cut/REGENERATE.md` section 6). Each record's `ell_hi` followed `4*Δtheta`: 1677 -> 1690 -> 1710/10000 (PR 83, also mixed-step b) -> now >= 1711/10000.

---------------------------------------------------------------------------------------------------------------------

## 2. Inventory of box consumers (question 1)

`tb/sites.txt` lists all 229 textual uses (`tb_sites.py`): 35 in `TransportGeometry.lean` itself, 194 on 157 distinct lines of 39 other `ReturnD/` files
(136 `theta_bounds`, 22 `ly_coarse`, 21 `h_interval`, 7 `ell_interval`, 1 each `small_saving`, `theta_lower`, `floor_margin`, plus derived lemmas). `Return/` has none besides section 1.1.

**How they are proved.** (a) the six fields once, by `norm_num` at the instance; (b) every consumer by `linarith` over the field hypotheses (the fields are passed as conjunctions, e.g. `linarith [BoundsN.theta_bounds]`),
with five `nlinarith` sites carrying box hints (`FloorExponent.lean:40`, `PrincipalRemainderBounds.lean:589,592`, `FullW.lean:39`, `CentralErrorSaving.lean:31`; hints at `:617,:621` are irrelevant to their goals);
(c) a few direct projections (`FinalFixedHigh.lean:66,67,72`, aliases in `TransportGeometry.lean`). **No interval or Bernstein certificate appears anywhere in the transport layer**; those live in `Return/EdgeCertificates.lean`, `Return/Rows/` and use the actual constants only.

Columns: *margin now* = slack of the needed inequality on the abstract box (the proof sees only the numerals), PR 83 numerals; *ℓ<.175* = same with `ell_hi = 175/1000`;
*future-proof* = `ell_hi = 175/1000, y_lo = 440/1000, ss = 6/100`; *limit* = value of that numeral at which the margin reaches 0, others fixed (table is generated by `tb_make_tables.py`).
`G1`, `G2` are the two functional fields as hypotheses of the instance (no inequality of their own to prove).

| id | where (`ReturnD/…`, PR 83) | inequality the proof needs | proof | margin now | ℓ<.175 | future-proof | limit of the numerals it uses |
|---|---|---|---|---|---|---|---|
| A1 | TransportGeometry.lean:58-62 (four_ell_lt_h) | 4*ell < h | linarith [h_interval.1, ell_interval.2] | 0.1090 | 0.0930 | 0.0930 | h_lo ≥ 0.6840; ℓ_hi ≤ 0.1983 |
| A2 | TransportGeometry.lean:54 (half_lt_h) | 1/2 < h | linarith [h_interval] | 0.2930 | 0.2930 | 0.2930 | h_lo ≥ 0.5000 |
| A3 | TransportGeometry.lean:55 (h_lt_two_y) | h < 2*y | linarith [h_interval, ly_coarse] | 0.1100 | 0.1100 | 0.0740 | h_hi ≤ 0.9160; y_lo ≥ 0.4030 |
| A4 | TransportGeometry.lean:64 (dPlus_lt_one), :97 (extended_h_lt_one) | h + 1e-10 < 1 | linarith [h_interval.2] | 0.1940 | 0.1940 | 0.1940 | h_hi ≤ 1.0000 |
| A5 | TransportGeometry.lean:80 (theta_gt_half) | 1/2 < theta | linarith [theta_bounds.1] | 0.3730 | 0.3730 | 0.3730 | θ_lo ≥ 0.5000 |
| A6 | TransportGeometry.lean:96 (h_pos) | 0 < h | linarith [h_interval.1] | 0.7930 | 0.7930 | 0.7930 | h_lo ≥ 0.0000 |
| B1 | Transport/FinalFixedHigh.lean:64-70 and :107-113 (hsig) | 1/10 < signal theta = (5x+y)/12 with x > ell_lo, y > y_lo | linarith [signal_at_boundary, ell_interval.1.trans ell_lt_x, ly_coarse.1] (numerals 1672/10000, 458/1000 hard-coded at :66,:67,:109,:110) | 0.0078 | 0.0078 | 0.0063 | ℓ_lo ≥ 0.1484; y_lo ≥ 0.3640 |
| B2 | Transport/FinalFixedHigh.lean:71-74 and :114-117 (hcap) | h + 5e-11 <= 7/8 - 1/100 | have hb : h<806/1000 (hard-coded numeral at :72,:115) ; linarith | 0.0590 | 0.0590 | 0.0590 | h_hi ≤ 0.8650 |
| C1 | GenericFeedback.lean:23 and :44 | 7/10 <= kappa = 2 theta - 1 | linarith [theta_bounds.1] | 0.0460 | 0.0460 | 0.0460 | θ_lo ≥ 0.8500 |
| C2 | GenericFeedback.lean:26 (hcoef) | 5*dp/288 <= 1/50 | linarith [h_interval.2] | 0.0060 | 0.0060 | 0.0060 | h_hi ≤ 1.1520 |
| D1 | PhysicalDirect/Geometry.lean:87 (shiftBase_nonneg) | dp < 2*y | linarith [h_interval.2, ly_coarse.1] | 0.1100 | 0.1100 | 0.0740 | h_hi ≤ 0.9160; y_lo ≥ 0.4030 |
| D2 | PhysicalDirect/SourceParameters.lean:51 (hy: y <= 19/40) | y <= 19/40 (then y/d <= 19/20 for d >= 1/2) | linarith [ly_coarse.1, ly_coarse.2] | 0.0080 | 0.0080 | 0.0080 | y_hi ≤ 0.4750 |
| D3 | PhysicalDirect/Active.lean:57 (eventually_new_cutoff_le_base) | y/d <= 19/20 for d > 1/2, i.e. y <= 19/40 | linarith [ly_coarse.2] | 0.0080 | 0.0080 | 0.0080 | y_hi ≤ 0.4750 |
| D4 | PhysicalDirect/OldGeometry.lean:66 (physical_y_range), OldActive.lean:45 | y/d <= 99 for d >= 1/200, i.e. y <= 99/200 | linarith [ly_coarse.2] | 0.0280 | 0.0280 | 0.0280 | y_hi ≤ 0.4950 |
| D5 | PhysicalDirect/OldGeometry.lean:155-160 (hyell) | y <= ell*(6*kappa), kappa >= 7/10: y <= 4.2*ell | linarith [ell_interval.1, ly_coarse.2] + one product | 0.2352 | 0.2352 | 0.2352 | y_hi ≤ 0.7022; ℓ_lo ≥ 0.1112 |
| D6 | PhysicalDirect/OldActive.lean:160 | 0 < y | linarith [ly_coarse.1, ly_coarse.2] | 0.4580 | 0.4580 | 0.4400 | y_lo ≥ 0.0000 |
| D7 | PhysicalDirect/Finite/Bridge.lean:39 (target_positive) | 1/10 < theta + signalShift = theta - 5/6 + x/3 + ell/6, x > ell > ell_lo | linarith [theta_bounds.1, ell_interval.1, ell_lt_x] | 0.0233 | 0.0233 | 0.0233 | θ_lo ≥ 0.8497; ℓ_lo ≥ 0.1207 |
| D8 | PhysicalDirect/Finite/Summation.lean:82, Finite/Geometry.lean:63, SourceLedger.lean:81 | dp <= 1 | linarith [h_interval.2] | 0.1940 | 0.1940 | 0.1940 | h_hi ≤ 1.0000 |
| D9 | PhysicalDirect/SourceActual.lean:111 | dp <= 7/8 | linarith [h_interval.2] | 0.0690 | 0.0690 | 0.0690 | h_hi ≤ 0.8750 |
| D10 | PhysicalDirect/JointHeight.lean:37, SourceActual.lean:83 | 51/100 < theta | linarith [theta_bounds.1] | 0.3630 | 0.3630 | 0.3630 | θ_lo ≥ 0.5100 |
| D11 | PhysicalDirect/Chosen.lean:52 | 85/100 < theta | linarith [theta_bounds.1] | 0.0230 | 0.0230 | 0.0230 | θ_lo ≥ 0.8500 |
| D12 | PhysicalDirect/FiniteError/FullW.lean:39, Transport/CentralErrorSaving.lean:31 | crude exponent 0.16*x + 1.34 - y(a+6e) <= 2 (a,e >= 0), x <= 1-ell_lo-y_lo | nlinarith [length_sum, ly_coarse, ell_interval] (products y*a, y*e >= 0) | 0.6000 | 0.6000 | 0.5972 | — |
| D13 | FullW.lean:57,170,176; CubeFiniteError.lean:52,58; CentralErrorSaving.lean:49 | h + zeta <= 1 and ell <= 1 | linarith [h_interval.2] / [ell_interval] | 0.1940 | 0.1940 | 0.1940 | h_hi ≤ 1.0000 |
| D14 | CommonProbe.lean:67, CanonicalReduction.lean:54, NonfloorTransport.lean:136 | 1/100 <= h + zeta (rpow exponent order) | linarith [h_interval.1] | 0.7830 | 0.7830 | 0.7830 | h_lo ≥ 0.0100 |
| E1 | Transport/Transport/FloorExponent.lean:40 (floor_loss_bound) | (16-6 ly) e <= 14 e (e>=0): ly >= 1/3 | nlinarith [ly_coarse, e*(ly-1/3) >= 0] | 0.1247 | 0.1247 | 0.1067 | y_lo ≥ 0.3333 |
| E2 | Transport/Transport/NormalizedTransportSaving.lean:97 (h1) | 7/8 - S + 8e + nu + sigma <= theta  with sigma+8e+nu <= 1/20: theta + S >= 0.925, S = y/2-h(17/50-1/6)-1/50 | linarith [small_saving, theta_lower] (+ hypotheses hbetalo, _hgeometric) | 0.0180 | 0.0180 | 0.0080 | θ_lo ≥ 0.8550; ss ≥ 0.0520 |
| E3 | Transport/Transport/PrincipalRemainderBounds.lean:589 (source_w_strict_exponent), :617,:621 (same hint) | e(1+h) - y/20 + 1/4000 <= 0 for e <= 1/1000 | nlinarith [h_interval, ly_coarse, theta_bounds] | 0.0208 | 0.0208 | 0.0199 | y_lo ≥ 0.0411 |
| E4 | Transport/Transport/PrincipalRemainderBounds.lean:592 (source_z_strict_exponent) | e <= h/600 - 1/4000 for e <= 1/1000 | nlinarith [h_interval, ly_coarse, theta_bounds] (linear in effect) | 7.2e-05 | 7.2e-05 | 7.2e-05 | h_lo ≥ 0.7500 |
| E5a | Transport/Transport/PrincipalRemainderRegion.lean:39-40 (remainder_unramified_bound, hR); callers PrincipalSlots.lean:32,252 and PrincipalRemainderRegion.lean:141 | 4 - 6 theta - 6*(4/25) <= -219/100  (coordR_norm_le exponent 4-6x-6z) | Real.rpow_le_rpow_of_exponent_le .. (by linarith) with hx: theta <= x.re (theta_bounds.1) | 0.0080 | 0.0080 | 0.0080 | θ_lo ≥ 0.8717 |
| E5b | Transport/Transport/PrincipalRemainderRegion.lean:45-46 (same lemma, hK) | 1 - theta - 9/10 <= -77/100 (coordK_norm_le exponent 1-x-w) | linarith [theta_bounds] | 0.0030 | 0.0030 | 0.0030 | θ_lo ≥ 0.8700 |
| E6 | Transport/Transport/PrincipalSlots.lean:108-109, 115-120 (principal_marked_error_bounds hRT, hBR); :328, :334-338 (region_marked_error_bounds hRT, hBR) | 3-5s <= -theta, 3-6s <= -theta with s >= theta: theta >= 3/4 | linarith [theta_bounds] with hs: theta <= s.re | 0.4920 | 0.4920 | 0.4920 | θ_lo ≥ 0.7500 |
| E7 | Transport/Transport/PrincipalSlots.lean:339-346 (region_marked_error_bounds hBKV: 1 - w - 6z <= -theta) | theta <= 0.94 | linarith [theta_bounds.2] | 0.0650 | 0.0650 | 0.0650 | θ_hi ≤ 0.9400 |
| F1 | PrincipalRemainder{Contours,FiniteProduct,FiniteProductX,Transport,Bounds,Region,RayThresholds,Normalized,Physical,PhysicalBounds}.lean, PrincipalSlots.lean, PrincipalSignal.lean:63, SignalShift.lean:58, TransportParameters.lean:95,191 | 0 < Q, 1 <= Q, 4 <= Q (from 480 <= Q), 0 < theta, 4/25 <= xi from 1/6 < xi, Z^(...) monotone: theta > 0 .. 1/2 | linarith [theta_bounds] used only as a weak positivity hint | 0.3730 | 0.3730 | 0.3730 | θ_lo ≥ 0.5000 |
| F2 | Transport/FinalCommonProbe.lean:45-46 (and TransportGeometry.lean:79) | theta <= 7/8 (the upper field must not exceed 7/8; 1/2 <= theta is A5) | theta_bounds.2.le (direct projection) | 0.0000 | 0.0000 | 0.0000 | θ_hi ≤ 0.8750 |
| G1 | Transport/Transport/FloorExponent.lean:25 (floor_source_margin) | floorSourceExponent(v) <= signal theta - 1/200 for v <= h+1e-10, i.e. 0.01 + 1.03 ell <= (5+3 ell-4h)/12 - fm | the field floor_margin itself (dsimp + linarith; it is a restatement) | field | field | field | — |
| G2 | TransportGeometry.lean:24 (field small_saving) -> NormalizedTransportSaving.lean:97 only | 7/100 < y/2 - h(17/50-1/6) - 1/50 | field | field | field | field | — |

**The theta-only bulk (row F1).** 136 of the 194 outside uses are `have hθ := Transport.theta_bounds` / `linarith [theta_bounds]` in
`PrincipalRemainder{Contours,FiniteProduct,FiniteProductX,Transport,Bounds,Region,RayThresholds,Normalized,Physical,PhysicalBounds}.lean`, `PrincipalSlots.lean`, `PrincipalSignal.lean:63`,
`SignalShift.lean:58`, `TransportParameters.lean:95,191`: positivity hints (`0 < Q`, `1 <= Q`, `4 <= Q` from `480 <= Q`, `4/25 <= xi` from `1/6 < xi`, `0 < theta`) or exponent comparisons that need theta >= 0.5..0.75 (`E6`: `3-5s <= -theta` with `s >= theta` needs theta >= 3/4).
I read every distinct pattern; the only sharp ones are `E5a/E5b` (rows above): `remainder_unramified_bound` (`PrincipalRemainderRegion.lean:24-90`) uses `coordR_norm_le`'s exponent `4-6x-6z` (`openai_baseline/.../Detector/EulerCoordinates.lean:47-53`)
and needs `4 - 6 theta - 24/25 <= -219/100` (hR, lines 39-40) and `1 - theta - 9/10 <= -77/100` (hK, lines 45-46); it is called at `PrincipalSlots.lean:32, 252` and `PrincipalRemainderRegion.lean:141` (`remainder_idealClosedCorrection_bound`, hence all `globalClosedCorrection`/`correction_*` bounds used by `PrincipalRemainderFiniteProduct.lean`).

---------------------------------------------------------------------------------------------------------------------

## 3. Does it survive the widening? (question 2)

### 3.1 Proof limits of each numeral [N] (`tb_results_thresholds.txt`)

| numeral | PR 83 | the proofs stay valid for | binding statement(s) |
|---|---|---|---|
| `theta_lo` | 0.873 | >= **0.871667** (then 0.870, 0.855, 0.850) | E5a `PrincipalRemainderRegion.lean:39-40`; E5b `:45-46`; E2; C1, D11 |
| `theta_hi` | 7/8 | <= **7/8** (it is the global ceiling `beta <= 7/8`; `theta <= 7/8` is used directly) | F2 `FinalCommonProbe.lean:46`; E7 `PrincipalSlots.lean:339-346` would allow 0.94 |
| `h_lo` | 0.793 | >= 0.75 | E4 `PrincipalRemainderBounds.lean:592` (`e <= h/600 - 1/4000`, e <= 1/1000); A1 needs `4 ell_hi < h_lo` |
| `h_hi` | 0.806 | <= **0.865** | B2 `FinalFixedHigh.lean:71-74` (`h + 5e-11 <= 7/8 - 1/100`); then D9 `SourceActual.lean:111` (0.875), A3/D1 (0.916) |
| `y_lo` | 0.458 | >= **0.403** | A3 `TransportGeometry.lean:55` and D1 `PhysicalDirect/Geometry.lean:87` (`h < 2y`); B1 0.364; E1 1/3; E3 0.041 |
| `y_hi` | 0.467 | <= **0.475** | D2 `SourceParameters.lean:51`, D3 `Active.lean:57` (`y/d <= 19/20`, d > 1/2); D4 0.495 |
| `ell_lo` | 0.1672 | >= 0.1484 | B1 `FinalFixedHigh.lean:64-70` |
| `ell_hi` | 0.171 | <= **0.19825** (theta >= 0.8671) | A1 `TransportGeometry.lean:58-62` (`4 ell < h`) |
| `ss` | 7/100 | >= **0.052** | E2 `NormalizedTransportSaving.lean:97` (`theta + S >= 7/8 + 1/20`) |

E2 note [D][I]: the `1/20` is `TransportParameters.geometric_budget` (`TransportParameters.lean:68`, `sigma + 8e + nu <= 1/20`); the actual `sigma + 8e + nu` is O(`D.t`) <= 4e-11, so the true requirement is `S > 7/8 - theta`, about 0.001, and `ss` could drop to ~0.002 if that hypothesis were tightened
(an edit of one structure field and its proof; not needed for any target considered here).

### 3.2 Widened boxes: margins [N] (`tb_results_statements.txt`, `tb_results_polygons.txt`)

All statements of the table above keep a positive margin in every box tried (F2 is the identity `theta_hi = 7/8`, margin 0 for the non-strict `theta <= 7/8`; G1/G2 are fields):

| box (changes vs PR 83) | theta_min of the (theta,h) polygon | smallest abstract margins | verdict |
|---|---|---|---|
| PR 83/86 (theta>.873, ell<.171) | 0.8739167 | E4 7e-5, C2 6e-3, B1 7.8e-3, D2/D3 8e-3 | current |
| minimal: `ell<1715/10000` | 0.8737917 | same; A1 0.107 | numeral-only |
| caller's example: `theta>.8735`, `ell<.175` | **0.8736445** | same; A1 0.093; E5a 0.011 | numeral-only, but polygon ends above 0.8735 (3.3) |
| `ell<175/1000` (theta>.873 kept) | 0.8736445 | same as above | numeral-only |
| future-proof: `ell<.175, y>.44, ss=.06` | 0.8730 (= theta_lo) | A3/D1 0.074, E2 0.008, B1 6.3e-3, D2/D3 8e-3 | numeral-only (the y_lo and ss lines have no precedent: unverified by a compiler) |
| stress (not proposed) | — | `ell<0.2` fails A1; `theta_lo<0.8717` fails E5a; `h_hi>0.865` fails B2; `y_hi>0.475` fails D2/D3 | real proof edits |

Over the parameter polygon of each box the worst margins are the same list (parameter-mode column of `tb_statements.py`: C2 6.0e-3, D2/D3 8.0e-3, E5a 8e-3..0.0135, E5b 3.0e-3..3.9e-3, E2 0.0124..0.0192); at the two target points (0.8739058, 0.8047), (0.8738, 0.8037) all margins are >= 1.8e-3 except E4 (9e-5) and the field slacks.

### 3.3 What really limits theta: the functional fields [D][N]

With h eliminated, the three field constraints are affine in ell (equivalently theta):

* `floor_margin`: **`h <= 1.205 - 2.34 ell - 2.01e-10`**, i.e. `9.36 theta - 7.375` (`tb_common.floor_slack`; the h-coefficient of the left side `4/25 x - 51/100 y + 67/100 dPlus` is `-0.16 - 0.51 + 0.67 = 0`, the right side `signal - fm` has slope `-1/3` in h);
* `small_saving` (`ss`): `h > 150 (ss + 1/50 + ell)/49 = 0.27551 + 3.06122 ell` for ss = 7/100;
* `ly_coarse.1`: `h > y_lo + 2 ell`.

(theta, h) windows (`tb_results_relation.txt`, stock `ss = 7/100`, `y_lo = 0.458`, floor `fm = 1/200`; h in 1e-6 as the models take it):

| theta | ell | h_floor (max) | h_min (small_saving) | h_min (y>.458) | window | S at h_floor | y at h_floor |
|---|---|---|---|---|---|---|---|
| 0.873995 (PR 83) | 0.1706867 | 0.805593 | 0.798020 | 0.799373 | [0.79937, 0.80559] | 0.07247 | 0.46422 |
| 0.8739558 (PR 86) | 0.1708435 | 0.805226 | 0.798500 | 0.799687 | [0.79969, 0.80523] | 0.07220 | 0.46354 |
| 0.8739167 | 0.1709999 | 0.804860 | 0.798979 | 0.800000 | [0.80000, 0.80486] | 0.07192 | 0.46286 |
| **0.8739058** | **0.1710435** | 0.804758 | 0.799113 | 0.800087 | [0.80009, 0.80476] | 0.07184 | 0.46267 |
| 0.8739 | 0.1710667 | 0.804704 | 0.799184 | 0.800133 | [0.80013, 0.80470] | 0.07180 | 0.46257 |
| **0.8738** | **0.1714667** | 0.803768 | 0.800408 | 0.800933 | [0.80093, 0.80377] | 0.07110 | 0.46083 |
| 0.8737 | 0.1718667 | 0.802832 | 0.801633 | 0.801733 | [0.80173, 0.80283] | 0.07039 | 0.45910 |
| 0.8736 | 0.1722667 | 0.801896 | 0.802857 | 0.802533 | **empty** | 0.06969 | 0.45736 |
| 0.8735 | 0.1726667 | 0.800960 | 0.804082 | 0.803333 | **empty** | 0.06898 | 0.45563 |
| 0.873 | 0.1746667 | 0.796280 | 0.810204 | 0.807333 | **empty** | 0.06545 | 0.44695 |

So with the stock fields the polygon closes at theta = 0.873644 (`small_saving` meets `floor_margin` at h = 0.802312) and the caller's `theta > 0.8735` cannot be met: **at theta in (0.8735, 0.87364) there is no point (theta,h) satisfying `BoundsN`**.
This is an artefact of two slack constants, not of the mathematics: `ss` is needed only down to 0.052 (E2) and `y_lo` down to 0.403 (A3/D1). theta_min as a function of the constants (box otherwise PR 83 with `ell_hi = .175`):

| ss \ y_lo | 0.458 | 0.450 | 0.445 | 0.440 | 0.403 |
|---|---|---|---|---|---|
| 0.070 | 0.87364 | 0.87364 | 0.87364 | 0.87364 | 0.87364 |
| 0.066 | 0.87364 | 0.87318 | 0.87308 | 0.87308 | 0.87308 |
| 0.065 | 0.87364 | 0.87318 | 0.87294 | 0.87294 | 0.87294 |
| 0.060 | 0.87364 | 0.87318 | 0.87292 | 0.87292 | 0.87292 |

(0.87292 is the `ell<0.175` edge itself; `theta > 0.873` then binds.)

The one remaining hard coupling is the floor ceiling `h <= 9.36 theta - 7.375`: it comes from the rows at the zero-free floor `a = 51/100` (`FloorExponent.lean:14-33`: `floorSourceExponent v = centralScale (51/100) 0 + 67/100 v - 3 ell/20 = 0.16 x - 0.15 - 0.51 y + 0.67 v - 0.15 ell` for `v <= h + 1e-10`) and its right side keeps the loss budget `fm = 1/200`
(`CubeFloorSaving.lean:54 htotal <= 1/200`). The models give it up gracefully: `theta*(h)` on PR 86's faces is `0.873958069 (h=.803)`, `...956735 (.804)`, `...955849 (.805)`, `...955786 (.8051)` (`analysis/lemmaW/logs/hscan_both.log`), slope -1.07e-3, so the floor-forced h costs +3e-7 at h = 0.8047 and +1.3e-6 at h = 0.8037.
Lowering `fm` (e.g. 1/400 raises the ceiling by 7.5e-3) is **not** a numeral edit: `1/200` is threaded through `FloorExponent.lean:24`, `CubeFloorSaving.lean:54`, `CubeFloorCollected.lean:54`, `HighApproximation.lean:121,198`, `SharedNonfloor.lean:54`, `NonfloorTransport.lean:58`,
`TransportParameters.lean:71,158,254`, `FinalFixedHigh.lean:88,131`; the gain would be <= 1e-6 in theta. Not worth it.

### 3.4 The other scalar side conditions of the return (not box) [N] (`tb_results_receipts.txt`)

`pr86.receipts` (mirrors `Return/*.lean`) with PR 86's faces, box widened to (theta>.873, h<.806, y<.467, ell<.175), h on the floor ceiling: **no receipt is negative for theta >= 0.8737** (smallest: `small_saving` 3.8e-4, `y>458/1000` 1.1e-3 at 0.8737;
Gram/conductor/schedule receipts all >= 1.4e-2 (`prime_supply`) except `incumbent` 2.6e-3, `theta>lo` 7e-4 and `theta<7/8`); at 0.8736 only `y>458/1000` (-7.3e-4) and `small_saving` (-3.5e-4) fail — the same two fields as in 3.3. So I find no obstruction outside the box fields for theta in [0.8737, 0.8739558];
the Bernstein cover itself needs new faces and is not part of this question.

---------------------------------------------------------------------------------------------------------------------

## 4. theta <-> ell <-> h <-> y at the optimum (question 3)

Exact: `ell = 11/3 - 4 theta = 4c - 1/3` (c = 1-theta), `x = 1 + ell - h`, `y = h - 2 ell`, `signal theta = (5 + 3 ell - 4 h)/12`, `dPlus = h + 1e-10`.
With the models' h (the floor ceiling): `h = 9.36 theta - 7.375`, `y = 17.36 theta - 14.708333`, `x = 12.041667 - 13.36 theta`.

| theta | ell (needs `ell_hi` >) | h (ceiling; 4-digit choice) | y | x | recommended `ell_hi` |
|---|---|---|---|---|---|
| 0.8739167 | 0.1709999 (0.171) | 0.804860 (0.8048) | 0.46286 | 0.36614 | — (current) |
| **0.8739058** (bar 5e-5) | **0.1710435** | 0.804758 (0.8047) | 0.46267 | 0.36629 | 0.1711 minimum, 0.1715 comfortable |
| 0.8739 | 0.1710667 | 0.804704 (0.8047) | 0.46257 | 0.36636 | |
| **0.8738** | **0.1714667** | 0.803768 (0.8037) | 0.46083 | 0.36770 | 0.172 (0.1715 leaves 3e-5) |
| 0.8737 | 0.1718667 | 0.802832 (0.8028) | 0.45910 | 0.36904 | 0.172 (window is 1.1e-3 wide) |
| 0.8736 | 0.1722667 | 0.801896 | 0.45736 | 0.37037 | needs `ss`, `y_lo` relaxed |
| 0.873 | 0.1746667 | 0.796280 | 0.44695 | 0.37839 | 0.175 |

Rational forms: theta = 0.8739058 = 4369529/5000000 gives ell = 641413/3750000; theta = 0.8738 = 4369/5000 gives ell = 643/3750.
For the (bar) target, `small_saving` has slack 1.8e-3 (stock `ss`), `y>.458` 4.6e-3, `floor_margin` 0 by construction (keep h one digit below the ceiling, e.g. 0.8047 leaves 5.8e-5 in h).
The `Parameters` fields (`Gram_*` receipts: `ell<x`, `x<y`, `2x>y+ell`, `ell<1/5`, `y<1/2`) keep margins >= 2.7e-2 down to theta = 0.8735.

---------------------------------------------------------------------------------------------------------------------

## 5. Lean work to widen the box (question 4)

Every change below was derived by reading; none has been compiled (no `lake`/`lean` allowed). `tb_patch_dryrun.py` prints the exact diff against PR 83's files for any numerals and checks that no old numeral remains in `ReturnD/` + `Return/`.

| option | numeral lines (PR 83 `ReturnD/`) | proofs touched | verdict |
|---|---|---|---|
| **A** `ell<175/1000` (covers theta >= 0.87365 with stock fields) | `TransportGeometry.lean:23, 60, 95` (+ docstring `:16-18`) | none | 3 lines, 1 file; same as PR 76 -> PR 83 |
| **B** = A + `y>440/1000`, `small_saving 6/100` (covers theta down to 0.873) | + `TransportGeometry.lean:22, 101` (y_lo), `:24, 104` (ss); `Transport/FinalFixedHigh.lean:67, 110` (`458/1000<Geometry.y`) | none (margins in 3.2) | 7 lines, 2 files; y_lo/ss edits have no compiled precedent |
| C raise `h_hi` (not needed: models need <= 0.8048) | `TransportGeometry.lean:21, 100`; `FinalFixedHigh.lean:72, 115` | none up to 0.865 | skip |
| D lower `theta_lo` below 0.8717 | `TransportGeometry.lean:20, 98, 99` + exponent constants `219/100`, `77/100` at `PrincipalRemainderRegion.lean:36-46` | **yes** (2 constants, then hKV/hRT re-checked) | not needed |
| E change the floor budget `1/200` | 12 statements in 9 files (3.3) | yes (threaded) | not worth 1e-6 |
| F column excess `x+y = 1-ell+e` (r3 lever P1) | identities `TransportGeometry.lean:39-44, 69-78`; Collet's `Parameters.x_add_y` | **yes** | separate project |

Around the edit:

* **Fork.** The class lives in `ReturnD/`, which PR 86 imports from PR 83, so a PR with a different `BoundsN` forks all 119 modules (15,080 lines, 0.96 MB; `find ReturnD -name '*.lean'`) under its own `Submissions.<slug>.ReturnD` and namespace (PR 83 did this from PR 76; a sed over two tokens, `sil_density_split_20261026` and `SilDensitySplit` (the longer names `SilDensitySplitReturn`, `SilDensitySplitTransportLow` contain it), is enough; `grep -rhoi 'density_\?split'` finds no other form).
  `Return/` (44 modules, 5,415 lines) is regenerated anyway for a new theta; only `TransportInstances.lean:9-12` (re-proved by `norm_num`) and the four `local instance` lines (section 1.1) must point at the new class.
* **Instance.** `finalBounds` needs no text change: its six `norm_num` goals are re-checked at the new constants.
* **Build.** All 119 + 44 modules recompile because `TransportGeometry.lean` is imported by every `ReturnD/` module. Precedent: mixed-step build 3 compiled 161 modules in 923 s wall (2 Lean processes, 1738 s summed, ALL-OK); the admission limits (30 min per module, 12 h total, `replan/process.md` 2.2) are not an issue.
* **Review risk.** Option A is the most precedented edit in the tree; B adds two lower-end numerals whose consumers are all single `linarith` calls with margins >= 6e-3 (B1) / 0.074 (A3, D1), i.e. low risk but uncompiled.

---------------------------------------------------------------------------------------------------------------------

## 6. Caveats

* Margins are computed on the hypotheses I identified at each site; `linarith` may use extra context facts (this only helps), but if I misread a goal the limit would move. The goals behind the small margins (E4, D2/D3, E5a/b, B1, E2) were checked against the source text line by line.
* The abstract-box margins assume independent intervals; the polygon (identities `ell_eq`, `x_eq`, `y_eq`) is strictly smaller, so the abstract margins are conservative.
* `hscan_both.log` measures theta*(h) for PR 86's faces only; new faces from the amplifier work may have a different (still small) slope.
* "Future-proof" (B) was not run through Lean. If `y_lo`/`ss` are left alone, theta >= 0.87365 is what the stock fields allow.

## 7. Files (all in `research/newpowers/tb/`)

| file | content |
|---|---|
| `tb_common.py` | exact relations, `Box`, polygon (half-plane intersection), floor/small_saving/y windows |
| `tb_statements.py` | the 36 statements with their needed inequality; abstract-box and parameter margins; polygon worst cases |
| `tb_thresholds.py` | per-numeral proof limits (table 3.1) |
| `tb_make_tables.py` | Markdown table of section 2 (`tb_table_statements.md`) |
| `tb_relation.py` | theta <-> ell/h/y tables and the (ss, y_lo, fm) -> theta_min grids (section 3.3, 4) |
| `tb_polygons.py` | polygon vertices with active constraints (`tb_results_polygons.txt`) |
| `tb_receipts.py` + `tc/` | the return's scalar receipts at lower theta (verbatim copies of `pr86.py`, `cert_return.py`, `gen_return_lean.py`, `chain_params.py`); `tb_results_receipts.txt` |
| `tb_sites.py` -> `sites.txt` | index of the 229 textual uses (file:line:name) |
| `tb_patch_dryrun.py` | prints the diff of option A/B/C/D numerals against PR 83 and checks no old numeral is left |
| `tb_results_*.txt` | raw outputs quoted above |

---------------------------------------------------------------------------------------------------------------------

## Appendix A. Every consumer line of PR 83 `ReturnD/` (file: field:lines)

`θ` = `theta_bounds` (or its alias `Transport.theta_bounds`), `θlo` = `theta_lower`, `h`, `y`, `ell` = `h_interval`, `ly_coarse`, `ell_interval`, `ss` = `small_saving`, `fm` = `floor_margin`; derived lemmas of `TransportGeometry.lean` by their statement (`dP<1` = `dPlus_lt_one`, `h+ext<1` = `extended_h_lt_one`, `h>0` = `h_pos`).
Generated by `tb/tb_sites.py` (`sites.txt` has the per-occurrence list).

```
GenericFeedback.lean                                         θ:23,44; h:26; dP<1:52
PhysicalDirect/Active.lean                                   y:57
PhysicalDirect/Chosen.lean                                   θ:52
PhysicalDirect/Finite/Bridge.lean                            ell:39; θ:39
PhysicalDirect/Finite/Geometry.lean                          h:63
PhysicalDirect/Finite/Summation.lean                         h:82
PhysicalDirect/FiniteError/FullW.lean                        ell:39,176; y:39; h:57,170
PhysicalDirect/Geometry.lean                                 h:87; y:87
PhysicalDirect/JointHeight.lean                              θ:37
PhysicalDirect/OldActive.lean                                y:45,160
PhysicalDirect/OldGeometry.lean                              y:66,158; ell:157
PhysicalDirect/SourceActual.lean                             θ:83; h:111
PhysicalDirect/SourceLedger.lean                             h:81; dP<1:105
PhysicalDirect/SourceParameters.lean                         y:51
Transport/FinalCommonProbe.lean                              θ:45,46
Transport/FinalFixedHigh.lean                                ell:66,109; y:67,110; h:72,115
Transport/Transport/CanonicalReduction.lean                  h:45,54
Transport/Transport/CentralErrorSaving.lean                  y:31; h:49
Transport/Transport/CommonProbe.lean                         h:67
Transport/Transport/CubeFiniteError.lean                     h:52; ell:58
Transport/Transport/CubeFloorSaving.lean                     h+ext<1:86
Transport/Transport/FloorExponent.lean                       fm:25; y:40
Transport/Transport/LargeTail.lean                           h>0:55,66
Transport/Transport/NonfloorTransport.lean                   h:136
Transport/Transport/NormalizedTransportSaving.lean           ss:97; θlo:97
Transport/Transport/PrincipalRemainderBounds.lean            θ:54,343,405,501,511,526,589,592,617,621; h:589,592,617,621; y:589,592,617,621
Transport/Transport/PrincipalRemainderContours.lean          θ:86,90,96,253,257,331,334,436,442,468,471,534,540,676,677,770,771,774,775
Transport/Transport/PrincipalRemainderFiniteProduct.lean     θ:46,51,64,80,105,129,130,132,134,137,139,142,191,204,205,212,214,218,223,310,329,434
Transport/Transport/PrincipalRemainderFiniteProductX.lean    θ:26,43
Transport/Transport/PrincipalRemainderNormalized.lean        θ:66,79
Transport/Transport/PrincipalRemainderPhysical.lean          θ:68
Transport/Transport/PrincipalRemainderPhysicalBounds.lean    θ:50,57
Transport/Transport/PrincipalRemainderRayThresholds.lean     θ:32,36
Transport/Transport/PrincipalRemainderRegion.lean            θ:28,49,65,66,91
Transport/Transport/PrincipalRemainderTransport.lean         θ:98,104,108,113,118,121,151,168,190,193,195,275,277,278,302,355,404
Transport/Transport/PrincipalSignal.lean                     θ:63
Transport/Transport/PrincipalSlots.lean                      θ:29,45,54,62,73,126,140,155,166,188,193,206,216,247,264,274,283,293,307,360,381,399,412,425
Transport/Transport/SignalShift.lean                         θ:58
Transport/TransportParameters.lean                           θ:95,191
TransportGeometry.lean                                       θ:20,79,80,98,99; h:21,54,55,59,64,96,97,100; y:22,55,101; ell:23,60,95; ss:24,104; fm:25; h>1/2:54; h<2y:55; 4ell<h:58; dP<1:64; θ<7/8:79; θ>1/2:80; h+ext<1:97; θlo:98
```
