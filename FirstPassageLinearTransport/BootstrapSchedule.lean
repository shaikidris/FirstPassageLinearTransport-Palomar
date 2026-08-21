/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.GlobalAssembly

/-!
# Logarithmic bootstrap schedule

Scalar control of the recursively generated density prefactor and proof that
the logarithmic stopped-stage schedule has vanishing dyadic-shell exceptional
proportion.
-/

namespace FirstPassageLinearTransport

open scoped Real Topology BigOperators
open Filter

noncomputable section

/-- A finite geometric clock sum is bounded by its infinite-series value. -/
theorem clockGeomLeInvOneSub {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ R, clockGeom r R ≤ (1 - r)⁻¹ := by
  intro R
  induction R with
  | zero =>
      simpa [clockGeom] using hr1.le
  | succ R ih =>
      rw [clockGeom]
      have hden : 0 < 1 - r := sub_pos.mpr hr1
      have hmul : r * clockGeom r R ≤ r * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left ih hr0
      calc
        1 + r * clockGeom r R ≤ 1 + r * (1 - r)⁻¹ :=
          by simpa [add_comm] using add_le_add_left hmul 1
        _ = (1 - r)⁻¹ := by
          field_simp
          ring

/-- The logarithm of the explicit bootstrap-prefactor majorant. -/
def bootstrapLogBound {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) (R : ℕ) : ℝ :=
  Real.log (quadraticWindowGlobalConstant eta + 2) +
    (R : ℝ) * Real.log (bootstrapStageK p chi Dc) +
    2 * (R : ℝ) * Real.log Dc⁻¹ +
    2 * (R : ℝ) ^ 2 * Real.log chi⁻¹

/-- Before taking the logarithmic stage schedule, the shell error has this
single exact exponential majorant. -/
theorem shellBootstrapRatioLeExp
    {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) (R M : ℕ) :
    shellExceptionalRatio (bootstrapSet p R) M ≤
      Real.exp (Real.log 2 + bootstrapLogBound p chi Dc R -
        Real.log 2 * bootstrapD chi Dc R * M) := by
  have hPD := bootstrapSet_powerDense p hchi0 hchir hchi1
    hDc0 hDcRate hchiDc R
  have hshell := shellExceptionalRatio_le_of_powerDense hPD M
  have hC := bootstrapC_exp_bound p hchi0 hchir hchi1
    hDc0 hDc1 hchiDc R
  have hCpos := (bootstrapC_pos p hchi0 hchir hDc0 hchiDc R).le
  have hlog2 : Real.exp (Real.log 2) = 2 :=
    Real.exp_log (by norm_num)
  calc
    shellExceptionalRatio (bootstrapSet p R) M
        ≤ 2 * bootstrapC p chi Dc R *
            Real.exp (-(Real.log 2 * bootstrapD chi Dc R * M)) := hshell
    _ ≤ 2 * (bootstrapC p chi Dc R + 2) *
            Real.exp (-(Real.log 2 * bootstrapD chi Dc R * M)) := by
          gcongr
          · linarith
    _ ≤ 2 * Real.exp (bootstrapLogBound p chi Dc R) *
            Real.exp (-(Real.log 2 * bootstrapD chi Dc R * M)) := by
          gcongr
          simpa [bootstrapLogBound] using hC
    _ = Real.exp (Real.log 2 + bootstrapLogBound p chi Dc R -
          Real.log 2 * bootstrapD chi Dc R * M) := by
          rw [show Real.log 2 + bootstrapLogBound p chi Dc R -
              Real.log 2 * bootstrapD chi Dc R * M =
            Real.log 2 + (bootstrapLogBound p chi Dc R -
              Real.log 2 * bootstrapD chi Dc R * M) by ring,
            Real.exp_add, hlog2]
          rw [mul_assoc, ← Real.exp_add]
          congr 1

/-- Density-loss exponent induced by a logarithmic stage schedule. -/
def densityGamma (omega chi : ℝ) : ℝ :=
  omega * Real.log (1 / chi)

/-- Exact conversion between scheduled density loss and a power of the shell
index. -/
theorem rpowLogScheduleIdentity
    {chi omega x : ℝ} (hchi : 0 < chi) (hx : 0 < x) :
    chi ^ (omega * Real.log x) =
      x ^ (-densityGamma omega chi) := by
  rw [Real.rpow_def_of_pos hchi, Real.rpow_def_of_pos hx]
  unfold densityGamma
  rw [one_div, Real.log_inv]
  congr 1
  ring

/-- Flooring the logarithmic stage count can only improve the terminal
density exponent, because `chi ≤ 1`. -/
theorem scheduleDensityLower
    {chi Dc omega : ℝ} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1)
    (hDc0 : 0 ≤ Dc) (homega0 : 0 ≤ omega) (M : ℕ) :
    Dc * ((M : ℝ) + 4) ^ (-densityGamma omega chi) ≤
      bootstrapD chi Dc (stageCount omega M) := by
  have hM4 : (0 : ℝ) < (M : ℝ) + 4 := by positivity
  have hR := stageCount_le homega0 M
  have hp : chi ^ (omega * Real.log ((M : ℝ) + 4)) ≤
      chi ^ (stageCount omega M : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hchi0 hchi1 hR
  rw [rpowLogScheduleIdentity hchi0 hM4,
    Real.rpow_natCast] at hp
  simpa [bootstrapD] using mul_le_mul_of_nonneg_left hp hDc0

/-- Quadratic-log coefficient controlling the scheduled bootstrap prefactor. -/
def bootstrapScheduleA {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc omega : ℝ) : ℝ :=
  Real.log (quadraticWindowGlobalConstant eta + 2) +
    omega * Real.log (bootstrapStageK p chi Dc) +
    2 * omega * Real.log Dc⁻¹ +
    2 * omega ^ 2 * Real.log chi⁻¹

/-- On a logarithmic schedule, the full recursively generated prefactor has
only quadratic-logarithmic cost. -/
theorem bootstrapLogBoundScheduleLe
    {r eta chi Dc omega : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (homega0 : 0 ≤ omega) (M : ℕ) :
    bootstrapLogBound p chi Dc (stageCount omega M) ≤
      bootstrapScheduleA p chi Dc omega *
        (Real.log ((M : ℝ) + 4) + 1) ^ 2 := by
  let x := Real.log ((M : ℝ) + 4)
  let R : ℝ := stageCount omega M
  let b0 := Real.log (quadraticWindowGlobalConstant eta + 2)
  let b1 := Real.log (bootstrapStageK p chi Dc)
  let b2 := Real.log Dc⁻¹
  let b3 := Real.log chi⁻¹
  have hx0 : 0 ≤ x := by
    dsimp [x]
    apply Real.log_nonneg
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR : R ≤ omega * x := by
    dsimp [R, x]
    exact stageCount_le homega0 M
  have hb0 : 0 ≤ b0 := by
    dsimp [b0]
    apply Real.log_nonneg
    linarith [(extendedWindow_powerDense p).C_pos]
  have hb1 : 0 ≤ b1 := by
    dsimp [b1]
    apply Real.log_nonneg
    unfold bootstrapStageK
    have hK : 0 < pullbackGlobalConstant p chi Dc := by
      have hnum : 0 < 2 * pullbackShellConstant p chi Dc :=
        mul_pos (by norm_num) (pullbackShellConstant_pos p hchir)
      have hden : 0 < 2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 := by
        have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        have hchiDc : chi * Dc < 1 := by
          have hprod : chi * Dc ≤ chi * 1 :=
            mul_le_mul_of_nonneg_left hDc1 hchi0.le
          nlinarith [hchir.trans p.r_lt_one]
        have harg : -Real.log 2 < -(chi * Dc * Real.log 2) := by
          nlinarith
        have hexp := Real.exp_lt_exp.2 harg
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
        nlinarith
      simpa [pullbackGlobalConstant] using div_pos hnum hden
    linarith
  have hb2 : 0 ≤ b2 := by
    dsimp [b2]
    exact Real.log_nonneg ((one_le_inv₀ hDc0).2 hDc1)
  have hb3 : 0 ≤ b3 := by
    dsimp [b3]
    exact Real.log_nonneg ((one_le_inv₀ hchi0).2 hchi1)
  have hR2 : R ^ 2 ≤ (omega * x) ^ 2 := by nlinarith
  have hraw : b0 + R * b1 + 2 * R * b2 + 2 * R ^ 2 * b3 ≤
      b0 + (omega * x) * b1 + 2 * (omega * x) * b2 +
        2 * (omega * x) ^ 2 * b3 := by
    gcongr
  have hx1 : 1 ≤ (x + 1) ^ 2 := by nlinarith
  have hxx : x ≤ (x + 1) ^ 2 := by nlinarith
  have hxx2 : x ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
  dsimp [bootstrapLogBound, bootstrapScheduleA, x, R, b0, b1, b2, b3]
    at hraw ⊢
  calc
    _ ≤ Real.log (quadraticWindowGlobalConstant eta + 2) +
        (omega * Real.log ((M : ℝ) + 4)) *
          Real.log (bootstrapStageK p chi Dc) +
        2 * (omega * Real.log ((M : ℝ) + 4)) * Real.log Dc⁻¹ +
        2 * (omega * Real.log ((M : ℝ) + 4)) ^ 2 *
          Real.log chi⁻¹ := hraw
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hx1 hb0,
        mul_le_mul_of_nonneg_left hxx (mul_nonneg homega0 hb1),
        mul_le_mul_of_nonneg_left hxx (mul_nonneg homega0 hb2),
        mul_le_mul_of_nonneg_left hxx2
          (mul_nonneg (sq_nonneg omega) hb3)]

/-- A shifted shell scale dominates a fixed fraction of its unshifted
counterpart. -/
theorem shiftedDensityScaleLower (gamma : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    (1 / 5 : ℝ) * ((M : ℝ) + 4) ^ (1 - gamma) ≤
      (M : ℝ) * ((M : ℝ) + 4) ^ (-gamma) := by
  have hx : (0 : ℝ) < (M : ℝ) + 4 := by positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hfrac : ((M : ℝ) + 4) / 5 ≤ M := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hmul := mul_le_mul_of_nonneg_right hfrac
    (Real.rpow_nonneg hx.le (-gamma))
  calc
    (1 / 5 : ℝ) * ((M : ℝ) + 4) ^ (1 - gamma) =
        (((M : ℝ) + 4) / 5) * ((M : ℝ) + 4) ^ (-gamma) := by
      rw [show (1 : ℝ) - gamma = 1 + (-gamma) by ring,
        Real.rpow_add hx, Real.rpow_one]
      ring
    _ ≤ (M : ℝ) * ((M : ℝ) + 4) ^ (-gamma) := hmul

/-- The exact logarithmic bootstrap schedule has vanishing exceptional
proportion on complete dyadic shells whenever its density exponent is
subcritical. -/
theorem shellBootstrapRatioTendstoZero
    {r eta chi Dc omega : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hdensity : densityGamma omega chi < 1) :
    Tendsto (fun M =>
      shellExceptionalRatio (shellBootstrap p omega M) M)
      atTop (nhds 0) := by
  let gamma := densityGamma omega chi
  let s := 1 - gamma
  let A := bootstrapScheduleA p chi Dc omega
  let B := 2 * (|A| + 1)
  let c := Real.log 2 * Dc / 5
  let C0 := Real.log 2 + 2 * (|A| + 1)
  have hs : 0 < s := by dsimp [s, gamma]; linarith
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htReal := tendsto_exp_log_sq_sub_rpow (A := B) hc hs
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have htCore : Tendsto (fun M : ℕ =>
      Real.exp (B * (Real.log ((M : ℝ) + 4)) ^ 2 -
        c * ((M : ℝ) + 4) ^ s)) atTop (nhds 0) :=
    htReal.comp hxT
  have htUpper : Tendsto (fun M : ℕ =>
      Real.exp (C0 + B * (Real.log ((M : ℝ) + 4)) ^ 2 -
        c * ((M : ℝ) + 4) ^ s)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _M : ℕ => Real.exp C0)
        atTop (nhds (Real.exp C0)) := tendsto_const_nhds
    have hmul : Tendsto (fun M : ℕ => Real.exp C0 *
        Real.exp (B * (Real.log ((M : ℝ) + 4)) ^ 2 -
          c * ((M : ℝ) + 4) ^ s)) atTop
        (nhds (Real.exp C0 * 0)) := hconst.mul htCore
    convert hmul using 1
    · funext M
      rw [show C0 + B * Real.log ((M : ℝ) + 4) ^ 2 -
          c * ((M : ℝ) + 4) ^ s =
        C0 + (B * Real.log ((M : ℝ) + 4) ^ 2 -
          c * ((M : ℝ) + 4) ^ s) by ring,
        Real.exp_add]
    · simp
  have hupper : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (shellBootstrap p omega M) M ≤
        Real.exp (C0 + B * (Real.log ((M : ℝ) + 4)) ^ 2 -
          c * ((M : ℝ) + 4) ^ s) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    let R := stageCount omega M
    let x := Real.log ((M : ℝ) + 4)
    have hbase := shellBootstrapRatioLeExp p hchi0 hchir hchi1
      hDc0 hDc1 hDcRate hchiDc R M
    have hlog := bootstrapLogBoundScheduleLe p hchi0 hchir hchi1
      hDc0 hDc1 homega0.le M
    have hD := scheduleDensityLower hchi0 hchi1 hDc0.le
      homega0.le M
    have hscale := shiftedDensityScaleLower gamma hM
    have hDM : Dc / 5 * ((M : ℝ) + 4) ^ s ≤
        bootstrapD chi Dc R * M := by
      have h1 := mul_le_mul_of_nonneg_left hscale hDc0.le
      have h2 := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg M)
      dsimp [s]
      nlinarith
    have hxSq : (x + 1) ^ 2 ≤ 2 * x ^ 2 + 2 := by
      nlinarith [sq_nonneg (x - 1)]
    have hA : A ≤ |A| + 1 := by linarith [le_abs_self A]
    have hAx : A * (x + 1) ^ 2 ≤
        (|A| + 1) * (2 * x ^ 2 + 2) := by
      exact (mul_le_mul_of_nonneg_right hA (sq_nonneg (x + 1))).trans
        (mul_le_mul_of_nonneg_left hxSq (by positivity))
    apply hbase.trans
    apply Real.exp_le_exp.2
    dsimp [shellBootstrap, R] at hbase
    dsimp [gamma, s, A, B, c, C0, x] at hlog hD hDM hAx ⊢
    have hpref := hlog.trans hAx
    have hdecay := mul_le_mul_of_nonneg_left hDM
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    nlinarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htUpper
  · filter_upwards with M
    exact shellExceptionalRatio_nonneg _ _
  · exact hupper

set_option maxHeartbeats 2000000 in
/-- Quantitative strengthening of the varying-shell estimate.  Every strict
power below the density exponent is available with shell prefactor `2`. -/
theorem eventuallyShellBootstrapRatioLeStretched
    {r eta chi Dc omega sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (shellBootstrap p omega M) M ≤
        2 * Real.exp (-c * ((M : ℝ) + 4) ^ sigma) := by
  let gamma := densityGamma omega chi
  let s := 1 - gamma
  let A := bootstrapScheduleA p chi Dc omega
  let B := 2 * (|A| + 1)
  let c0 := Real.log 2 * Dc / 5
  let C0 := Real.log 2 + 2 * (|A| + 1)
  let c := c0 / 4
  have hs : 0 < s := by dsimp [s, gamma]; linarith
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let q := c0 / (8 * (|B| + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hlogSmallReal :=
    (isLittleO_log_rpow_rpow_atTop (s := s) 2 hs).bound hq
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogSmall := hxT.eventually hlogSmallReal
  have hpowT : Tendsto (fun M : ℕ => ((M : ℝ) + 4) ^ s)
      atTop atTop := (tendsto_rpow_atTop hs).comp hxT
  have hconstLarge : ∀ᶠ M : ℕ in atTop,
      8 * (|C0| + 1) / c0 ≤ ((M : ℝ) + 4) ^ s :=
    (tendsto_atTop.1 hpowT) _
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlogSmall, hconstLarge,
    eventually_ge_atTop (1 : ℕ)] with M hlogSmall hconstLarge hM
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  let lx := Real.log x
  have hx : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hxs0 : 0 ≤ x ^ s := Real.rpow_nonneg (zero_le_one.trans hx) _
  have hlx0 : 0 ≤ lx := by dsimp [lx]; exact Real.log_nonneg hx
  have hbase := shellBootstrapRatioLeExp p hchi0 hchir hchi1
    hDc0 hDc1 hDcRate hchiDc R M
  have hlog := bootstrapLogBoundScheduleLe p hchi0 hchir hchi1
    hDc0 hDc1 homega0.le M
  have hD := scheduleDensityLower hchi0 hchi1 hDc0.le
    homega0.le M
  have hscale := shiftedDensityScaleLower gamma hM
  have hDM : Dc / 5 * x ^ s ≤ bootstrapD chi Dc R * M := by
    have h1 := mul_le_mul_of_nonneg_left hscale hDc0.le
    have h2 := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg M)
    dsimp [x, s]
    nlinarith
  have hxSq : (lx + 1) ^ 2 ≤ 2 * lx ^ 2 + 2 := by
    nlinarith [sq_nonneg (lx - 1)]
  have hAle : A ≤ |A| + 1 := by linarith [le_abs_self A]
  have hAx : A * (lx + 1) ^ 2 ≤
      (|A| + 1) * (2 * lx ^ 2 + 2) := by
    exact (mul_le_mul_of_nonneg_right hAle (sq_nonneg (lx + 1))).trans
      (mul_le_mul_of_nonneg_left hxSq (by positivity))
  have hexpBound :
      shellExceptionalRatio (shellBootstrap p omega M) M ≤
        Real.exp (C0 + B * lx ^ 2 - c0 * x ^ s) := by
    apply hbase.trans
    apply Real.exp_le_exp.2
    dsimp [shellBootstrap, R] at hbase
    dsimp [gamma, s, A, B, c0, C0, x, lx] at hlog hD hDM hAx ⊢
    have hpref := hlog.trans hAx
    have hdecay := mul_le_mul_of_nonneg_left hDM
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlx0 2),
    Real.norm_eq_abs, abs_of_nonneg hxs0] at hlogSmall
  have hBLog : B * lx ^ (2 : ℕ) ≤ c0 / 8 * x ^ s := by
    have hBabs : B ≤ |B| + 1 := by linarith [le_abs_self B]
    have hmul := mul_le_mul_of_nonneg_left hlogSmall
      (by positivity : 0 ≤ |B| + 1)
    dsimp [q] at hmul
    have hden : |B| + 1 ≠ 0 := ne_of_gt (by positivity)
    have hreform : (|B| + 1) * (c0 / (8 * (|B| + 1)) * x ^ s) =
        c0 / 8 * x ^ s := by
      field_simp [hden]
    rw [hreform] at hmul
    exact (mul_le_mul_of_nonneg_right hBabs (sq_nonneg lx)).trans
      (by simpa [mul_assoc] using hmul)
  have hC0 : C0 ≤ c0 / 8 * x ^ s := by
    have hcross := mul_le_mul_of_nonneg_left hconstLarge hc0.le
    have hCabs : C0 ≤ |C0| + 1 := by linarith [le_abs_self C0]
    have hrewrite : c0 * (8 * (|C0| + 1) / c0) =
        8 * (|C0| + 1) := by field_simp [hc0.ne']
    rw [hrewrite] at hcross
    change 8 * (|C0| + 1) ≤ c0 * x ^ s at hcross
    have hdiv := (div_le_div_iff_of_pos_right
      (by norm_num : (0 : ℝ) < 8)).2 hcross
    calc
      C0 ≤ |C0| + 1 := hCabs
      _ = (8 * (|C0| + 1)) / 8 := by ring
      _ ≤ (c0 * x ^ s) / 8 := hdiv
      _ = c0 / 8 * x ^ s := by ring
  have hsigPow : x ^ sigma ≤ x ^ s :=
    Real.rpow_le_rpow_of_exponent_le hx (by dsimp [s]; exact hsigma.le)
  have hexponents :
      C0 + B * lx ^ 2 - c0 * x ^ s ≤
        Real.log 2 - c * x ^ sigma := by
    have hlog2pos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [c]
    nlinarith
  calc
    shellExceptionalRatio (shellBootstrap p omega M) M ≤
        Real.exp (C0 + B * lx ^ 2 - c0 * x ^ s) := hexpBound
    _ ≤ Real.exp (Real.log 2 - c * x ^ sigma) :=
      Real.exp_le_exp.2 hexponents
    _ = 2 * Real.exp (-c * x ^ sigma) := by
      rw [show Real.log 2 - c * x ^ sigma =
        Real.log 2 + (-c * x ^ sigma) by ring, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end

end FirstPassageLinearTransport
