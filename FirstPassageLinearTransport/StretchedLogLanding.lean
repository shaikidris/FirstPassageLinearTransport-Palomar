/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.BootstrapSchedule

/-!
# Stretched-logarithmic landing

Power-versus-logarithm asymptotics for the stopped-stage schedule and the
uniform shellwise landing estimate at every fixed exponent below one.
-/

namespace FirstPassageLinearTransport

open scoped Real Topology BigOperators
open Filter

noncomputable section

/-- A logarithmic startup term plus a strictly smaller power is eventually
dominated by the target power. -/
theorem eventuallyLogAddRpowLe
    {A C c a delta : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 < c)
    (hdelta : delta < 1) (ha : delta < a) :
    ∀ᶠ x : ℝ in atTop,
      A * Real.log x + C * x ^ (1 - a) ≤
        c * x ^ (1 - delta) := by
  have hs : 0 < 1 - delta := sub_pos.mpr hdelta
  let q1 := c / (2 * (A + 1))
  let q2 := c / (2 * (C + 1))
  have hq1 : 0 < q1 := by dsimp [q1]; positivity
  have hq2 : 0 < q2 := by dsimp [q2]; positivity
  have hlog := (isLittleO_log_rpow_atTop hs).bound hq1
  have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).eventually
    (Iio_mem_nhds hq2)
  filter_upwards [hlog, hpow, eventually_ge_atTop (1 : ℝ)] with x hxlog hxpow hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have htarget0 : 0 ≤ x ^ (1 - delta) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0,
    Real.norm_eq_abs, abs_of_nonneg htarget0] at hxlog
  have hfirst : A * Real.log x ≤ c / 2 * x ^ (1 - delta) := by
    have hmul := mul_le_mul_of_nonneg_left hxlog hA
    dsimp [q1] at hmul
    have hfrac : A / (A + 1) ≤ 1 := by
      apply (div_le_one (by linarith)).2
      linarith
    have hcoef : A * (c / (2 * (A + 1))) ≤ c / 2 := by
      rw [show A * (c / (2 * (A + 1))) =
        (c / 2) * (A / (A + 1)) by field_simp]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (div_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 2))
    calc
      A * Real.log x ≤ A * (q1 * x ^ (1 - delta)) := hmul
      _ = (A * q1) * x ^ (1 - delta) := by ring
      _ ≤ (c / 2) * x ^ (1 - delta) :=
        mul_le_mul_of_nonneg_right hcoef htarget0
  have hxpow0 : 0 ≤ x ^ (delta - a) := Real.rpow_nonneg hx0.le _
  have hpowRewrite : x ^ (-(a - delta)) = x ^ (delta - a) := by
    congr 1
    ring
  rw [hpowRewrite] at hxpow
  have hsecond : C * x ^ (1 - a) ≤ c / 2 * x ^ (1 - delta) := by
    have hid : x ^ (1 - a) = x ^ (1 - delta) * x ^ (delta - a) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_left hxpow.le hC
    have hfrac : C / (C + 1) ≤ 1 := by
      apply (div_le_one (by linarith)).2
      linarith
    have hcoef : C * q2 ≤ c / 2 := by
      dsimp [q2]
      rw [show C * (c / (2 * (C + 1))) =
        (c / 2) * (C / (C + 1)) by field_simp]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (div_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 2))
    calc
      C * (x ^ (1 - delta) * x ^ (delta - a)) =
          x ^ (1 - delta) * (C * x ^ (delta - a)) := by ring
      _ ≤ x ^ (1 - delta) * (C * q2) :=
        mul_le_mul_of_nonneg_left hmul htarget0
      _ ≤ x ^ (1 - delta) * (c / 2) :=
        mul_le_mul_of_nonneg_left hcoef htarget0
      _ = c / 2 * x ^ (1 - delta) := by ring
  nlinarith

/-- Descent exponent induced by `omega log M` stages of contraction `r`. -/
def descentAlpha (omega r : ℝ) : ℝ :=
  omega * Real.log (1 / r)

/-- Flooring the logarithmic stage count costs at most one factor of `r⁻¹`. -/
theorem stageCountRpowUpper
    {r omega : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℕ) :
    r ^ (stageCount omega M) ≤
      r⁻¹ * ((M : ℝ) + 4) ^ (-descentAlpha omega r) := by
  have hx : (0 : ℝ) < (M : ℝ) + 4 := by positivity
  have hfloor := stageCount_gt_sub_one (omega := omega) M
  have hp : r ^ (stageCount omega M : ℝ) ≤
      r ^ (omega * Real.log ((M : ℝ) + 4) - 1) :=
    (Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 hfloor).le
  rw [Real.rpow_natCast] at hp
  calc
    r ^ stageCount omega M ≤
        r ^ (omega * Real.log ((M : ℝ) + 4) - 1) := hp
    _ = r⁻¹ * ((M : ℝ) + 4) ^ (-descentAlpha omega r) := by
      rw [Real.rpow_sub hr0, Real.rpow_one,
        rpowLogScheduleIdentity hr0 hx]
      unfold descentAlpha densityGamma
      ring

/-- Uniform shellwise stretched-log landing for the logarithmic stopped-stage
schedule. -/
theorem eventuallyShellLanding
    {r eta omega delta : ℝ} (p : StageSetup r eta)
    (homega0 : 0 < omega) (hdelta1 : delta < 1)
    (hdescent : delta < descentAlpha omega r) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      (stageOrbit p (stageCount omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta)) := by
  let a := descentAlpha omega r
  let A := omega * Real.log (stageK p)
  let C := r⁻¹ * Real.log 2
  let c := (Real.log 2 / 5) ^ (1 - delta)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg homega0.le
      (Real.log_nonneg (stageK_one_le p))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (inv_nonneg.mpr p.r_pos.le)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hc : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hscalarReal := eventuallyLogAddRpowLe hA hC hc
    hdelta1 hdescent
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have hscalar : ∀ᶠ M : ℕ in atTop,
      A * Real.log ((M : ℝ) + 4) +
          C * ((M : ℝ) + 4) ^ (1 - a) ≤
        c * ((M : ℝ) + 4) ^ (1 - delta) :=
    hxT.eventually hscalarReal
  filter_upwards [hscalar, eventually_ge_atTop (1 : ℕ)] with M hsc hM
  intro n hn hnshell hnboot
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 0 < x := by dsimp [x]; positivity
  have hstage := stageOrbit_le_power p hn hnboot
  have hRle := stageCount_le homega0.le M
  have hlogK0 : 0 ≤ Real.log (stageK p) :=
    Real.log_nonneg (stageK_one_le p)
  have hstartup : (R : ℝ) * Real.log (stageK p) ≤
      A * Real.log x := by
    dsimp [R, A, x]
    convert mul_le_mul_of_nonneg_right hRle hlogK0 using 1
    all_goals ring
  have hrpow := stageCountRpowUpper (omega := omega)
    p.r_pos p.r_lt_one M
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hnupper : (n : ℝ) < (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast (mem_dyadicShell.mp hnshell).2
  have hlognUpper : Real.log n ≤ ((M : ℝ) + 1) * Real.log 2 := by
    have h := Real.log_le_log (by exact_mod_cast hn) hnupper.le
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hMx : (M : ℝ) + 1 ≤ x := by dsimp [x]; linarith
  have htail : (r ^ R : ℝ) * Real.log n ≤
      C * x ^ (1 - a) := by
    have hrhs0 : 0 ≤ r⁻¹ * ((M : ℝ) + 4) ^
        (-descentAlpha omega r) :=
      mul_nonneg (inv_nonneg.mpr p.r_pos.le)
        (Real.rpow_nonneg (by positivity) _)
    have h1 := mul_le_mul hrpow hlognUpper hlogn0 hrhs0
    have h2 : r⁻¹ * x ^ (-a) * (((M : ℝ) + 1) * Real.log 2) ≤
        r⁻¹ * Real.log 2 * x ^ (1 - a) := by
      have hxm := mul_le_mul_of_nonneg_right hMx
        (mul_nonneg (inv_nonneg.mpr p.r_pos.le)
          (Real.rpow_nonneg hx.le (-a)))
      have hid : r⁻¹ * x ^ (-a) * (x * Real.log 2) =
          r⁻¹ * Real.log 2 * x ^ (1 - a) := by
        rw [show (1 : ℝ) - a = 1 + (-a) by ring,
          Real.rpow_add hx, Real.rpow_one]
        ring
      calc
        r⁻¹ * x ^ (-a) * (((M : ℝ) + 1) * Real.log 2)
            = (((M : ℝ) + 1) * (r⁻¹ * x ^ (-a))) *
                Real.log 2 := by ring
        _ ≤ (x * (r⁻¹ * x ^ (-a))) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hxm
            (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
        _ = r⁻¹ * x ^ (-a) * (x * Real.log 2) := by ring
        _ = r⁻¹ * Real.log 2 * x ^ (1 - a) := hid
    exact h1.trans h2
  have hexponent : (R : ℝ) * Real.log (stageK p) +
      (r ^ R : ℝ) * Real.log n ≤
        c * x ^ (1 - delta) := by
    dsimp [A, C, a, c, x] at hsc ⊢
    exact (add_le_add hstartup htail).trans hsc
  have htargetBase : Real.log 2 / 5 * x ≤ Real.log n := by
    have hfrac : x / 5 ≤ (M : ℝ) := by
      dsimp [x]
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hlowerNat : (2 : ℕ) ^ M ≤ n :=
      (mem_dyadicShell.mp hnshell).1
    have hlower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
      have hlowerCast : (2 : ℝ) ^ M ≤ (n : ℝ) := by
        exact_mod_cast hlowerNat
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
        hlowerCast
      rw [Real.log_pow] at h
      exact h
    nlinarith [mul_le_mul_of_nonneg_right hfrac
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  have htarget : c * x ^ (1 - delta) ≤
      (Real.log n) ^ (1 - delta) := by
    have hpow := Real.rpow_le_rpow
      (by positivity : (0 : ℝ) ≤ Real.log 2 / 5 * x)
      htargetBase (sub_pos.mpr hdelta1).le
    have hmul : (Real.log 2 / 5 * x) ^ (1 - delta) =
        c * x ^ (1 - delta) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ Real.log 2 / 5) hx.le]
    rw [← hmul]
    exact hpow
  have hprod : stageK p ^ R * (n : ℝ) ^ (r ^ R) =
      Real.exp ((R : ℝ) * Real.log (stageK p) +
        (r ^ R : ℝ) * Real.log n) := by
    rw [Real.exp_add, Real.rpow_def_of_pos (by exact_mod_cast hn)]
    congr 1
    · rw [← Real.exp_log (pow_pos (stageK_pos p) R), Real.log_pow]
    · congr 1
      ring
  calc
    (stageOrbit p R n : ℝ) ≤
        stageK p ^ R * (n : ℝ) ^ (r ^ R) := hstage
    _ = Real.exp ((R : ℝ) * Real.log (stageK p) +
        (r ^ R : ℝ) * Real.log n) := hprod
    _ ≤ Real.exp (c * x ^ (1 - delta)) :=
      Real.exp_le_exp.2 hexponent
    _ ≤ Real.exp ((Real.log n) ^ (1 - delta)) :=
      Real.exp_le_exp.2 htarget

end

end FirstPassageLinearTransport
