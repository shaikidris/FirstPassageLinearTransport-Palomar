/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Constants

/-! # Strict headline parameter selection -/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- Largest stage contraction compatible with the explicit `6.953` clock. -/
def clockThreshold : ℝ :=
  1 - 1 / ((6953 / 1000 : ℝ) * Real.log 2)

/-- Strict scalar parameters simultaneously satisfying density, descent, and
clock compatibility for a fixed stretched-log exponent. -/
structure HeadlineScalars (delta : ℝ) where
  r : ℝ
  chi : ℝ
  omega : ℝ
  eta : ℝ
  a0_lt_r : a0 < r
  r_lt_clock : r < clockThreshold
  r_lt_one : r < 1
  chi_pos : 0 < chi
  chi_lt_r : chi < r
  chi_le_one : chi ≤ 1
  omega_pos : 0 < omega
  density_compat : omega * Real.log (1 / chi) < 1
  descent_compat : delta < omega * Real.log (1 / r)
  eta_pos : 0 < eta
  eta_gap : eta < r - a0

/-- Headline parameters carrying an explicit density margin.  The additional
field is exactly what is needed to retain a prescribed stretched-exponential
exceptional-count power `sigma`. -/
structure QuantitativeHeadlineScalars (delta sigma : ℝ)
    extends HeadlineScalars delta where
  density_margin :
    omega * Real.log (1 / chi) < 1 - sigma

theorem clockThreshold_lt_one : clockThreshold < 1 := by
  unfold clockThreshold
  have : 0 < 1 / ((6953 / 1000 : ℝ) * Real.log 2) := by positivity
  linarith

theorem clockThreshold_pos : 0 < clockThreshold :=
  a0_pos.trans a0_lt_clockThreshold

/-- Explicit strict parameter choice.  Taking `chi = r^(1/q)` makes the
compatibility ratio exactly `q`, avoiding a nonconstructive limit argument. -/
theorem exists_headlineScalars {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    Nonempty (HeadlineScalars delta) := by
  let r := (a0 + clockThreshold) / 2
  let q := (delta + 1) / 2
  let chi := r ^ (1 / q)
  let omega := (delta + q) / (2 * Real.log (1 / r))
  let eta := (r - a0) / 2
  have hr0 : 0 < r := by
    dsimp [r]
    linarith [a0_pos, clockThreshold_pos]
  have ha0r : a0 < r := by
    have hgap : a0 < clockThreshold := by
      simpa [clockThreshold] using a0_lt_clockThreshold
    dsimp [r]
    linarith
  have hrclock : r < clockThreshold := by
    have hgap : a0 < clockThreshold := by
      simpa [clockThreshold] using a0_lt_clockThreshold
    dsimp [r]
    linarith
  have hr1 : r < 1 := hrclock.trans clockThreshold_lt_one
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hdq : delta < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have honeq : 1 < 1 / q := by
    rw [one_lt_div hq0]
    exact hq1
  have hchi0 : 0 < chi := by
    dsimp [chi]
    exact Real.rpow_pos_of_pos hr0 _
  have hchir : chi < r := by
    dsimp [chi]
    have := Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 honeq
    simpa [Real.rpow_one] using this
  have hchi1 : chi ≤ 1 := hchir.le.trans hr1.le
  have hlogr : 0 < Real.log (1 / r) := by
    exact Real.log_pos (by
      rw [one_div, one_lt_inv₀ hr0]
      exact hr1)
  have homega0 : 0 < omega := by
    dsimp [omega]
    positivity
  have hloginvr : Real.log (1 / r) = -Real.log r := by
    rw [one_div, Real.log_inv]
  have hlogchi : Real.log (1 / chi) = (1 / q) * Real.log (1 / r) := by
    dsimp [chi]
    rw [one_div, Real.log_inv, Real.log_rpow hr0, hloginvr]
    ring
  have hdescent : delta < omega * Real.log (1 / r) := by
    have heq : omega * Real.log (1 / r) = (delta + q) / 2 := by
      dsimp [omega]
      field_simp [hlogr.ne']
    rw [heq]
    linarith
  have hdensity : omega * Real.log (1 / chi) < 1 := by
    rw [hlogchi]
    have hqne : q ≠ 0 := hq0.ne'
    have hlogne : Real.log (1 / r) ≠ 0 := hlogr.ne'
    have heq : omega * ((1 / q) * Real.log (1 / r)) =
        (delta + q) / (2 * q) := by
      dsimp [omega]
      field_simp [hqne, hlogne]
    rw [heq]
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * q)]
    linarith
  have heta0 : 0 < eta := by dsimp [eta]; linarith
  have hetagap : eta < r - a0 := by dsimp [eta]; linarith
  exact ⟨{
    r := r
    chi := chi
    omega := omega
    eta := eta
    a0_lt_r := ha0r
    r_lt_clock := hrclock
    r_lt_one := hr1
    chi_pos := hchi0
    chi_lt_r := hchir
    chi_le_one := hchi1
    omega_pos := homega0
    density_compat := hdensity
    descent_compat := hdescent
    eta_pos := heta0
    eta_gap := hetagap }⟩

/-- Explicit parameter choice retaining every strict quantitative margin
`sigma < 1 - delta`. -/
theorem exists_quantitativeHeadlineScalars {delta sigma : ℝ}
    (hdelta0 : 0 < delta)
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 - delta) :
    Nonempty (QuantitativeHeadlineScalars delta sigma) := by
  let r := (a0 + clockThreshold) / 2
  let q := (delta / (1 - sigma) + 1) / 2
  let theta := (delta + q * (1 - sigma)) / 2
  let chi := r ^ (1 / q)
  let omega := theta / Real.log (1 / r)
  let eta := (r - a0) / 2
  have hsigma1 : sigma < 1 := by linarith
  have honeSigma : 0 < 1 - sigma := sub_pos.mpr hsigma1
  have hdeltaGap : delta < 1 - sigma := by linarith
  have hratio0 : 0 < delta / (1 - sigma) :=
    div_pos hdelta0 honeSigma
  have hratio1 : delta / (1 - sigma) < 1 := by
    rw [div_lt_one honeSigma]
    exact hdeltaGap
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hratioq : delta / (1 - sigma) < q := by
    dsimp [q]
    linarith
  have hdeltaq : delta < q * (1 - sigma) := by
    have := mul_lt_mul_of_pos_right hratioq honeSigma
    field_simp [honeSigma.ne'] at this
    simpa [mul_comm] using this
  have htheta0 : 0 < theta := by dsimp [theta]; linarith
  have hdeltatheta : delta < theta := by dsimp [theta]; linarith
  have hthetaq : theta < q * (1 - sigma) := by
    dsimp [theta]
    linarith
  have hr0 : 0 < r := by
    dsimp [r]
    linarith [a0_pos, clockThreshold_pos]
  have ha0r : a0 < r := by
    have hgap : a0 < clockThreshold := by
      simpa [clockThreshold] using a0_lt_clockThreshold
    dsimp [r]
    linarith
  have hrclock : r < clockThreshold := by
    have hgap : a0 < clockThreshold := by
      simpa [clockThreshold] using a0_lt_clockThreshold
    dsimp [r]
    linarith
  have hr1 : r < 1 := hrclock.trans clockThreshold_lt_one
  have honeq : 1 < 1 / q := by
    rw [one_lt_div hq0]
    exact hq1
  have hchi0 : 0 < chi := by
    dsimp [chi]
    exact Real.rpow_pos_of_pos hr0 _
  have hchir : chi < r := by
    dsimp [chi]
    have := Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 honeq
    simpa [Real.rpow_one] using this
  have hchi1 : chi ≤ 1 := hchir.le.trans hr1.le
  have hlogr : 0 < Real.log (1 / r) := by
    exact Real.log_pos (by
      rw [one_div, one_lt_inv₀ hr0]
      exact hr1)
  have homega0 : 0 < omega := by
    dsimp [omega]
    exact div_pos htheta0 hlogr
  have hloginvr : Real.log (1 / r) = -Real.log r := by
    rw [one_div, Real.log_inv]
  have hlogchi : Real.log (1 / chi) = (1 / q) * Real.log (1 / r) := by
    dsimp [chi]
    rw [one_div, Real.log_inv, Real.log_rpow hr0, hloginvr]
    ring
  have hdescent : delta < omega * Real.log (1 / r) := by
    have heq : omega * Real.log (1 / r) = theta := by
      dsimp [omega]
      field_simp [hlogr.ne']
    rw [heq]
    exact hdeltatheta
  have hdensityMargin : omega * Real.log (1 / chi) < 1 - sigma := by
    rw [hlogchi]
    have hqne : q ≠ 0 := hq0.ne'
    have hlogne : Real.log (1 / r) ≠ 0 := hlogr.ne'
    have heq : omega * ((1 / q) * Real.log (1 / r)) = theta / q := by
      dsimp [omega]
      field_simp [hqne, hlogne]
    rw [heq]
    rw [div_lt_iff₀ hq0]
    simpa [mul_comm] using hthetaq
  have hdensity : omega * Real.log (1 / chi) < 1 :=
    hdensityMargin.trans (by linarith)
  have heta0 : 0 < eta := by dsimp [eta]; linarith
  have hetagap : eta < r - a0 := by dsimp [eta]; linarith
  exact ⟨{
    r := r
    chi := chi
    omega := omega
    eta := eta
    a0_lt_r := ha0r
    r_lt_clock := hrclock
    r_lt_one := hr1
    chi_pos := hchi0
    chi_lt_r := hchir
    chi_le_one := hchi1
    omega_pos := homega0
    density_compat := hdensity
    descent_compat := hdescent
    eta_pos := heta0
    eta_gap := hetagap
    density_margin := hdensityMargin }⟩

end

end FirstPassageLinearTransport
