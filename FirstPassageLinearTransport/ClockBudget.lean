/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.StretchedLogLanding

/-!
# Explicit first-passage clock budget

Geometric first-passage clock control and the exact shellwise
`6.953 * log n` bound.
-/

namespace FirstPassageLinearTransport

open scoped Real Topology BigOperators
open Filter

noncomputable section

/-- The leading geometric first-passage clock coefficient lies strictly
below the explicit `6.953` budget. -/
theorem clockLeadingLt6953 {r : ℝ}
    (hr : r < clockThreshold) :
    1 / ((1 - r) * Real.log 2) < (6953 / 1000 : ℝ) := by
  have hclock : (0 : ℝ) < 6953 / 1000 := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr1 : r < 1 := hr.trans clockThreshold_lt_one
  have hden : 0 < (1 - r) * Real.log 2 :=
    mul_pos (sub_pos.mpr hr1) hlog2
  rw [div_lt_iff₀ hden]
  unfold clockThreshold at hr
  have hclocklog : 0 < (6953 / 1000 : ℝ) * Real.log 2 :=
    mul_pos hclock hlog2
  have hbase : 1 / ((6953 / 1000 : ℝ) * Real.log 2) < 1 - r := by
    linarith
  rw [div_lt_iff₀ hclocklog] at hbase
  nlinarith

/-- The accumulated first-passage clock is eventually strictly below the
explicit `6.953 log n` budget, uniformly within each large shell. -/
theorem eventuallyShellClockLt6953
    {r eta omega : ℝ} (p : StageSetup r eta)
    (hrclock : r < clockThreshold) (homega0 : 0 < omega) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      (stageClock p (stageCount omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n := by
  let lead := 1 / ((1 - r) * Real.log 2)
  let gap := (6953 / 1000 : ℝ) - lead
  let A := omega ^ 2 * Real.logb 2 (stageK p)
  let c := gap * (Real.log 2 / 5)
  have hlead : lead < (6953 / 1000 : ℝ) := by
    dsimp [lead]
    exact clockLeadingLt6953 hrclock
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sq_nonneg omega)
      (Real.logb_nonneg (by norm_num) (stageK_one_le p))
  have hc : 0 < c := by dsimp [c]; positivity
  let q := c / (2 * (A + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hsmallReal := (isLittleO_log_rpow_rpow_atTop
    (s := (1 : ℝ)) 2 (by norm_num)).bound hq
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with M hsm hM
  intro n hn hnshell hnboot
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxpow0 : 0 ≤ x ^ (1 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hx) _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogx0 2),
    Real.norm_eq_abs, abs_of_nonneg hxpow0, Real.rpow_one] at hsm
  have herrorScalar : A * (Real.log x) ^ 2 < c * x := by
    have hmul := mul_le_mul_of_nonneg_left hsm
      (by linarith : 0 ≤ A + 1)
    dsimp [q] at hmul
    have hcoef : A ≤ A + 1 := by linarith
    have hnonneg : 0 ≤ Real.log x ^ (2 : ℕ) := sq_nonneg _
    have hleft : A * Real.log x ^ (2 : ℕ) ≤
        (A + 1) * Real.log x ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hcoef hnonneg
    have hA1ne : A + 1 ≠ 0 := ne_of_gt (by linarith)
    have hhalf : (A + 1) * (c / (2 * (A + 1)) * x) =
        c / 2 * x := by
      field_simp [hA1ne]
    rw [hhalf] at hmul
    have hmid : A * Real.log x ^ (2 : ℕ) ≤ c / 2 * x :=
      hleft.trans (by simpa [mul_assoc] using hmul)
    have hcx : 0 < c * x := mul_pos hc (zero_lt_one.trans_le hx)
    exact hmid.trans_lt (by
      calc
        c / 2 * x = (c * x) / 2 := by ring
        _ < c * x := div_lt_self hcx (by norm_num))
  have hRle := stageCount_le homega0.le M
  have hR2 : (R : ℝ) ^ 2 ≤ (omega * Real.log x) ^ 2 := by
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith
  have hlogbK0 : 0 ≤ Real.logb 2 (stageK p) :=
    Real.logb_nonneg (by norm_num) (stageK_one_le p)
  have herror : (R : ℝ) ^ 2 * Real.logb 2 (stageK p) <
      gap * (Real.log 2 / 5 * x) := by
    have hmul := mul_le_mul_of_nonneg_right hR2 hlogbK0
    have hform : (omega * Real.log x) ^ 2 *
        Real.logb 2 (stageK p) = A * (Real.log x) ^ 2 := by
      dsimp [A]
      ring
    rw [hform] at hmul
    exact hmul.trans_lt (by
      dsimp [c] at herrorScalar
      nlinarith)
  have hlogLower : Real.log 2 / 5 * x ≤ Real.log n := by
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
  have hclock := stageClock_le_logb p hn hnboot
  have hgeom := clockGeomLeInvOneSub p.r_pos.le p.r_lt_one R
  have hlogbN0 : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  have hleading : clockGeom r R * Real.logb 2 n ≤
      lead * Real.log n := by
    have hmul := mul_le_mul_of_nonneg_right hgeom hlogbN0
    have hlog2ne := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have heq : (1 - r)⁻¹ * Real.logb 2 n = lead * Real.log n := by
      dsimp [lead]
      rw [Real.logb]
      field_simp [hlog2ne]
    exact hmul.trans_eq heq
  have hlogn0 : 0 < Real.log n := by
    have hn2 : 2 ≤ n := by
      have hpow2 : 2 ≤ 2 ^ M := by
        have hp : 2 ^ 1 ≤ 2 ^ M :=
          Nat.pow_le_pow_right (by norm_num) hM
        simpa using hp
      exact hpow2.trans (mem_dyadicShell.mp hnshell).1
    exact Real.log_pos (by exact_mod_cast hn2)
  calc
    (stageClock p R n : ℝ) ≤
        clockGeom r R * Real.logb 2 n +
          (R : ℝ) ^ 2 * Real.logb 2 (stageK p) := hclock
    _ < lead * Real.log n + gap * Real.log n := by
      apply add_lt_add_of_le_of_lt hleading
      exact herror.trans_le (mul_le_mul_of_nonneg_left hlogLower hgap.le)
    _ = (6953 / 1000 : ℝ) * Real.log n := by
      dsimp [gap]
      ring

end

end FirstPassageLinearTransport
