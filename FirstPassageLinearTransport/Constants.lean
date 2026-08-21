/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum.BigOperators
import FirstPassageLinearTransport.Scalar

/-! # Exact clock constants -/

namespace FirstPassageLinearTransport

open scoped Real BigOperators

noncomputable section

/-- Explicit rational lower bound for `log (4/3)`. -/
theorem log_four_thirds_gt_296_div_1029 :
    (296 / 1029 : ℝ) < Real.log (4 / 3) := by
  let f : ℕ → ℝ := fun k =>
    2 * (1 / (2 * k + 1 : ℝ)) * (1 / 7 : ℝ) ^ (2 * k + 1)
  have hsum : HasSum f (Real.log (1 + (3 : ℝ)⁻¹)) := by
    simpa [f, show (2 * (3 : ℝ) + 1) = 7 by norm_num] using
      (Real.hasSum_log_one_add_inv (a := (3 : ℝ)) (by norm_num))
  have hnonneg : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have hpartial : ∑ k ∈ Finset.range 3, f k ≤ ∑' k, f k :=
    hsum.summable.sum_le_tsum (Finset.range 3) (fun k _ => hnonneg k)
  rw [hsum.tsum_eq] at hpartial
  have hlog : Real.log (1 + (3 : ℝ)⁻¹) = Real.log (4 / 3) := by
    congr 1
    norm_num
  rw [hlog] at hpartial
  norm_num [f] at hpartial ⊢
  exact lt_of_lt_of_le (by norm_num) hpartial

theorem inv_drift_clock_eq :
    1 / ((1 - a0) * Real.log 2) = 2 / Real.log (4 / 3) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog3 : Real.log 3 = logTwoThree * Real.log 2 := by
    unfold logTwoThree
    field_simp
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have h43 : Real.log (4 / 3) = 2 * ((1 - a0) * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4, hlog3]
    unfold a0
    ring
  rw [h43]
  have hA : (1 - a0) * Real.log 2 ≠ 0 :=
    ne_of_gt (mul_pos (sub_pos.mpr a0_lt_one) (Real.log_pos (by norm_num)))
  field_simp [hA]

theorem inv_drift_clock_lt_6953 :
    1 / ((1 - a0) * Real.log 2) < (6953 / 1000 : ℝ) := by
  rw [inv_drift_clock_eq]
  have hlog := log_four_thirds_gt_296_div_1029
  have hlogPos : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hlogPos).2
  have hrat : (2 : ℝ) < (6953 / 1000 : ℝ) * (296 / 1029) := by
    norm_num
  exact hrat.trans (mul_lt_mul_of_pos_left hlog (by norm_num))

/-- The clock-compatible interval for the contraction parameter is nonempty. -/
theorem a0_lt_clockThreshold :
    a0 < 1 - 1 / ((6953 / 1000 : ℝ) * Real.log 2) := by
  have hden : 0 < (6953 / 1000 : ℝ) * Real.log 2 := by positivity
  have hdrift : 0 < (1 - a0) * Real.log 2 := by
    exact mul_pos (sub_pos.mpr a0_lt_one) (Real.log_pos (by norm_num))
  have h := inv_drift_clock_lt_6953
  rw [div_lt_iff₀ hdrift] at h
  have hinv : 1 / ((6953 / 1000 : ℝ) * Real.log 2) < 1 - a0 := by
    apply (div_lt_iff₀ hden).2
    convert h using 1
    all_goals ring
  linarith

end

end FirstPassageLinearTransport
