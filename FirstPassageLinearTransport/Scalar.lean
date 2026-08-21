/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Bootstrap

/-!
# Scalar asymptotics for the logarithmic stage schedule
-/

namespace FirstPassageLinearTransport

open scoped Real Topology BigOperators
open Filter Asymptotics

noncomputable section

/-- A quadratic logarithmic prefactor is swallowed by every positive power
in a negative exponential. -/
theorem tendsto_exp_log_sq_sub_rpow
    {A c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    Tendsto (fun x : ℝ =>
      Real.exp (A * (Real.log x) ^ 2 - c * x ^ s))
      atTop (nhds 0) := by
  let q := c / (2 * (|A| + 1))
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop 2 hs).bound hq
  have hupper : ∀ᶠ x : ℝ in atTop,
      Real.exp (A * (Real.log x) ^ 2 - c * x ^ s) ≤
        Real.exp (-(c / 2 * x ^ s)) := by
    filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxs0 : 0 ≤ x ^ s := Real.rpow_nonneg (zero_le_one.trans hx1) s
    rw [Real.rpow_two] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)),
      Real.norm_eq_abs, abs_of_nonneg hxs0] at hx
    have hA : A ≤ |A| + 1 := by linarith [le_abs_self A]
    have hlogSq : 0 ≤ Real.log x ^ (2 : ℕ) := sq_nonneg _
    have hmain : A * Real.log x ^ (2 : ℕ) ≤ c / 2 * x ^ s := by
      have h1 := mul_le_mul_of_nonneg_right hA hlogSq
      have h2 : (|A| + 1) * (q * x ^ s) = c / 2 * x ^ s := by
        dsimp [q]
        field_simp
      calc
        A * Real.log x ^ (2 : ℕ) ≤
            (|A| + 1) * Real.log x ^ (2 : ℕ) := h1
        _ ≤ (|A| + 1) * (q * x ^ s) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        _ = c / 2 * x ^ s := h2
    apply Real.exp_le_exp.2
    norm_num at hmain ⊢
    linarith
  have htPower : Tendsto (fun x : ℝ => c / 2 * x ^ s) atTop atTop :=
    (tendsto_rpow_atTop hs).const_mul_atTop (by positivity)
  have htUpper : Tendsto (fun x : ℝ =>
      Real.exp (-(c / 2 * x ^ s))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp htPower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htUpper
  · filter_upwards with x
    exact Real.exp_pos _ |>.le
  · exact hupper

/-- Number of stopped stages used on shell `M`. -/
def stageCount (omega : ℝ) (M : ℕ) : ℕ :=
  ⌊omega * Real.log (M + 4)⌋₊

theorem stageCount_le {omega : ℝ} (homega : 0 ≤ omega) (M : ℕ) :
    (stageCount omega M : ℝ) ≤ omega * Real.log (M + 4) := by
  unfold stageCount
  apply Nat.floor_le
  have hM4 : (1 : ℝ) ≤ (M : ℝ) + 4 := by
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  exact mul_nonneg homega (Real.log_nonneg hM4)

theorem stageCount_gt_sub_one {omega : ℝ} (M : ℕ) :
    omega * Real.log (M + 4) - 1 < stageCount omega M := by
  unfold stageCount
  exact Nat.sub_one_lt_floor _


end

end FirstPassageLinearTransport
