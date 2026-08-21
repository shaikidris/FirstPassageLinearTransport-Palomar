/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.AdjustableEntropyRate
import FirstPassageLinearTransport.Constants

/-!
# Endpoint parameters for fixed-polylogarithmic descent

This module isolates the scalar endpoint optimization behind the paper's
constant `A_FP`.  It contains no Collatz-set or checkpoint-congestion input.
The main result selects an admissible adjustable low-rank barrier and a
strictly positive exceptional-count exponent from every
`A > fixedPolylogCriticalExponent`.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- The endpoint displacement obtained as the envelope tolerance approaches
the full drift gap and the adjustable barrier fraction approaches one. -/
def firstPassageEndpointDisplacement : ℝ := driftGap / logTwoThree

/-- The entropy rate available at the nonattained low-rank endpoint. -/
def firstPassageEndpointRate : ℝ :=
  binaryBarrierRate firstPassageEndpointDisplacement

/-- Exact critical fixed-polylogarithmic exponent. -/
def fixedPolylogCriticalExponent : ℝ :=
  Real.log 2 / firstPassageEndpointRate

/-- Base-three logarithm of two. -/
def logThreeTwo : ℝ := Real.log 2 / Real.log 3

/-- Binary entropy in base two, expressed through Mathlib's natural-log
binary entropy. -/
def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

theorem driftGap_lt_a0 : driftGap < a0 := by
  have haHalf : (1 / 2 : ℝ) < a0 := by
    unfold a0
    linarith [logTwoThree_one_lt]
  unfold driftGap
  linarith

theorem firstPassageEndpointDisplacement_pos :
    0 < firstPassageEndpointDisplacement := by
  unfold firstPassageEndpointDisplacement
  exact div_pos driftGap_pos logTwoThree_pos

theorem firstPassageEndpointDisplacement_lt_half :
    firstPassageEndpointDisplacement < 1 / 2 := by
  unfold firstPassageEndpointDisplacement
  rw [div_lt_iff₀ logTwoThree_pos]
  have htwo : logTwoThree = 2 * a0 := by
    unfold a0
    ring
  rw [htwo]
  linarith [driftGap_lt_a0]

theorem endpoint_probability_eq_logThreeTwo :
    1 / 2 + firstPassageEndpointDisplacement = logThreeTwo := by
  unfold firstPassageEndpointDisplacement driftGap a0 logTwoThree logThreeTwo
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog2, hlog3]
  ring

theorem firstPassageEndpointRate_pos : 0 < firstPassageEndpointRate := by
  unfold firstPassageEndpointRate binaryBarrierRate
  apply sub_pos.mpr
  rw [Real.binEntropy_lt_log_two]
  have hdisp := firstPassageEndpointDisplacement_pos
  intro hEq
  linarith

theorem firstPassageEndpointRate_lt_logTwo :
    firstPassageEndpointRate < Real.log 2 := by
  unfold firstPassageEndpointRate binaryBarrierRate
  have hp0 : 0 < 1 / 2 + firstPassageEndpointDisplacement := by
    linarith [firstPassageEndpointDisplacement_pos]
  have hp1 : 1 / 2 + firstPassageEndpointDisplacement < 1 := by
    linarith [firstPassageEndpointDisplacement_lt_half]
  linarith [Real.binEntropy_pos hp0 hp1]

theorem fixedPolylogCriticalExponent_gt_one :
    1 < fixedPolylogCriticalExponent := by
  unfold fixedPolylogCriticalExponent
  rw [lt_div_iff₀ firstPassageEndpointRate_pos]
  simpa using firstPassageEndpointRate_lt_logTwo

/-- Exact identification with the paper's
`1 / (1 - H₂(log₃ 2))`. -/
theorem fixedPolylogCriticalExponent_eq_entropy :
    fixedPolylogCriticalExponent =
      1 / (1 - binaryEntropyBaseTwo logThreeTwo) := by
  rw [fixedPolylogCriticalExponent, firstPassageEndpointRate,
    binaryBarrierRate, endpoint_probability_eq_logThreeTwo]
  unfold binaryEntropyBaseTwo
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hrate : Real.log 2 - Real.binEntropy logThreeTwo ≠ 0 := by
    have hpos := firstPassageEndpointRate_pos
    rw [firstPassageEndpointRate, binaryBarrierRate] at hpos
    change 0 < Real.log 2 - Real.binEntropy
      (1 / 2 + firstPassageEndpointDisplacement) at hpos
    rw [endpoint_probability_eq_logThreeTwo] at hpos
    exact ne_of_gt hpos
  field_simp [hlog2, hrate]

theorem continuous_binaryBarrierRate : Continuous binaryBarrierRate := by
  unfold binaryBarrierRate
  fun_prop

/-- A one-parameter admissible approach to the low-rank endpoint. -/
def endpointLambda (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 2)

/-- The matching envelope tolerance, strictly below the full drift gap. -/
def endpointTolerance (n : ℕ) : ℝ :=
  driftGap * endpointLambda n

theorem tendsto_endpointLambda :
    Tendsto endpointLambda atTop (nhds 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hden
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (nhds 1)
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hinv)

theorem tendsto_endpointTolerance :
    Tendsto endpointTolerance atTop (nhds driftGap) := by
  simpa [endpointTolerance] using
    tendsto_const_nhds.mul tendsto_endpointLambda

theorem tendsto_endpointEntropyRate :
    Tendsto
      (fun n : ℕ =>
        adjustableEntropyRate (endpointLambda n) (endpointTolerance n))
      atTop (nhds firstPassageEndpointRate) := by
  have hdisp : Tendsto
      (fun n : ℕ => adjustableBarrierDisplacement
        (endpointLambda n) (endpointTolerance n))
      atTop (nhds firstPassageEndpointDisplacement) := by
    have hmul := tendsto_endpointLambda.mul tendsto_endpointTolerance
    simpa [adjustableBarrierDisplacement, firstPassageEndpointDisplacement]
      using hmul.div_const logTwoThree
  unfold adjustableEntropyRate firstPassageEndpointRate
  exact continuous_binaryBarrierRate.continuousAt.tendsto.comp hdisp

theorem endpointLambda_pos (n : ℕ) : 0 < endpointLambda n := by
  unfold endpointLambda
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hden : (1 : ℝ) < (n : ℝ) + 2 := by linarith
  have hinv : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).2 hden
  linarith

theorem endpointLambda_lt_one (n : ℕ) : endpointLambda n < 1 := by
  unfold endpointLambda
  have hinv : 0 < 1 / ((n : ℝ) + 2) := by positivity
  linarith

theorem endpointTolerance_pos (n : ℕ) : 0 < endpointTolerance n := by
  unfold endpointTolerance
  exact mul_pos driftGap_pos (endpointLambda_pos n)

theorem endpointTolerance_lt_driftGap (n : ℕ) :
    endpointTolerance n < driftGap := by
  unfold endpointTolerance
  nlinarith [driftGap_pos, endpointLambda_pos n, endpointLambda_lt_one n]

/-- Critical shortcut-clock coefficient in the natural-logarithm
normalization. -/
def fixedPolylogClockCritical : ℝ :=
  1 / (driftGap * Real.log 2)

theorem fixedPolylogClockCritical_eq_paper :
    fixedPolylogClockCritical = 2 / Real.log (4 / 3) := by
  exact inv_drift_clock_eq

theorem fixedPolylogClockCritical_pos : 0 < fixedPolylogClockCritical := by
  unfold fixedPolylogClockCritical
  exact one_div_pos.mpr
    (mul_pos driftGap_pos (Real.log_pos (by norm_num)))

end

end FirstPassageLinearTransport
