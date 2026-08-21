/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Canonical polylogarithmic terminal schedule

Only the terminal-rank schedule used by the public timeout theorem lives in
this module.  Historical high/low switch schedules are packaged separately.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Low-rank terminal schedule for target exponent `A`. -/
def polylogTerminalRank (A : ℝ) (M : ℕ) : ℕ :=
  ⌈A * Real.logb 2 ((M : ℝ) + 2)⌉₊

theorem polylogTerminalRank_lower (A : ℝ) (M : ℕ) :
    A * Real.logb 2 ((M : ℝ) + 2) ≤
      (polylogTerminalRank A M : ℝ) := by
  exact Nat.le_ceil _

theorem polylogTerminalRank_lt_add_one
    {A : ℝ} (hA : 0 ≤ A) (M : ℕ) :
    (polylogTerminalRank A M : ℝ) <
      A * Real.logb 2 ((M : ℝ) + 2) + 1 := by
  apply Nat.ceil_lt_add_one
  have hx : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    nlinarith [show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M]
  exact mul_nonneg hA (Real.logb_nonneg (by norm_num) hx)

/-- The integer terminal rank corresponds to the manuscript's fixed
polylogarithmic target, with only the factor two introduced by the ceiling. -/
theorem two_pow_polylogTerminalRank_lt
    {A : ℝ} (hA : 0 ≤ A) (M : ℕ) :
    ((2 ^ polylogTerminalRank A M : ℕ) : ℝ) <
      2 * (((M : ℝ) + 2) ^ A) := by
  have hx : 0 < (M : ℝ) + 2 := by positivity
  have hExp := polylogTerminalRank_lt_add_one hA M
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  calc
    (2 : ℝ) ^ (polylogTerminalRank A M : ℝ) <
        (2 : ℝ) ^
          (A * Real.logb 2 ((M : ℝ) + 2) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hExp
    _ = 2 * (((M : ℝ) + 2) ^ A) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      rw [show A * Real.logb 2 ((M : ℝ) + 2) =
          Real.logb 2 ((M : ℝ) + 2) * A by ring]
      rw [Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hx]
      ring

/-- Every positive logarithmic terminal schedule diverges with the source
shell rank. -/
theorem tendsto_polylogTerminalRank_atTop
    {A : ℝ} (hA : 0 < A) :
    Tendsto (polylogTerminalRank A) atTop atTop := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 2))
      atTop atTop := Real.tendsto_log_atTop.comp hxT
  have hcoef : 0 < A / Real.log 2 :=
    div_pos hA (Real.log_pos (by norm_num))
  have hreal : Tendsto
      (fun M : ℕ => A * Real.logb 2 ((M : ℝ) + 2)) atTop atTop := by
    have hmul := hlogT.const_mul_atTop hcoef
    simpa [Real.logb, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hmul
  rw [tendsto_atTop]
  intro N
  have hN := (tendsto_atTop.1 hreal) (N : ℝ)
  filter_upwards [hN] with M hN
  have hceil := polylogTerminalRank_lower A M
  have hcast : (N : ℝ) ≤ (polylogTerminalRank A M : ℝ) :=
    hN.trans hceil
  exact_mod_cast hcast

/-- A positive target exponent gives a nonzero terminal rank on every shell. -/
theorem polylogTerminalRank_pos
    {A : ℝ} (hA : 0 < A) (M : ℕ) :
    0 < polylogTerminalRank A M := by
  apply Nat.ceil_pos.mpr
  apply mul_pos hA
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  linarith

end

end FirstPassageLinearTransport
