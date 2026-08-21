/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Basic

/-!
# Shell-to-logarithm target conversion

Shared scalar conversions from a dyadic-shell clock and terminal target to
the natural-logarithm normalization used by the public theorems.  These
lemmas are independent of any particular recertification execution.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Explicit natural-logarithm normalization constant for the fixed
polylogarithmic landing target. -/
def fixedPolylogTargetConstant (A : ℝ) : ℝ :=
  2 * (1 / Real.log 2 + 2) ^ A


/-- The shell clock is no larger than the corresponding natural-logarithm
clock for a nonnegative clock coefficient. -/
theorem shellClock_le_natLog
    {c : ℝ} (hc : 0 ≤ c) {M n : ℕ} (hnShell : n ∈ dyadicShell M) :
    c * (M : ℝ) * Real.log 2 ≤ c * Real.log n := by
  have hnLower : ((2 : ℕ) ^ M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hnShell).1
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
      hnLower
    rw [Real.log_pow] at h
    exact h
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlogLower hc

/-- Conversion of the shell target to the paper's natural-logarithm target. -/
theorem shellPolylogTarget_le_natLog
    {A : ℝ} (hA : 0 ≤ A) {M n : ℕ}
    (hnShell : n ∈ dyadicShell M) (hlogn : 1 ≤ Real.log n) :
    2 * (((M : ℝ) + 2) ^ A) ≤
      fixedPolylogTargetConstant A * (Real.log n) ^ A := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnLower : ((2 : ℕ) ^ M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hnShell).1
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
      hnLower
    rw [Real.log_pow] at h
    exact h
  have hM : (M : ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa [mul_comm] using hlogLower
  have hbase : (M : ℝ) + 2 ≤
      (1 / Real.log 2 + 2) * Real.log n := by
    calc
      (M : ℝ) + 2 ≤ Real.log n / Real.log 2 + 2 * Real.log n := by
        gcongr
        linarith
      _ = (1 / Real.log 2 + 2) * Real.log n := by ring
  have hleft0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hright0 : 0 ≤ (1 / Real.log 2 + 2) * Real.log n := by
    positivity
  have hpow := Real.rpow_le_rpow hleft0 hbase hA
  calc
    2 * (((M : ℝ) + 2) ^ A) ≤
        2 * (((1 / Real.log 2 + 2) * Real.log n) ^ A) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = fixedPolylogTargetConstant A * (Real.log n) ^ A := by
      rw [Real.mul_rpow (by positivity) (by linarith)]
      simp only [fixedPolylogTargetConstant]
      ring

end

end FirstPassageLinearTransport
