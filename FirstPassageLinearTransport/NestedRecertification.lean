/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.LossTransport
import FirstPassageLinearTransport.RawDynamics

/-!
# Nested first-passage re-certification

This module formalizes the structural cut vertex of the optimized assembly:
successive first passages through strictly decreasing thresholds collapse to a
direct first passage of the original source.  It also records the exact
additivity and rescaling laws for reverse loss under concatenation.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- Concatenating a first passage through a lower threshold to a first passage
through a higher threshold produces a direct first passage of the original
source through the lower threshold. -/
theorem IsFirstPassage.nested
    {Ylo Yhi n t h : ℕ}
    (hthreshold : Ylo < Yhi)
    (hhi : IsFirstPassage Yhi n t)
    (hlo : IsFirstPassage Ylo (orbit t n) h) :
    IsFirstPassage Ylo n (t + h) := by
  constructor
  · calc
      orbit (t + h) n = orbit (h + t) n := by rw [Nat.add_comm]
      _ = orbit h (orbit t n) := orbit_add h t n
      _ ≤ Ylo := hlo.1
  · intro j hj
    by_cases hjt : j < t
    · exact hthreshold.trans (hhi.2 j hjt)
    · have htj : t ≤ j := by omega
      have hlocal : j - t < h := by omega
      have hjform : j = (j - t) + t := by omega
      rw [hjform, orbit_add]
      exact hlo.2 (j - t) hlocal

/-- Reverse loss is shift-covariant under an orbit prefix. -/
theorem reverseLoss_add (n k j : ℕ) :
    reverseLoss n (k + j) = reverseLoss (orbit k n) j := by
  simp [reverseLoss, parityBit_add,
    show k + j + 1 = (j + 1) + k by omega, orbit_add]

theorem reverseLossTotal_succ (n h : ℕ) :
    reverseLossTotal n (h + 1) =
      reverseLossTotal n h + reverseLoss n h := by
  simp [reverseLossTotal, Finset.sum_range_succ]

/-- Total reverse loss is exactly additive under concatenation. -/
theorem reverseLossTotal_add (n k h : ℕ) :
    reverseLossTotal n (k + h) =
      reverseLossTotal n k + reverseLossTotal (orbit k n) h := by
  induction h with
  | zero => simp [reverseLossTotal]
  | succ h ih =>
      rw [show k + (h + 1) = k + h + 1 by omega,
        reverseLossTotal_succ, ih, reverseLoss_add,
        reverseLossTotal_succ]
      ring

/-- Exact rescaling of concatenated loss.  Earlier block loss is suppressed by
the ratio of the later threshold to the earlier one. -/
theorem scaledReverseLoss_add_rescaled
    {Ylo Yhi : ℕ} (n k h : ℕ) (hYhi : 0 < Yhi) :
    scaledReverseLoss Ylo n (k + h) =
      (Ylo : ℚ) / (Yhi : ℚ) * scaledReverseLoss Yhi n k +
        scaledReverseLoss Ylo (orbit k n) h := by
  have hYhiQ : (Yhi : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hYhi)
  rw [scaledReverseLoss, reverseLossTotal_add]
  simp only [scaledReverseLoss]
  field_simp [hYhiQ]

/-- A first-passage block of length `h` has scaled reverse loss at most
`h / 2` at its own threshold. -/
theorem scaledReverseLoss_le_half_time
    {Y n h : ℕ} (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    scaledReverseLoss Y n h ≤ (h : ℚ) / 2 := by
  have hsum :
      reverseLossTotal n h ≤ (h : ℚ) / (2 * (Y : ℚ)) := by
    unfold reverseLossTotal
    calc
      ∑ i ∈ Finset.range h, reverseLoss n i ≤
          ∑ _i ∈ Finset.range h, (1 / (2 * (Y : ℚ)) : ℚ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact reverseLoss_le_firstPassage hY hfp
              (Finset.mem_range.mp hi)
      _ = (h : ℚ) / (2 * (Y : ℚ)) := by
        simp
        ring
  have hYQ : (0 : ℚ) ≤ (Y : ℚ) := by positivity
  unfold scaledReverseLoss
  calc
    (Y : ℚ) * reverseLossTotal n h ≤
        (Y : ℚ) * ((h : ℚ) / (2 * (Y : ℚ))) :=
      mul_le_mul_of_nonneg_left hsum hYQ
    _ = (h : ℚ) / 2 := by
      have hYne : (Y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hY)
      field_simp [hYne]

end

end FirstPassageLinearTransport
