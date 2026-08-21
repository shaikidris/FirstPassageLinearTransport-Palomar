/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.Order.Field.GeomSum
import FirstPassageLinearTransport.RecertificationRun

/-!
# Exponential terminal-tail summation

The optimized profile contains a linear rank factor multiplying an exponential
shell tail.  Any strict rate margin absorbs that factor while preserving an
arbitrarily close exponential rate.  This module proves the finite bound with
an explicit constant.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

noncomputable section

/-- Explicit constant for absorbing one linear rank factor and then summing
the remaining geometric tail. -/
def weightedTailConstant (c c' : ℝ) : ℝ :=
  (1 + 1 / (c - c')) / (1 - Real.exp (-c'))

theorem weighted_exp_term_le
    {c c' : ℝ} (hcc' : c' < c) (q : ℕ) :
    ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      (1 + 1 / (c - c')) * (Real.exp (-c')) ^ q := by
  let g := c - c'
  let C := 1 + 1 / g
  have hg : 0 < g := sub_pos.mpr hcc'
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hx0 : 0 ≤ g * (q : ℝ) := mul_nonneg hg.le (Nat.cast_nonneg q)
  have hpoly : ((q + 1 : ℕ) : ℝ) ≤ C * Real.exp (g * (q : ℝ)) := by
    have hexp := Real.add_one_le_exp (g * (q : ℝ))
    have hlinear : ((q + 1 : ℕ) : ℝ) ≤ C * (g * (q : ℝ) + 1) := by
      have hinv0 : 0 ≤ 1 / g := one_div_nonneg.mpr hg.le
      have hextra : 0 ≤ g * (q : ℝ) + 1 / g := add_nonneg hx0 hinv0
      have hrearrange :
          C * (g * (q : ℝ) + 1) =
            ((q + 1 : ℕ) : ℝ) + (g * (q : ℝ) + 1 / g) := by
        dsimp [C]
        field_simp [ne_of_gt hg]
        push_cast
        ring
      rw [hrearrange]
      exact le_add_of_nonneg_right hextra
    exact hlinear.trans (mul_le_mul_of_nonneg_left hexp hC0)
  calc
    ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        (C * Real.exp (g * (q : ℝ))) *
          Real.exp (-(c * (q : ℝ))) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = C * Real.exp (-(c' * (q : ℝ))) := by
      rw [mul_assoc, ← Real.exp_add]
      dsimp [g]
      congr 1
      ring
    _ = (1 + 1 / (c - c')) * (Real.exp (-c')) ^ q := by
      dsimp [C]
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- Finite weighted exponential tails retain every strict smaller rate. -/
theorem weighted_exp_Icc_le
    {c c' : ℝ} (hc' : 0 < c') (hcc' : c' < c) (L U : ℕ) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      weightedTailConstant c c' * Real.exp (-(c' * (L : ℝ))) := by
  let a := Real.exp (-c')
  let C := 1 + 1 / (c - c')
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a < 1 := by
    dsimp [a]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsum :
      ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        ∑ q ∈ Finset.Icc L U, C * a ^ q := by
    apply Finset.sum_le_sum
    intro q hq
    simpa [C, a] using weighted_exp_term_le hcc' q
  have hgeom :
      ∑ q ∈ Finset.Icc L U, a ^ q ≤ a ^ L / (1 - a) := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    exact geom_sum_Ico_le_of_lt_one ha0 ha1
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        ∑ q ∈ Finset.Icc L U, C * a ^ q := hsum
    _ = C * ∑ q ∈ Finset.Icc L U, a ^ q := by
      rw [Finset.mul_sum]
    _ ≤ C * (a ^ L / (1 - a)) := by
      exact mul_le_mul_of_nonneg_left hgeom (by
        dsimp [C]
        exact add_nonneg zero_le_one (one_div_nonneg.mpr (sub_nonneg.mpr hcc'.le)))
    _ = weightedTailConstant c c' * Real.exp (-(c' * (L : ℝ))) := by
      unfold weightedTailConstant
      dsimp [C, a]
      rw [← Real.exp_nat_mul]
      ring

end

end FirstPassageLinearTransport
