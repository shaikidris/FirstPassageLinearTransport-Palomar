/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.PolylogTerminalSchedule
import FirstPassageLinearTransport.TerminalProfile

/-!
# Terminal-tail asymptotics

This module contains the scalar terminal-tail estimates shared by the public
timeout proof.  Historical two-regime horizon and switch-rank profiles are
packaged separately.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Positive coefficient left after replacing the two terminal exponentials
by their slower common rate. -/
def terminalTailPrefactor (b b' c' : ℝ) : ℝ :=
  weightedTailConstant (Real.log 2) c' +
    Real.exp b * weightedTailConstant b b'

theorem weightedTailConstant_pos
    {c c' : ℝ} (hc' : 0 < c') (hcc' : c' < c) :
    0 < weightedTailConstant c c' := by
  unfold weightedTailConstant
  have hgap : 0 < c - c' := sub_pos.mpr hcc'
  have hexp : Real.exp (-c') < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hnum : 0 < 1 + 1 / (c - c') := by positivity
  have hden : 0 < 1 - Real.exp (-c') := sub_pos.mpr hexp
  exact div_pos hnum hden

theorem terminalTailPrefactor_pos
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    0 < terminalTailPrefactor b b' c' := by
  unfold terminalTailPrefactor
  have hdy := weightedTailConstant_pos hc' hc2
  have hent := weightedTailConstant_pos hb' hbb'
  positivity

/-- The exact two-term terminal tail is bounded by one exponential at the
slower retained rate. -/
theorem terminalTailBound_le_minRate
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (L : ℕ) :
    terminalTailBound b b' c' L ≤
      terminalTailPrefactor b b' c' *
        Real.exp (-(min b' c' * (L : ℝ))) := by
  have hdy0 : 0 ≤ weightedTailConstant (Real.log 2) c' :=
    (weightedTailConstant_pos hc' hc2).le
  have hent0 : 0 ≤ Real.exp b * weightedTailConstant b b' := by
    exact mul_nonneg (Real.exp_pos b).le
      (weightedTailConstant_pos hb' hbb').le
  have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hdyExp :
      Real.exp (-(c' * (L : ℝ))) ≤
        Real.exp (-(min b' c' * (L : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hmin := min_le_right b' c'
    nlinarith
  have hentExp :
      Real.exp (-(b' * (L : ℝ))) ≤
        Real.exp (-(min b' c' * (L : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hmin := min_le_left b' c'
    nlinarith
  unfold terminalTailBound terminalTailPrefactor
  calc
    weightedTailConstant (Real.log 2) c' *
          Real.exp (-(c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(b' * (L : ℝ))) ≤
      weightedTailConstant (Real.log 2) c' *
          Real.exp (-(min b' c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(min b' c' * (L : ℝ))) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hdyExp hdy0)
        (mul_le_mul_of_nonneg_left hentExp hent0)
    _ = (weightedTailConstant (Real.log 2) c' +
          Real.exp b * weightedTailConstant b b') *
        Real.exp (-(min b' c' * (L : ℝ))) := by ring

/-- Substitution of the terminal schedule gives the exact polynomial power
predicted by the paper calculation. -/
theorem terminalTailBound_polylog_le
    {A b b' c' : ℝ}
    (_hA : 0 < A)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (M : ℕ) :
    terminalTailBound b b' c' (polylogTerminalRank A M) ≤
      terminalTailPrefactor b b' c' *
        (((M : ℝ) + 2) ^
          (-(A * min b' c' / Real.log 2))) := by
  let d := min b' c'
  have hd : 0 < d := lt_min hb' hc'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 < (M : ℝ) + 2 := by positivity
  have hL := polylogTerminalRank_lower A M
  have hscaled :
      d * (A * Real.logb 2 ((M : ℝ) + 2)) ≤
        d * (polylogTerminalRank A M : ℝ) :=
    mul_le_mul_of_nonneg_left hL hd.le
  have hexp :
      Real.exp (-(d * (polylogTerminalRank A M : ℝ))) ≤
        Real.exp (-(d * (A * Real.logb 2 ((M : ℝ) + 2)))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hpref0 : 0 ≤ terminalTailPrefactor b b' c' :=
    (terminalTailPrefactor_pos hb' hbb' hc' hc2).le
  calc
    terminalTailBound b b' c' (polylogTerminalRank A M) ≤
        terminalTailPrefactor b b' c' *
          Real.exp (-(d * (polylogTerminalRank A M : ℝ))) := by
      simpa [d] using terminalTailBound_le_minRate
        hb' hbb' hc' hc2 (polylogTerminalRank A M)
    _ ≤ terminalTailPrefactor b b' c' *
        Real.exp (-(d * (A * Real.logb 2 ((M : ℝ) + 2)))) :=
      mul_le_mul_of_nonneg_left hexp hpref0
    _ = terminalTailPrefactor b b' c' *
        (((M : ℝ) + 2) ^ (-(A * d / Real.log 2))) := by
      congr 1
      rw [Real.rpow_def_of_pos hx]
      simp only [Real.logb]
      congr 1
      field_simp [ne_of_gt hlog2]

end

end FirstPassageLinearTransport
