/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.NestedRecertification

/-!
# Rank-scaled reverse-loss budget

This module isolates the numerical induction behind the optimized terminal
profile.  A loss budget at a higher threshold is geometrically suppressed
when rescaled to the next lower threshold; the new block then fits exactly
inside the affine budget `(q + 2) / r`.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- The elementary geometric weight used by the rank-scaled budget. -/
theorem rankWeight_nat (q d : ℕ) :
    q + (d + 1) + 2 ≤ 2 ^ d * (q + 3) := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        q + (d + 1 + 1) + 2 ≤ 2 * (q + (d + 1) + 2) := by omega
        _ ≤ 2 * (2 ^ d * (q + 3)) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (d + 1) * (q + 3) := by
          rw [pow_succ]
          ring

theorem rankWeight_div (q d : ℕ) :
    ((q + (d + 1) + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1) ≤
      ((q + 3 : ℕ) : ℚ) / 2 := by
  have hnat := rankWeight_nat q d
  have hq :
      ((q + (d + 1) + 2 : ℕ) : ℚ) ≤
        ((2 ^ d * (q + 3) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hden : (0 : ℚ) ≤ (2 : ℚ) ^ (d + 1) := by positivity
  calc
    ((q + (d + 1) + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1) ≤
        ((2 ^ d * (q + 3) : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1) :=
      div_le_div_of_nonneg_right hq hden
    _ = ((q + 3 : ℕ) : ℚ) / 2 := by
      push_cast
      rw [pow_succ]
      have hp : (2 : ℚ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hp]

/-- One numerical rank step preserves the budget `(q + 2) / r`.  The old
threshold has rank `q + d + 1`, so at least one bit of scale is gained. -/
theorem rankScaledBudget_step
    {q d : ℕ} {r previous newLoss : ℚ}
    (hr : 0 < r)
    (hprevious : previous ≤ ((q + (d + 1) + 2 : ℕ) : ℚ) / r)
    (hlocal : newLoss ≤ ((q + 1 : ℕ) : ℚ) / (2 * r)) :
    (1 / (2 : ℚ) ^ (d + 1)) * previous + newLoss ≤
      ((q + 2 : ℕ) : ℚ) / r := by
  have hfactor : 0 ≤ (1 / (2 : ℚ) ^ (d + 1)) := by positivity
  have hold := mul_le_mul_of_nonneg_left hprevious hfactor
  have hweight := rankWeight_div q d
  have hweightR :
      (((q + (d + 1) + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (d + 1)) / r ≤
        (((q + 3 : ℕ) : ℚ) / 2) / r :=
    (div_le_div_iff_of_pos_right hr).2 hweight
  calc
    (1 / (2 : ℚ) ^ (d + 1)) * previous + newLoss ≤
        (1 / (2 : ℚ) ^ (d + 1)) *
            (((q + (d + 1) + 2 : ℕ) : ℚ) / r) +
          ((q + 1 : ℕ) : ℚ) / (2 * r) := add_le_add hold hlocal
    _ ≤ ((((q + 3 : ℕ) : ℚ) / 2) / r) +
          ((q + 1 : ℕ) : ℚ) / (2 * r) := by
      apply add_le_add
      · convert hweightR using 1 <;> ring
      · rfl
    _ = ((q + 2 : ℕ) : ℚ) / r := by
      field_simp [ne_of_gt hr]
      push_cast
      ring

/-- Applied form of the numerical step for two concatenated first-passage
segments. -/
theorem scaledReverseLoss_rank_step
    {q d m n k h : ℕ} {r : ℚ}
    (hr : 0 < r)
    (hprevious :
      scaledReverseLoss (2 ^ (q + d + 1)) n k ≤
        ((q + d + 3 : ℕ) : ℚ) / r)
    (hlocalFP : IsFirstPassage (2 ^ q) (orbit k n) h)
    (hhm : h ≤ m)
    (hm : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / r) :
    scaledReverseLoss (2 ^ q) n (k + h) ≤
      ((q + 2 : ℕ) : ℚ) / r := by
  have hYhi : 0 < 2 ^ (q + d + 1) := by positivity
  have hYlo : 0 < 2 ^ q := by positivity
  have hadd := scaledReverseLoss_add_rescaled
    (Ylo := 2 ^ q) (Yhi := 2 ^ (q + d + 1)) n k h hYhi
  have hratio :
      ((2 ^ q : ℕ) : ℚ) / ((2 ^ (q + d + 1) : ℕ) : ℚ) =
        1 / (2 : ℚ) ^ (d + 1) := by
    push_cast
    rw [show q + d + 1 = q + (d + 1) by omega, pow_add]
    have hp : (2 : ℚ) ^ q ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hp]
  have hlocal0 := scaledReverseLoss_le_half_time hYlo hlocalFP
  have hhq : (h : ℚ) ≤ (m : ℚ) := by exact_mod_cast hhm
  have hlocal :
      scaledReverseLoss (2 ^ q) (orbit k n) h ≤
        ((q + 1 : ℕ) : ℚ) / (2 * r) := by
    calc
      scaledReverseLoss (2 ^ q) (orbit k n) h ≤ (h : ℚ) / 2 := hlocal0
      _ ≤ (m : ℚ) / 2 := by linarith
      _ ≤ ((q + 1 : ℕ) : ℚ) / (2 * r) := by
        have hhalf := mul_le_mul_of_nonneg_left hm
          (by norm_num : (0 : ℚ) ≤ 1 / 2)
        convert hhalf using 1 <;> ring
  rw [hadd, hratio]
  exact rankScaledBudget_step hr hprevious hlocal

/-- A finite semantic chain of certified first-passage blocks.  The state
records the cumulative time and the most recent threshold rank. -/
inductive CertifiedRankChain (r : ℚ) (n : ℕ) : ℕ → ℕ → Prop
  | first {q m h : ℕ}
      (hfp : IsFirstPassage (2 ^ q) n h)
      (hhm : h ≤ m)
      (hm : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / r) :
      CertifiedRankChain r n h q
  | next {t qprev q m h : ℕ}
      (hchain : CertifiedRankChain r n t qprev)
      (hgap : q < qprev)
      (hfp : IsFirstPassage (2 ^ q) (orbit t n) h)
      (hhm : h ≤ m)
      (hm : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / r) :
      CertifiedRankChain r n (t + h) q

/-- Every cumulative landing of a certified rank chain is a direct first
passage of the original source. -/
theorem CertifiedRankChain.directFirstPassage
    {r : ℚ} {n t q : ℕ} (hchain : CertifiedRankChain r n t q) :
    IsFirstPassage (2 ^ q) n t := by
  induction hchain with
  | first hfp _hhm _hm => exact hfp
  | @next t qprev q m h hchain hgap hfp hhm hm ih =>
      have hthreshold : 2 ^ q < 2 ^ qprev :=
        Nat.pow_lt_pow_right (by omega) hgap
      exact ih.nested hthreshold hfp

/-- The complete all-block rank-scaled loss estimate. -/
theorem CertifiedRankChain.scaledReverseLoss_le
    {r : ℚ} (hr : 0 < r) {n t q : ℕ}
    (hchain : CertifiedRankChain r n t q) :
    scaledReverseLoss (2 ^ q) n t ≤ ((q + 2 : ℕ) : ℚ) / r := by
  induction hchain with
  | @first q m h hfp hhm hm =>
      have hY : 0 < 2 ^ q := by positivity
      have hlocal := scaledReverseLoss_le_half_time hY hfp
      have hhmQ : (h : ℚ) ≤ (m : ℚ) := by exact_mod_cast hhm
      calc
        scaledReverseLoss (2 ^ q) n h ≤ (h : ℚ) / 2 := hlocal
        _ ≤ (m : ℚ) / 2 := by linarith
        _ ≤ (((q + 1 : ℕ) : ℚ) / r) / 2 := by
          exact div_le_div_of_nonneg_right hm (by norm_num)
        _ ≤ ((q + 2 : ℕ) : ℚ) / r := by
          have hq :
              ((q + 1 : ℕ) : ℚ) / 2 ≤ ((q + 2 : ℕ) : ℚ) := by
            push_cast
            have hq0 : (0 : ℚ) ≤ q := by positivity
            linarith
          have hqR := (div_le_div_iff_of_pos_right hr).2 hq
          convert hqR using 1
          ring
  | @next t qprev q m h hchain hgap hfp hhm hm ih =>
      let d : ℕ := qprev - q - 1
      have hqprev : qprev = q + d + 1 := by
        dsimp [d]
        omega
      have hprevious :
          scaledReverseLoss (2 ^ (q + d + 1)) n t ≤
            ((q + d + 3 : ℕ) : ℚ) / r := by
        rw [hqprev] at ih
        convert ih using 1
      exact scaledReverseLoss_rank_step hr hprevious hfp hhm hm

end

end FirstPassageLinearTransport
