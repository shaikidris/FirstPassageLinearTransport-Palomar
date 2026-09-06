/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite ballot and multiplicative-maximum estimates

This module owns the finite Boolean-word input added in Version 4.  It checks
the centered survival estimate, the tilted binomial atom bound, and the exact
multiplicative maximal inequality used for the relative-height exception.  The
fixed-barrier three-block estimate is built in the same finite-word language.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators Real

noncomputable section

/-! ## Centered finite survival -/

def bernoulliAverage (p x₀ x₁ : ℝ) : ℝ :=
  (1 - p) * x₀ + p * x₁

noncomputable def stoppedWalkMean
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => z
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then z
      else bernoulliAverage p
        (stoppedWalkMean p x lo hi r (z + x false))
        (stoppedWalkMean p x lo hi r (z + x true))

noncomputable def stoppedWalkSecond
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => z ^ 2
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then z ^ 2
      else bernoulliAverage p
        (stoppedWalkSecond p x lo hi r (z + x false))
        (stoppedWalkSecond p x lo hi r (z + x true))

noncomputable def stoppedWalkTime
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then 0
      else 1 + bernoulliAverage p
        (stoppedWalkTime p x lo hi r (z + x false))
        (stoppedWalkTime p x lo hi r (z + x true))

noncomputable def stoppedUpperMass
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => if hi ≤ z then 1 else 0
  | r + 1, z =>
      if hi ≤ z then 1
      else if z < lo then 0
      else bernoulliAverage p
        (stoppedUpperMass p x lo hi r (z + x false))
        (stoppedUpperMass p x lo hi r (z + x true))

noncomputable def stoppedHorizonMass
    (p : ℝ) (x : Bool → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, z => if z < lo ∨ hi ≤ z then 0 else 1
  | r + 1, z =>
      if z < lo ∨ hi ≤ z then 0
      else bernoulliAverage p
        (stoppedHorizonMass p x lo hi r (z + x false))
        (stoppedHorizonMass p x lo hi r (z + x true))

noncomputable def lowerSurvivalMass
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) : ℕ → ℝ → ℝ
  | 0, z => if lo ≤ z then 1 else 0
  | r + 1, z =>
      if lo ≤ z then bernoulliAverage p
        (lowerSurvivalMass p x lo r (z + x false))
        (lowerSurvivalMass p x lo r (z + x true))
      else 0

theorem bernoulliAverage_nonneg
    {p x₀ x₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁) :
    0 ≤ bernoulliAverage p x₀ x₁ := by
  unfold bernoulliAverage
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hp₁) hx₀)
    (mul_nonneg hp₀ hx₁)

theorem bernoulliAverage_le_one
    {p x₀ x₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hx₀ : x₀ ≤ 1) (hx₁ : x₁ ≤ 1) :
    bernoulliAverage p x₀ x₁ ≤ 1 := by
  unfold bernoulliAverage
  nlinarith

theorem bernoulliAverage_mono
    {p a₀ a₁ b₀ b₁ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) :
    bernoulliAverage p a₀ a₁ ≤ bernoulliAverage p b₀ b₁ := by
  unfold bernoulliAverage
  exact add_le_add
    (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hp₁))
    (mul_le_mul_of_nonneg_left h₁ hp₀)

theorem lowerSurvivalMass_mem_unit
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo : ℝ) :
    ∀ r z, 0 ≤ lowerSurvivalMass p x lo r z ∧
      lowerSurvivalMass p x lo r z ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hz : lo ≤ z <;> simp [lowerSurvivalMass, hz]
  | succ r ihr =>
      intro z
      by_cases hz : lo ≤ z
      · simp only [lowerSurvivalMass, hz, if_true]
        exact ⟨bernoulliAverage_nonneg hp₀ hp₁ (ihr _).1 (ihr _).1,
          bernoulliAverage_le_one hp₀ hp₁ (ihr _).2 (ihr _).2⟩
      · simp [lowerSurvivalMass, hz]

theorem stoppedUpperMass_mem_unit
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ r z, 0 ≤ stoppedUpperMass p x lo hi r z ∧
      stoppedUpperMass p x lo hi r z ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hz : hi ≤ z <;> simp [stoppedUpperMass, hz]
  | succ r ihr =>
      intro z
      by_cases hup : hi ≤ z
      · simp [stoppedUpperMass, hup]
      · by_cases hlo : z < lo
        · simp [stoppedUpperMass, hup, hlo]
        · simp only [stoppedUpperMass, hup, hlo, if_false]
          exact ⟨bernoulliAverage_nonneg hp₀ hp₁ (ihr _).1 (ihr _).1,
            bernoulliAverage_le_one hp₀ hp₁ (ihr _).2 (ihr _).2⟩

theorem stoppedHorizonMass_mem_unit
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ r z, 0 ≤ stoppedHorizonMass p x lo hi r z ∧
      stoppedHorizonMass p x lo hi r z ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hz : z < lo ∨ hi ≤ z <;> simp [stoppedHorizonMass, hz]
  | succ r ihr =>
      intro z
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp [stoppedHorizonMass, hstop]
      · simp only [stoppedHorizonMass, hstop, if_false]
        exact ⟨bernoulliAverage_nonneg hp₀ hp₁ (ihr _).1 (ihr _).1,
          bernoulliAverage_le_one hp₀ hp₁ (ihr _).2 (ihr _).2⟩

theorem stoppedWalkMean_eq
    {p : ℝ} (x : Bool → ℝ) (lo hi : ℝ)
    (hcenter : bernoulliAverage p (x false) (x true) = 0) :
    ∀ r z, stoppedWalkMean p x lo hi r z = z := by
  intro r
  induction r with
  | zero => simp [stoppedWalkMean]
  | succ r ihr =>
      intro z
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp [stoppedWalkMean, hstop]
      · simp only [stoppedWalkMean, hstop, if_false, ihr]
        unfold bernoulliAverage at hcenter ⊢
        nlinarith

theorem stoppedWalkSecond_eq
    {p v : ℝ} (x : Bool → ℝ) (lo hi : ℝ)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v) :
    ∀ r z, stoppedWalkSecond p x lo hi r z =
      z ^ 2 + v * stoppedWalkTime p x lo hi r z := by
  intro r
  induction r with
  | zero => simp [stoppedWalkSecond, stoppedWalkTime]
  | succ r ihr =>
      intro z
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp [stoppedWalkSecond, stoppedWalkTime, hstop]
      · simp only [stoppedWalkSecond, stoppedWalkTime, hstop, if_false, ihr]
        calc
          bernoulliAverage p
              ((z + x false) ^ 2 +
                v * stoppedWalkTime p x lo hi r (z + x false))
              ((z + x true) ^ 2 +
                v * stoppedWalkTime p x lo hi r (z + x true)) =
              z ^ 2 + 2 * z * bernoulliAverage p (x false) (x true) +
                bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) +
                v * bernoulliAverage p
                  (stoppedWalkTime p x lo hi r (z + x false))
                  (stoppedWalkTime p x lo hi r (z + x true)) := by
            unfold bernoulliAverage
            ring
          _ = z ^ 2 + v *
              (1 + bernoulliAverage p
                (stoppedWalkTime p x lo hi r (z + x false))
                (stoppedWalkTime p x lo hi r (z + x true))) := by
            rw [hcenter, hvariance]
            ring

theorem stoppedWalkMoment_upper
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1) {lo hi : ℝ} :
    ∀ r z, lo - 1 ≤ z → z ≤ hi + 1 →
      stoppedWalkSecond p x lo hi r z ≤
        (lo + hi) * stoppedWalkMean p x lo hi r z -
          (lo - 1) * (hi + 1) := by
  intro r
  induction r with
  | zero =>
      intro z hzlo hzhi
      simp only [stoppedWalkSecond, stoppedWalkMean]
      have hprod : 0 ≤ (z - (lo - 1)) * ((hi + 1) - z) :=
        mul_nonneg (sub_nonneg.mpr hzlo) (sub_nonneg.mpr hzhi)
      nlinarith
  | succ r ihr =>
      intro z hzlo hzhi
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp only [stoppedWalkSecond, stoppedWalkMean, hstop, if_true]
        have hprod : 0 ≤ (z - (lo - 1)) * ((hi + 1) - z) :=
          mul_nonneg (sub_nonneg.mpr hzlo) (sub_nonneg.mpr hzhi)
        nlinarith
      · have hzSafe : lo ≤ z ∧ z < hi := by
          constructor
          · exact le_of_not_gt (fun h => hstop (Or.inl h))
          · exact lt_of_not_ge (fun h => hstop (Or.inr h))
        have hxFalse := abs_le.mp (hx false)
        have hxTrue := abs_le.mp (hx true)
        have hf := ihr (z + x false) (by linarith) (by linarith)
        have ht := ihr (z + x true) (by linarith) (by linarith)
        simp only [stoppedWalkSecond, stoppedWalkMean, hstop, if_false]
        have havg := bernoulliAverage_mono hp₀ hp₁ hf ht
        unfold bernoulliAverage at havg ⊢
        nlinarith

theorem stoppedUpperMass_mean_lower
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1) {lo hi : ℝ}
    (hlohi : lo ≤ hi) :
    ∀ r z, lo - 1 ≤ z →
      (lo - 1) * (1 - stoppedUpperMass p x lo hi r z) +
          hi * stoppedUpperMass p x lo hi r z ≤
        stoppedWalkMean p x lo hi r z := by
  intro r
  induction r with
  | zero =>
      intro z hzlo
      by_cases hup : hi ≤ z
      · simp [stoppedUpperMass, stoppedWalkMean, hup]
      · simp [stoppedUpperMass, stoppedWalkMean, hup, hzlo]
  | succ r ihr =>
      intro z hzlo
      by_cases hup : hi ≤ z
      · have hnotlo : ¬z < lo := by
          intro hz
          linarith
        simp [stoppedUpperMass, stoppedWalkMean, hup, hnotlo]
      · by_cases hlo : z < lo
        · have hstop : z < lo ∨ hi ≤ z := Or.inl hlo
          simp [stoppedUpperMass, stoppedWalkMean, hup, hlo, hstop, hzlo]
        · have hstop : ¬(z < lo ∨ hi ≤ z) := not_or_intro hlo hup
          have hxFalse := abs_le.mp (hx false)
          have hxTrue := abs_le.mp (hx true)
          have hf := ihr (z + x false) (by linarith)
          have ht := ihr (z + x true) (by linarith)
          simp only [stoppedUpperMass, stoppedWalkMean, hup, hlo, hstop, if_false]
          have havg := bernoulliAverage_mono hp₀ hp₁ hf ht
          calc
            (lo - 1) *
                  (1 - bernoulliAverage p
                    (stoppedUpperMass p x lo hi r (z + x false))
                    (stoppedUpperMass p x lo hi r (z + x true))) +
                hi * bernoulliAverage p
                  (stoppedUpperMass p x lo hi r (z + x false))
                  (stoppedUpperMass p x lo hi r (z + x true)) =
              bernoulliAverage p
                ((lo - 1) *
                    (1 - stoppedUpperMass p x lo hi r (z + x false)) +
                  hi * stoppedUpperMass p x lo hi r (z + x false))
                ((lo - 1) *
                    (1 - stoppedUpperMass p x lo hi r (z + x true)) +
                  hi * stoppedUpperMass p x lo hi r (z + x true)) := by
                unfold bernoulliAverage
                ring
            _ ≤ bernoulliAverage p
                (stoppedWalkMean p x lo hi r (z + x false))
                (stoppedWalkMean p x lo hi r (z + x true)) := havg

theorem stoppedHorizonMass_mul_le_time
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ (r : ℕ) (z : ℝ), (r : ℝ) * stoppedHorizonMass p x lo hi r z ≤
      stoppedWalkTime p x lo hi r z := by
  intro r
  induction r with
  | zero => simp [stoppedHorizonMass, stoppedWalkTime]
  | succ r ihr =>
      intro z
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp [stoppedHorizonMass, stoppedWalkTime, hstop]
      · have hf := ihr (z + x false)
        have ht := ihr (z + x true)
        have havg := bernoulliAverage_mono hp₀ hp₁ hf ht
        have hmass := stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi
        have hunit := bernoulliAverage_le_one hp₀ hp₁
          (hmass r (z + x false)).2 (hmass r (z + x true)).2
        simp only [stoppedHorizonMass, stoppedWalkTime, hstop, if_false,
          Nat.cast_add, Nat.cast_one]
        unfold bernoulliAverage at havg hunit ⊢
        nlinarith

theorem lowerSurvivalMass_le_stopped_split
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ r z, lowerSurvivalMass p x lo r z ≤
      stoppedUpperMass p x lo hi r z + stoppedHorizonMass p x lo hi r z := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hlo : lo ≤ z
      · by_cases hup : hi ≤ z
        · simp [lowerSurvivalMass, stoppedUpperMass, stoppedHorizonMass, hlo, hup]
        · have hnotstop : ¬(z < lo ∨ hi ≤ z) :=
            not_or_intro (not_lt.mpr hlo) hup
          simp [lowerSurvivalMass, stoppedUpperMass, stoppedHorizonMass,
            hlo, hup, not_lt.mpr hlo, hnotstop]
      · have hlt : z < lo := lt_of_not_ge hlo
        have hupNonneg := (stoppedUpperMass_mem_unit hp₀ hp₁ x lo hi 0 z).1
        simp only [lowerSurvivalMass, hlo, if_false]
        exact add_nonneg hupNonneg
          (stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi 0 z).1
  | succ r ihr =>
      intro z
      by_cases hlo : lo ≤ z
      · by_cases hup : hi ≤ z
        · have hsurv' :=
            (lowerSurvivalMass_mem_unit hp₀ hp₁ x lo (r + 1) z).2
          have hhor :=
            (stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi (r + 1) z).1
          rw [stoppedUpperMass]
          simp only [hup, if_true]
          linarith
        · have hnotlo : ¬z < lo := not_lt.mpr hlo
          have hnotstop : ¬(z < lo ∨ hi ≤ z) := not_or_intro hnotlo hup
          have hf := ihr (z + x false)
          have ht := ihr (z + x true)
          simp only [lowerSurvivalMass, stoppedUpperMass, stoppedHorizonMass,
            hlo, hup, hnotlo, hnotstop, if_true, if_false]
          calc
            bernoulliAverage p
                (lowerSurvivalMass p x lo r (z + x false))
                (lowerSurvivalMass p x lo r (z + x true)) ≤
              bernoulliAverage p
                (stoppedUpperMass p x lo hi r (z + x false) +
                  stoppedHorizonMass p x lo hi r (z + x false))
                (stoppedUpperMass p x lo hi r (z + x true) +
                  stoppedHorizonMass p x lo hi r (z + x true)) :=
                bernoulliAverage_mono hp₀ hp₁ hf ht
            _ = bernoulliAverage p
                  (stoppedUpperMass p x lo hi r (z + x false))
                  (stoppedUpperMass p x lo hi r (z + x true)) +
                bernoulliAverage p
                  (stoppedHorizonMass p x lo hi r (z + x false))
                  (stoppedHorizonMass p x lo hi r (z + x true)) := by
              unfold bernoulliAverage
              ring
      · have hlt : z < lo := lt_of_not_ge hlo
        have hupNonneg :=
          (stoppedUpperMass_mem_unit hp₀ hp₁ x lo hi (r + 1) z).1
        have hhorNonneg :=
          (stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi (r + 1) z).1
        simp only [lowerSurvivalMass, hlo, if_false]
        exact add_nonneg hupNonneg hhorNonneg

/-- The first, quantitative inequality in Appendix B.1, specialized to the
two-letter weighted walk used by the Collatz tilt. -/
theorem lowerSurvivalMass_le_centered_explicit
    {p v h : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hv : 0 < v) (hh : 0 ≤ h)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v)
    {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass p x (-h) n 0 ≤
      (h + 1) / (Real.sqrt n + h + 1) +
        (h + 1) * (Real.sqrt n + 1) / (v * n) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hlohi : -h ≤ Real.sqrt (n : ℝ) := by
    exact le_trans (neg_nonpos.mpr hh) (Real.sqrt_nonneg _)
  let upper := stoppedUpperMass p x (-h) (Real.sqrt n) n 0
  let horizon := stoppedHorizonMass p x (-h) (Real.sqrt n) n 0
  let time := stoppedWalkTime p x (-h) (Real.sqrt n) n 0
  have hmean := stoppedWalkMean_eq x (-h) (Real.sqrt n) hcenter n 0
  have hupperMoment := stoppedUpperMass_mean_lower hp₀ hp₁ hx hlohi n 0 (by linarith)
  have hupperLinear :
      (Real.sqrt n + h + 1) * upper ≤ h + 1 := by
    dsimp [upper]
    rw [hmean] at hupperMoment
    nlinarith
  have hdenPos : 0 < Real.sqrt n + h + 1 := by positivity
  have hupper : upper ≤ (h + 1) / (Real.sqrt n + h + 1) :=
    (le_div_iff₀ hdenPos).2 (by simpa [mul_comm] using hupperLinear)
  have hsecond := stoppedWalkSecond_eq x (-h) (Real.sqrt n)
    hcenter hvariance n (0 : ℝ)
  have hmoment := stoppedWalkMoment_upper hp₀ hp₁ hx
    (lo := -h) (hi := Real.sqrt n) n (0 : ℝ)
    (by linarith)
    (by have hs := Real.sqrt_nonneg (n : ℝ); linarith)
  have htimeLinear : v * time ≤ (h + 1) * (Real.sqrt n + 1) := by
    dsimp [time]
    rw [hsecond, hmean] at hmoment
    nlinarith
  have htime : time ≤ (h + 1) * (Real.sqrt n + 1) / v :=
    (le_div_iff₀ hv).2 (by simpa [mul_comm] using htimeLinear)
  have hhorizonMul := stoppedHorizonMass_mul_le_time hp₀ hp₁
    x (-h) (Real.sqrt n) n 0
  have hhorizon :
      horizon ≤ (h + 1) * (Real.sqrt n + 1) / (v * n) := by
    calc
      horizon ≤ time / (n : ℝ) := by
        exact (le_div_iff₀ hnR).2
          (by simpa [horizon, time, mul_comm] using hhorizonMul)
      _ ≤ ((h + 1) * (Real.sqrt n + 1) / v) / (n : ℝ) :=
        div_le_div_of_nonneg_right htime hnR.le
      _ = (h + 1) * (Real.sqrt n + 1) / (v * n) := by
        field_simp [hv.ne', hnR.ne']
  have hsplit := lowerSurvivalMass_le_stopped_split hp₀ hp₁
    x (-h) (Real.sqrt n) n 0
  exact hsplit.trans (add_le_add hupper hhorizon)

/-- Appendix B.1 in the `O((h+1)/sqrt n)` form consumed twice by the
three-block fixed-barrier argument. -/
theorem lowerSurvivalMass_le_centered
    {p v h : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hv : 0 < v) (hh : 0 ≤ h)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v)
    {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass p x (-h) n 0 ≤
      (1 + 2 / v) * (h + 1) / Real.sqrt n := by
  have hexplicit := lowerSurvivalMass_le_centered_explicit
    hp₀ hp₁ hv hh hx hcenter hvariance hn
  have hnR : 0 < (n : ℝ) := by positivity
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrtOne : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hfirst :
      (h + 1) / (Real.sqrt n + h + 1) ≤
        (h + 1) / Real.sqrt n := by
    exact div_le_div_of_nonneg_left (by linarith) hsqrtPos (by linarith)
  have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnR.le
  have hratio :
      (Real.sqrt n + 1) / (n : ℝ) ≤ 2 / Real.sqrt n := by
    apply (div_le_div_iff₀ hnR hsqrtPos).2
    nlinarith
  have hfactor : 0 ≤ (h + 1) / v := by positivity
  have hsecond :
      (h + 1) * (Real.sqrt n + 1) / (v * n) ≤
        (2 / v) * (h + 1) / Real.sqrt n := by
    calc
      (h + 1) * (Real.sqrt n + 1) / (v * n) =
          ((h + 1) / v) * ((Real.sqrt n + 1) / n) := by
        field_simp [hv.ne', hnR.ne']
      _ ≤ ((h + 1) / v) * (2 / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hratio hfactor
      _ = (2 / v) * (h + 1) / Real.sqrt n := by ring
  calc
    lowerSurvivalMass p x (-h) n 0 ≤
        (h + 1) / (Real.sqrt n + h + 1) +
          (h + 1) * (Real.sqrt n + 1) / (v * n) := hexplicit
    _ ≤ (h + 1) / Real.sqrt n +
        (2 / v) * (h + 1) / Real.sqrt n := add_le_add hfirst hsecond
    _ = (1 + 2 / v) * (h + 1) / Real.sqrt n := by ring

/-! ## The tilted binomial atom -/

/-- Gibbs' inequality for a Bernoulli law, in exactly the logarithmic form
needed to cancel the entropy exponential in the Stirling estimate.  Keeping
this lemma elementary avoids importing a measure-theoretic relative-entropy
interface into the finite-word cone. -/
theorem entropy_add_logLikelihood_le_zero
    {p u : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (hu₀ : 0 < u) (hu₁ : u < 1) :
    Real.binEntropy u + u * Real.log p +
        (1 - u) * Real.log (1 - p) ≤ 0 := by
  have hpComp : 0 < 1 - p := sub_pos.mpr hp₁
  have huComp : 0 < 1 - u := sub_pos.mpr hu₁
  have hleft := Real.log_le_sub_one_of_pos (div_pos hp₀ hu₀)
  have hright := Real.log_le_sub_one_of_pos (div_pos hpComp huComp)
  have hleft' :
      u * Real.log (p / u) ≤ p - u := by
    calc
      u * Real.log (p / u) ≤ u * (p / u - 1) :=
        mul_le_mul_of_nonneg_left hleft hu₀.le
      _ = p - u := by field_simp [hu₀.ne']
  have hright' :
      (1 - u) * Real.log ((1 - p) / (1 - u)) ≤ u - p := by
    calc
      (1 - u) * Real.log ((1 - p) / (1 - u)) ≤
          (1 - u) * ((1 - p) / (1 - u) - 1) :=
        mul_le_mul_of_nonneg_left hright huComp.le
      _ = u - p := by
        field_simp [huComp.ne']
        ring
  calc
    Real.binEntropy u + u * Real.log p +
        (1 - u) * Real.log (1 - p) =
        u * Real.log (p / u) +
          (1 - u) * Real.log ((1 - p) / (1 - u)) := by
      rw [Real.binEntropy, Real.log_inv, Real.log_inv,
        Real.log_div hp₀.ne' hu₀.ne',
        Real.log_div hpComp.ne' huComp.ne']
      ring
    _ ≤ (p - u) + (u - p) := add_le_add hleft' hright'
    _ = 0 := by ring

theorem binomial_log_mass_le_zero
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    binomialLogWeight n k + (k : ℝ) * Real.log p +
        ((n - k : ℕ) : ℝ) * Real.log (1 - p) ≤ 0 := by
  have hn : 0 < n := hk.trans hkn
  have hnR : 0 < (n : ℝ) := by positivity
  have hu₀ : 0 < (k : ℝ) / (n : ℝ) := div_pos (by positivity) hnR
  have hu₁ : (k : ℝ) / (n : ℝ) < 1 :=
    (div_lt_one hnR).2 (by exact_mod_cast hkn)
  have hentropy := entropy_add_logLikelihood_le_zero hp₀ hp₁ hu₀ hu₁
  have hmul := mul_le_mul_of_nonneg_left hentropy hnR.le
  rw [binomialLogWeight_eq_mul_binEntropy hk hkn, Nat.cast_sub hkn.le]
  calc
    (n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)) +
          (k : ℝ) * Real.log p +
          ((n : ℝ) - (k : ℝ)) * Real.log (1 - p) =
        (n : ℝ) *
          (Real.binEntropy ((k : ℝ) / (n : ℝ)) +
            ((k : ℝ) / (n : ℝ)) * Real.log p +
            (1 - (k : ℝ) / (n : ℝ)) * Real.log (1 - p)) := by
      field_simp [hnR.ne']
    _ ≤ (n : ℝ) * 0 := hmul
    _ = 0 := by ring

theorem exp_binomialLogWeight_mul_powers_le_one
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Real.exp (binomialLogWeight n k) * p ^ k * (1 - p) ^ (n - k) ≤ 1 := by
  have hpComp : 0 < 1 - p := sub_pos.mpr hp₁
  have hlog := binomial_log_mass_le_zero hp₀ hp₁ hk hkn
  have hpPow : p ^ k = Real.exp ((k : ℝ) * Real.log p) := by
    rw [Real.exp_nat_mul, Real.exp_log hp₀]
  have hpCompPow :
      (1 - p) ^ (n - k) =
        Real.exp (((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
    rw [Real.exp_nat_mul, Real.exp_log hpComp]
  calc
    Real.exp (binomialLogWeight n k) * p ^ k * (1 - p) ^ (n - k) =
        Real.exp (binomialLogWeight n k + (k : ℝ) * Real.log p +
          ((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
      rw [hpPow, hpCompPow, Real.exp_add, Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hlog
    _ = 1 := Real.exp_zero

/-- Real-valued mass of the `k`th atom of a binomial law. -/
noncomputable def tiltedBinomialMass (p : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

theorem exists_tiltedBinomialMass_le_sqrt_of_quarter
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 0 < n → 0 < k → k < n →
        (n : ℝ) / 4 ≤ (k : ℝ) →
        (n : ℝ) / 4 ≤ ((n - k : ℕ) : ℝ) →
        tiltedBinomialMass p n k ≤ C / Real.sqrt n := by
  obtain ⟨C₀, hC₀, hchoose⟩ := exists_choose_le_stirlingCore_ratio
  refine ⟨4 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro n k hn hk hkn hkLower hnkLower
  have hchoose' := hchoose n k hk hkn
  have hchoose'' :
      (n.choose k : ℝ) ≤
        C₀ * (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) *
            Real.exp (binomialLogWeight n k)) := by
    calc
      (n.choose k : ℝ) ≤
          C₀ * stirlingCore n /
            (stirlingCore k * stirlingCore (n - k)) := hchoose'
      _ = C₀ *
          (stirlingCore n /
            (stirlingCore k * stirlingCore (n - k))) := by ring
      _ = C₀ * (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) *
            Real.exp (binomialLogWeight n k)) := by
        rw [stirlingCore_ratio_eq_sqrt_exp hk hkn]
  have hpref := stirlingSqrtPrefactor_le_of_quarter
    hn hk hkn hkLower hnkLower
  have hweight := exp_binomialLogWeight_mul_powers_le_one
    hp₀ hp₁ hk hkn
  have hpNonneg : 0 ≤ p ^ k * (1 - p) ^ (n - k) :=
    mul_nonneg (pow_nonneg hp₀.le _) (pow_nonneg (sub_nonneg.mpr hp₁.le) _)
  have hCNonneg : 0 ≤ C₀ := hC₀.le
  have hprefNonneg :
      0 ≤ Real.sqrt (2 * n) /
        (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) := by positivity
  have hweightNonneg :
      0 ≤ Real.exp (binomialLogWeight n k) * p ^ k *
        (1 - p) ^ (n - k) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hp₀.le _))
      (pow_nonneg (sub_nonneg.mpr hp₁.le) _)
  have hboundNonneg : 0 ≤ C₀ * (4 / Real.sqrt n) := by positivity
  unfold tiltedBinomialMass
  calc
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤
        (C₀ * (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k))) *
            Real.exp (binomialLogWeight n k))) *
              p ^ k * (1 - p) ^ (n - k) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchoose'' (pow_nonneg hp₀.le _))
        (pow_nonneg (sub_nonneg.mpr hp₁.le) _)
    _ = C₀ *
        (Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k)))) *
        (Real.exp (binomialLogWeight n k) * p ^ k *
          (1 - p) ^ (n - k)) := by ring
    _ ≤ C₀ * (4 / Real.sqrt n) * 1 := by
      calc
        C₀ * (Real.sqrt (2 * n) /
              (Real.sqrt (2 * k) * Real.sqrt (2 * (n - k)))) *
            (Real.exp (binomialLogWeight n k) * p ^ k *
              (1 - p) ^ (n - k)) ≤
            C₀ * (4 / Real.sqrt n) *
              (Real.exp (binomialLogWeight n k) * p ^ k *
                (1 - p) ^ (n - k)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpref hCNonneg) hweightNonneg
        _ ≤ C₀ * (4 / Real.sqrt n) * 1 :=
          mul_le_mul_of_nonneg_left hweight hboundNonneg
    _ = (4 * C₀) / Real.sqrt n := by ring

theorem tiltedBinomialMass_succ_balance
    {p : ℝ} {n k : ℕ} (hkn : k < n) :
    ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n (k + 1) =
      ((n - k : ℕ) : ℝ) * p * tiltedBinomialMass p n k := by
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  have hchoose :
      ((n.choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        ((n.choose k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  unfold tiltedBinomialMass
  calc
    ((k + 1 : ℕ) : ℝ) * (1 - p) *
        (((n.choose (k + 1) : ℕ) : ℝ) * p ^ (k + 1) *
          (1 - p) ^ (n - (k + 1))) =
        (((n.choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
          p ^ (k + 1) * ((1 - p) ^ (n - (k + 1)) * (1 - p)) := by ring
    _ = (((n.choose k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) *
          p ^ (k + 1) * ((1 - p) ^ (n - (k + 1)) * (1 - p)) := by rw [hchoose]
    _ = ((n - k : ℕ) : ℝ) * p *
          (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k)) := by
      rw [pow_succ p k, hsub, pow_succ]
      ring

theorem tiltedBinomialMass_pos
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hkn : k ≤ n) :
    0 < tiltedBinomialMass p n k := by
  have hchoose : 0 < n.choose k := Nat.choose_pos hkn
  unfold tiltedBinomialMass
  exact mul_pos (mul_pos (by exact_mod_cast hchoose) (pow_pos hp₀ _))
    (pow_pos (sub_pos.mpr hp₁) _)

theorem tiltedBinomialMass_nonneg
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n k : ℕ) :
    0 ≤ tiltedBinomialMass p n k := by
  unfold tiltedBinomialMass
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp₀ _))
    (pow_nonneg (sub_nonneg.mpr hp₁) _)

theorem sum_tiltedBinomialMass
    {p : ℝ} (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), tiltedBinomialMass p n k = 1 := by
  calc
    ∑ k ∈ Finset.range (n + 1), tiltedBinomialMass p n k =
        ∑ k ∈ Finset.range (n + 1),
          p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold tiltedBinomialMass
      ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by simp

theorem tiltedBinomialMass_le_one
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n k : ℕ) :
    tiltedBinomialMass p n k ≤ 1 := by
  by_cases hkn : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hle : tiltedBinomialMass p n k ≤
        ∑ j ∈ Finset.range (n + 1), tiltedBinomialMass p n j := by
      exact Finset.single_le_sum
        (fun j _ => tiltedBinomialMass_nonneg hp₀ hp₁ n j) hmem
    simpa [sum_tiltedBinomialMass n] using hle
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    simp [tiltedBinomialMass, Nat.choose_eq_zero_of_lt hnk]

theorem tiltedBinomialMass_lt_succ_of_ratio
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hkn : k < n)
    (hratio : ((k + 1 : ℕ) : ℝ) * (1 - p) <
      ((n - k : ℕ) : ℝ) * p) :
    tiltedBinomialMass p n k < tiltedBinomialMass p n (k + 1) := by
  have hmass := tiltedBinomialMass_pos hp₀ hp₁ hkn.le
  have hcoef : 0 < ((k + 1 : ℕ) : ℝ) * (1 - p) := by
    exact mul_pos (by positivity) (sub_pos.mpr hp₁)
  have hbalance := tiltedBinomialMass_succ_balance (p := p) hkn
  apply lt_of_mul_lt_mul_left _ hcoef.le
  calc
    ((k + 1 : ℕ) : ℝ) * (1 - p) * tiltedBinomialMass p n k <
        ((n - k : ℕ) : ℝ) * p * tiltedBinomialMass p n k :=
      mul_lt_mul_of_pos_right hratio hmass
    _ = ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n (k + 1) := hbalance.symm

theorem tiltedBinomialMass_succ_lt_of_ratio
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hkn : k < n)
    (hratio : ((n - k : ℕ) : ℝ) * p <
      ((k + 1 : ℕ) : ℝ) * (1 - p)) :
    tiltedBinomialMass p n (k + 1) < tiltedBinomialMass p n k := by
  have hmass := tiltedBinomialMass_pos hp₀ hp₁ hkn.le
  have hcoef : 0 < ((k + 1 : ℕ) : ℝ) * (1 - p) := by
    exact mul_pos (by positivity) (sub_pos.mpr hp₁)
  have hbalance := tiltedBinomialMass_succ_balance (p := p) hkn
  apply lt_of_mul_lt_mul_left _ hcoef.le
  calc
    ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n (k + 1) =
      ((n - k : ℕ) : ℝ) * p * tiltedBinomialMass p n k := hbalance
    _ < ((k + 1 : ℕ) : ℝ) * (1 - p) *
        tiltedBinomialMass p n k := mul_lt_mul_of_pos_right hratio hmass

theorem maximizer_is_in_quarter_window
    {p : ℝ} (hpHalf : 1 / 2 < p) (hpTwoThird : p < 2 / 3)
    {n k₀ : ℕ} (hn : 9 ≤ n) (hk₀n : k₀ ≤ n)
    (hmax : ∀ k : ℕ, k ≤ n →
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀) :
    (n : ℝ) / 4 ≤ (k₀ : ℝ) ∧
      (n : ℝ) / 4 ≤ ((n - k₀ : ℕ) : ℝ) := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : p < 1 := by linarith
  constructor
  · by_contra hnot
    have hkLower : (k₀ : ℝ) < (n : ℝ) / 4 := lt_of_not_ge hnot
    have h4cast : (4 * k₀ : ℕ) < n := by
      exact_mod_cast (show (4 : ℝ) * (k₀ : ℝ) < (n : ℝ) by nlinarith)
    have hk₀n' : k₀ < n := by omega
    have hstep : k₀ + 1 ≤ n - k₀ := by omega
    have hratio : ((k₀ + 1 : ℕ) : ℝ) * (1 - p) <
        ((n - k₀ : ℕ) : ℝ) * p := by
      calc
        ((k₀ + 1 : ℕ) : ℝ) * (1 - p) <
            ((k₀ + 1 : ℕ) : ℝ) * p := by
          apply mul_lt_mul_of_pos_left
          · linarith
          · positivity
        _ ≤ ((n - k₀ : ℕ) : ℝ) * p := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hstep) hp₀.le
    have hinc := tiltedBinomialMass_lt_succ_of_ratio hp₀ hp₁ hk₀n' hratio
    exact (not_le_of_gt hinc) (hmax (k₀ + 1) (by omega))
  · by_contra hnot
    have hrLower : ((n - k₀ : ℕ) : ℝ) < (n : ℝ) / 4 :=
      lt_of_not_ge hnot
    have hk₀pos : 0 < k₀ := by
      by_contra hkzero
      have : k₀ = 0 := Nat.eq_zero_of_not_pos hkzero
      subst k₀
      have hnR : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      norm_num only [Nat.sub_zero] at hrLower
      nlinarith
    let j := k₀ - 1
    have hjSucc : j + 1 = k₀ := by dsimp [j]; omega
    have hjn : j < n := by dsimp [j]; omega
    have hsub : n - j = (n - k₀) + 1 := by dsimp [j]; omega
    have hkLarge : (3 : ℝ) * (n : ℝ) / 4 < (k₀ : ℝ) := by
      have hcast : ((n - k₀ : ℕ) : ℝ) = (n : ℝ) - (k₀ : ℝ) :=
        Nat.cast_sub hk₀n
      nlinarith
    have hnReal : (8 : ℝ) < (n : ℝ) := by exact_mod_cast (show 8 < n by omega)
    have hratio : ((n - j : ℕ) : ℝ) * p <
        ((j + 1 : ℕ) : ℝ) * (1 - p) := by
      rw [hsub, hjSucc, Nat.cast_add, Nat.cast_one]
      calc
        (((n - k₀ : ℕ) : ℝ) + 1) * p <
            ((n : ℝ) / 4 + 1) * p := by
          exact mul_lt_mul_of_pos_right (by linarith) hp₀
        _ < ((n : ℝ) / 4 + 1) * (2 / 3) := by
          exact mul_lt_mul_of_pos_left hpTwoThird (by positivity)
        _ < (n : ℝ) / 4 := by nlinarith
        _ < (k₀ : ℝ) * (1 / 3) := by nlinarith
        _ < (k₀ : ℝ) * (1 - p) := by
          apply mul_lt_mul_of_pos_left
          · linarith
          · positivity
    have hdec := tiltedBinomialMass_succ_lt_of_ratio hp₀ hp₁ hjn hratio
    rw [hjSucc] at hdec
    exact (not_le_of_gt hdec) (hmax j (by dsimp [j]; omega))

theorem exists_tiltedBinomialMass_maximizer (p : ℝ) (n : ℕ) :
    ∃ k₀ : ℕ, k₀ ≤ n ∧ ∀ k : ℕ, k ≤ n →
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀ := by
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨k₀, hk₀, hmax⟩ :=
    Finset.exists_max_image (Finset.range (n + 1))
      (tiltedBinomialMass p n) hne
  have hk₀le : k₀ ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk₀)
  refine ⟨k₀, hk₀le, ?_⟩
  intro k hk
  exact hmax k (Finset.mem_range.mpr (by omega))

/-- Appendix B.2: uniformly in the atom index, a tilted binomial law with
parameter in the Collatz window `(1/2, 2/3)` has mass `O(n⁻¹ʲ²)`. -/
theorem exists_tiltedBinomialMass_le_sqrt
    {p : ℝ} (hpHalf : 1 / 2 < p) (hpTwoThird : p < 2 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 0 < n →
      tiltedBinomialMass p n k ≤ C / Real.sqrt n := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : p < 1 := by linarith
  obtain ⟨C₀, hC₀, hcentral⟩ :=
    exists_tiltedBinomialMass_le_sqrt_of_quarter hp₀ hp₁
  refine ⟨max C₀ 3, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro n k hn
  by_cases hnLarge : 9 ≤ n
  · obtain ⟨k₀, hk₀n, hmax⟩ := exists_tiltedBinomialMass_maximizer p n
    obtain ⟨hkLower, hnkLower⟩ :=
      maximizer_is_in_quarter_window hpHalf hpTwoThird hnLarge hk₀n hmax
    have hk₀ : 0 < k₀ := by
      have hnR : 0 < (n : ℝ) := by positivity
      have : 0 < (k₀ : ℝ) :=
        lt_of_lt_of_le (by positivity : 0 < (n : ℝ) / 4) hkLower
      exact_mod_cast this
    have hk₀n' : k₀ < n := by
      have hdiff : 0 < n - k₀ := by
        have hnR : 0 < (n : ℝ) := by positivity
        have : 0 < ((n - k₀ : ℕ) : ℝ) :=
          lt_of_lt_of_le (by positivity : 0 < (n : ℝ) / 4) hnkLower
        exact_mod_cast this
      omega
    have hkmax : tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀ := by
      by_cases hkn : k ≤ n
      · exact hmax k hkn
      · have hnk : n < k := Nat.lt_of_not_ge hkn
        have hzero : tiltedBinomialMass p n k = 0 := by
          simp [tiltedBinomialMass, Nat.choose_eq_zero_of_lt hnk]
        rw [hzero]
        exact tiltedBinomialMass_nonneg hp₀.le hp₁.le n k₀
    calc
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀ := hkmax
      _ ≤ C₀ / Real.sqrt n :=
        hcentral n k₀ hn hk₀ hk₀n' hkLower hnkLower
      _ ≤ max C₀ 3 / Real.sqrt n := by
        exact div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · have hnNine : n ≤ 9 := by omega
    have hmass := tiltedBinomialMass_le_one hp₀.le hp₁.le n k
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hsqrt : Real.sqrt (n : ℝ) ≤ 3 := by
      calc
        Real.sqrt (n : ℝ) ≤ Real.sqrt 9 :=
          Real.sqrt_le_sqrt (by exact_mod_cast hnNine)
        _ = 3 := by
          rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
            Real.sqrt_sq_eq_abs]
          norm_num
    have hone : (1 : ℝ) ≤ 3 / Real.sqrt n := by
      rw [le_div_iff₀ hsqrtPos]
      simpa using hsqrt
    exact hmass.trans (hone.trans (div_le_div_of_nonneg_right
      (le_max_right C₀ 3) (Real.sqrt_nonneg _)))

/-! ## The Collatz tilted walk -/

/-- Sum of the increments carried by a finite Boolean word. -/
def wordIncrementSum {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) : ℝ :=
  ∑ i, x (v i)

@[simp] theorem wordIncrementSum_cons
    {r : ℕ} (x : Bool → ℝ) (b : Bool) (w : Fin r → Bool) :
    wordIncrementSum x (Fin.cons b w) =
      x b + wordIncrementSum x w := by
  unfold wordIncrementSum
  rw [Fin.sum_univ_succ]
  simp

@[simp] theorem wordIncrementSum_append
    {r s : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) (w : Fin s → Bool) :
    wordIncrementSum x (Fin.append v w) =
      wordIncrementSum x v + wordIncrementSum x w := by
  unfold wordIncrementSum
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _hi
    simp [Fin.append]
  · apply Finset.sum_congr rfl
    intro i _hi
    simp [Fin.append]

theorem wordIncrementSum_neg
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum (fun bit ↦ -x bit) v = -wordIncrementSum x v := by
  unfold wordIncrementSum
  simpa only [Finset.sum_neg_distrib]

/-- The logarithmic shortcut multiplier attached to one parity bit. -/
def collatzLogIncrement (b : Bool) : ℝ :=
  if b then Real.log 3 - Real.log 2 else -Real.log 2

theorem collatzLogIncrement_eq (b : Bool) :
    collatzLogIncrement b =
      (if b then Real.log 3 else 0) - Real.log 2 := by
  cases b <;> simp [collatzLogIncrement]

/-- The increment sum depends only on the number of true bits.  This is the
lattice identity used to reduce every middle-block terminal interval to at
most one binomial atom. -/
theorem wordIncrementSum_collatz
    {r : ℕ} (v : Fin r → Bool) :
    wordIncrementSum collatzLogIncrement v =
      ((boolSupport v).card : ℝ) * Real.log 3 - (r : ℝ) * Real.log 2 := by
  classical
  unfold wordIncrementSum
  simp_rw [collatzLogIncrement_eq]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : Fin r, (if v i then Real.log 3 else 0)) =
      ∑ i ∈ (Finset.univ : Finset (Fin r)),
        (if v i = true then (1 : ℝ) else 0) * Real.log 3 by
    apply Finset.sum_congr rfl
    intro i _hi
    cases h : v i <;> simp [h]]
  rw [← Finset.sum_mul]
  simp [boolSupport]

theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three

/-- An interval of length one contains at most one support count for the
Collatz logarithmic lattice.  The decisive spacing is `log 3 > 1`. -/
theorem collatz_support_unique_in_unit_interval
    {k l : ℕ} {a : ℝ}
    (hklo : a ≤ (k : ℝ) * Real.log 3)
    (hkhi : (k : ℝ) * Real.log 3 < a + 1)
    (hllo : a ≤ (l : ℝ) * Real.log 3)
    (hlhi : (l : ℝ) * Real.log 3 < a + 1) :
    k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hcast : (1 : ℝ) ≤ (l : ℝ) - (k : ℝ) := by
      have hc : ((k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hkl)
      norm_num at hc ⊢
      linarith
    have hmul : Real.log 3 ≤ ((l : ℝ) - (k : ℝ)) * Real.log 3 := by
      simpa using mul_le_mul_of_nonneg_right hcast
        (zero_le_one.trans one_lt_log_three.le)
    have hgap :
        (1 : ℝ) < (l : ℝ) * Real.log 3 - (k : ℝ) * Real.log 3 := by
      calc
        (1 : ℝ) < Real.log 3 := one_lt_log_three
        _ ≤ ((l : ℝ) - (k : ℝ)) * Real.log 3 := hmul
        _ = (l : ℝ) * Real.log 3 - (k : ℝ) * Real.log 3 := by ring
    linarith
  · exact hkl
  · have hcast : (1 : ℝ) ≤ (k : ℝ) - (l : ℝ) := by
      have hc : ((l + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hkl)
      norm_num at hc ⊢
      linarith
    have hmul : Real.log 3 ≤ ((k : ℝ) - (l : ℝ)) * Real.log 3 := by
      simpa using mul_le_mul_of_nonneg_right hcast
        (zero_le_one.trans one_lt_log_three.le)
    have hgap :
        (1 : ℝ) < (k : ℝ) * Real.log 3 - (l : ℝ) * Real.log 3 := by
      calc
        (1 : ℝ) < Real.log 3 := one_lt_log_three
        _ ≤ ((k : ℝ) - (l : ℝ)) * Real.log 3 := hmul
        _ = (k : ℝ) * Real.log 3 - (l : ℝ) * Real.log 3 := by ring
    linarith

/-- The terminal interval imposed on the middle quarter of the three-block
argument. -/
def collatzMiddleInterval {r : ℕ} (a : ℝ) (v : Fin r → Bool) : Prop :=
  a ≤ wordIncrementSum collatzLogIncrement v ∧
    wordIncrementSum collatzLogIncrement v < a + 1

noncomputable def collatzMiddleIntervalIndicator
    {r : ℕ} (a : ℝ) (v : Fin r → Bool) : ℝ := by
  classical
  exact if collatzMiddleInterval a v then 1 else 0

theorem collatzMiddleInterval_support_unique
    {r : ℕ} {a : ℝ} {v w : Fin r → Bool}
    (hv : collatzMiddleInterval a v)
    (hw : collatzMiddleInterval a w) :
    (boolSupport v).card = (boolSupport w).card := by
  unfold collatzMiddleInterval at hv hw
  rw [wordIncrementSum_collatz] at hv hw
  apply collatz_support_unique_in_unit_interval
      (a := a + (r : ℝ) * Real.log 2)
  · linarith [hv.1]
  · linarith [hv.2]
  · linarith [hw.1]
  · linarith [hw.2]

/-- Critical Bernoulli tilt `p_* = log 2 / log 3`. -/
def collatzTilt : ℝ := Real.log 2 / Real.log 3

theorem collatzTilt_pos : 0 < collatzTilt := by
  unfold collatzTilt
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

theorem collatzTilt_lt_one : collatzTilt < 1 := by
  unfold collatzTilt
  rw [div_lt_one (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
  exact Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
    (by norm_num)

theorem collatzTilt_half_lt : 1 / 2 < collatzTilt := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [collatzTilt, lt_div_iff₀ hlog3]
  have hlog : Real.log 3 < Real.log 4 :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 4))
      (by norm_num)
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)] at hlog
  nlinarith

theorem collatzTilt_lt_two_thirds : collatzTilt < 2 / 3 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [collatzTilt, div_lt_iff₀ hlog3]
  have hlog : Real.log 8 < Real.log 9 :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 8))
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 9))
      (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 * (2 * 2) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h8, h9] at hlog
  nlinarith

theorem collatzLogIncrement_abs_le_one (b : Bool) :
    |collatzLogIncrement b| ≤ 1 := by
  cases b with
  | false =>
      simp only [collatzLogIncrement, Bool.false_eq_true, if_false, abs_neg]
      rw [abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      have h := Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      norm_num at h
      exact h.le
  | true =>
      have hpos : 0 < Real.log 3 - Real.log 2 := by
        exact sub_pos.mpr (Real.strictMonoOn_log
          (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
          (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
          (by norm_num))
      simp only [collatzLogIncrement, if_true]
      rw [abs_of_pos hpos]
      have hdiv : Real.log 3 - Real.log 2 = Real.log (3 / 2 : ℝ) := by
        rw [Real.log_div (by norm_num) (by norm_num)]
      rw [hdiv]
      linarith [Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 3 / 2)
        (by norm_num : (3 / 2 : ℝ) ≠ 1)]

theorem collatzLogIncrement_centered :
    bernoulliAverage collatzTilt
      (collatzLogIncrement false) (collatzLogIncrement true) = 0 := by
  unfold bernoulliAverage collatzTilt collatzLogIncrement
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp only [Bool.false_eq_true, if_false, if_true]
  field_simp [hlog3]
  ring

/-- Variance of the centered Collatz tilted increment. -/
def collatzTiltVariance : ℝ :=
  bernoulliAverage collatzTilt
    ((collatzLogIncrement false) ^ 2)
    ((collatzLogIncrement true) ^ 2)

theorem collatzTiltVariance_pos : 0 < collatzTiltVariance := by
  have hp0 := collatzTilt_pos
  have hp1 := collatzTilt_lt_one
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold collatzTiltVariance bernoulliAverage collatzLogIncrement
  simp only [Bool.false_eq_true, if_false, if_true]
  have hlog2ne : -Real.log 2 ≠ 0 := neg_ne_zero.mpr hlog2.ne'
  have hfirst : 0 < (1 - collatzTilt) * (-Real.log 2) ^ 2 :=
    mul_pos (sub_pos.mpr hp1) (sq_pos_of_ne_zero hlog2ne)
  have hsecond : 0 ≤ collatzTilt * (Real.log 3 - Real.log 2) ^ 2 :=
    mul_nonneg hp0.le (sq_nonneg _)
  linarith

/-- Appendix B.1 specialized to the critical Collatz tilt. -/
theorem collatzLowerSurvivalMass_le
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass collatzTilt collatzLogIncrement (-B) n 0 ≤
      (1 + 2 / collatzTiltVariance) * (B + 1) / Real.sqrt n := by
  exact lowerSurvivalMass_le_centered
    collatzTilt_pos.le collatzTilt_lt_one.le collatzTiltVariance_pos hB
    collatzLogIncrement_abs_le_one collatzLogIncrement_centered rfl hn

/-- The same survival estimate for the reversed-negated terminal block. -/
theorem collatzNegLowerSurvivalMass_le
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass collatzTilt
        (fun b ↦ -collatzLogIncrement b) (-B) n 0 ≤
      (1 + 2 / collatzTiltVariance) * (B + 1) / Real.sqrt n := by
  apply lowerSurvivalMass_le_centered
    collatzTilt_pos.le collatzTilt_lt_one.le collatzTiltVariance_pos hB
      (x := fun b ↦ -collatzLogIncrement b)
  · intro b
    simpa only [abs_neg] using collatzLogIncrement_abs_le_one b
  · have hcenter := collatzLogIncrement_centered
    unfold bernoulliAverage at hcenter ⊢
    linarith
  · unfold collatzTiltVariance
    congr 1 <;> ring
  · exact hn

/-! ## Exact finite-word masses -/

/-- Product weight of a finite Boolean word under Bernoulli parameter `p`. -/
def bernoulliWordWeight {r : ℕ} (p : ℝ) (v : Fin r → Bool) : ℝ :=
  ∏ i, if v i then p else 1 - p

theorem bernoulliWordWeight_nonneg
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {r : ℕ} (v : Fin r → Bool) :
    0 ≤ bernoulliWordWeight p v := by
  unfold bernoulliWordWeight
  exact Finset.prod_nonneg fun i _hi ↦ by
    by_cases h : v i <;> simp [h, hp₀, sub_nonneg.mpr hp₁]

/-- Literal survival of the lower barrier by every vertex of a finite word. -/
def wordSurvivesFrom (lo : ℝ) (x : Bool → ℝ) :
    (r : ℕ) → ℝ → (Fin r → Bool) → Prop
  | 0, z, _ => lo ≤ z
  | r + 1, z, v =>
      lo ≤ z ∧ wordSurvivesFrom lo x r (z + x (v 0)) (fun i => v i.succ)

noncomputable def wordSurvivalIndicator
    {r : ℕ} (lo : ℝ) (x : Bool → ℝ) (z : ℝ) (v : Fin r → Bool) : ℝ := by
  classical
  exact if wordSurvivesFrom lo x r z v then 1 else 0

theorem wordSurvivalIndicator_nonneg
    {r : ℕ} (lo : ℝ) (x : Bool → ℝ) (z : ℝ) (v : Fin r → Bool) :
    0 ≤ wordSurvivalIndicator lo x z v := by
  classical
  unfold wordSurvivalIndicator
  split <;> norm_num

/-! The list bridge below is used only to reverse a finite terminal block.
It keeps the proof finite and avoids introducing an infinite random-walk
model. -/

def listIncrementSum (x : Bool → ℝ) (l : List Bool) : ℝ :=
  (l.map x).sum

def listSurvivesFrom (lo : ℝ) (x : Bool → ℝ) : ℝ → List Bool → Prop
  | z, [] => lo ≤ z
  | z, b :: l => lo ≤ z ∧ listSurvivesFrom lo x (z + x b) l

@[simp] theorem listIncrementSum_nil (x : Bool → ℝ) :
    listIncrementSum x [] = 0 := rfl

@[simp] theorem listIncrementSum_cons (x : Bool → ℝ) (b : Bool)
    (l : List Bool) :
    listIncrementSum x (b :: l) = x b + listIncrementSum x l := by
  simp [listIncrementSum]

@[simp] theorem listIncrementSum_append (x : Bool → ℝ)
    (l r : List Bool) :
    listIncrementSum x (l ++ r) =
      listIncrementSum x l + listIncrementSum x r := by
  simp [listIncrementSum]

theorem listIncrementSum_neg (x : Bool → ℝ) (l : List Bool) :
    listIncrementSum (fun b => -x b) l = -listIncrementSum x l := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [listIncrementSum_cons, listIncrementSum_cons, ih]
      ring

theorem listIncrementSum_reverse (x : Bool → ℝ) (l : List Bool) :
    listIncrementSum x l.reverse = listIncrementSum x l := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [List.reverse_cons, listIncrementSum_append, ih]
      simp
      ring

theorem listSurvivesFrom_initial
    {lo z : ℝ} {x : Bool → ℝ} {l : List Bool}
    (h : listSurvivesFrom lo x z l) : lo ≤ z := by
  cases l with
  | nil => exact h
  | cons b l => exact h.1

theorem listSurvivesFrom_append (lo : ℝ) (x : Bool → ℝ)
    (z : ℝ) (l r : List Bool) :
    listSurvivesFrom lo x z (l ++ r) ↔
      listSurvivesFrom lo x z l ∧
        listSurvivesFrom lo x (z + listIncrementSum x l) r := by
  induction l generalizing z with
  | nil =>
      constructor
      · intro h
        exact ⟨listSurvivesFrom_initial h, by simpa using h⟩
      · rintro ⟨_hz, h⟩
        simpa using h
  | cons b l ih =>
      simp only [List.cons_append, listSurvivesFrom,
        listIncrementSum_cons]
      change
        (lo ≤ z ∧ listSurvivesFrom lo x (z + x b) (l ++ r)) ↔
          (lo ≤ z ∧ listSurvivesFrom lo x (z + x b) l) ∧
            listSurvivesFrom lo x
              (z + (x b + listIncrementSum x l)) r
      rw [ih (z + x b)]
      constructor
      · rintro ⟨hz, hl, hr⟩
        exact ⟨⟨hz, hl⟩, by convert hr using 1 <;> ring⟩
      · rintro ⟨⟨hz, hl⟩, hr⟩
        exact ⟨hz, hl, by convert hr using 1 <;> ring⟩

/-- If a word remains above `lo` and ends below `hi`, its reversed-negated
word remains above `lo-hi`.  This is the deterministic source of the second
outer-block survival condition. -/
theorem listSurvivesFrom_reverse_neg
    {lo hi z : ℝ} {x : Bool → ℝ} {l : List Bool}
    (hs : listSurvivesFrom lo x z l)
    (ht : z + listIncrementSum x l < hi) :
    listSurvivesFrom (lo - hi) (fun b => -x b) 0 l.reverse := by
  induction l generalizing z with
  | nil =>
      have hz : lo ≤ z := hs
      rw [listIncrementSum_nil] at ht
      change lo - hi ≤ 0
      linarith
  | cons b l ih =>
      rcases hs with ⟨hz, hs⟩
      rw [List.reverse_cons, listSurvivesFrom_append]
      have ht' : z + x b + listIncrementSum x l < hi := by
        simpa [listIncrementSum_cons, add_assoc] using ht
      have hrev := ih hs ht'
      constructor
      · exact hrev
      · have hstart := listSurvivesFrom_initial hs
        have hbefore : listIncrementSum x l + lo ≤ hi := by
          linarith
        have hfinal : listIncrementSum x l + (lo - hi) ≤ -x b := by
          linarith
        simpa [listSurvivesFrom, listIncrementSum_reverse,
          listIncrementSum_neg, add_comm, add_left_comm, add_assoc] using
            And.intro hbefore hfinal

theorem wordSurvivesFrom_iff_list
    {r : ℕ} (lo : ℝ) (x : Bool → ℝ) (z : ℝ) (v : Fin r → Bool) :
    wordSurvivesFrom lo x r z v ↔
      listSurvivesFrom lo x z (List.ofFn v) := by
  induction r generalizing z with
  | zero => simp [wordSurvivesFrom, listSurvivesFrom]
  | succ r ih =>
      rw [List.ofFn_succ]
      simp only [wordSurvivesFrom, listSurvivesFrom]
      rw [ih]

theorem ofFn_rev {r : ℕ} (v : Fin r → Bool) :
    List.ofFn (fun i => v (Fin.rev i)) = (List.ofFn v).reverse := by
  apply List.ext_get
  · simp
  · intro n hleft hright
    simp only [List.length_ofFn] at hleft
    rw [List.get_reverse']
    · simp only [List.get_ofFn]
      congr
      apply Fin.ext
      simp [Fin.rev]
      omega
    · simp
      omega

theorem wordIncrementSum_eq_list
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum x v = listIncrementSum x (List.ofFn v) := by
  induction r with
  | zero => simp [wordIncrementSum, listIncrementSum]
  | succ r ih =>
      rw [wordIncrementSum, Fin.sum_univ_succ, List.ofFn_succ,
        listIncrementSum_cons]
      change x (v 0) + (∑ i : Fin r, x (v i.succ)) =
        x (v 0) + listIncrementSum x (List.ofFn fun i => v i.succ)
      have htail := ih (fun i => v i.succ)
      unfold wordIncrementSum at htail
      rw [htail]

theorem wordIncrementSum_rev
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum x (fun i => v (Fin.rev i)) =
      wordIncrementSum x v := by
  rw [wordIncrementSum_eq_list, ofFn_rev, listIncrementSum_reverse,
    ← wordIncrementSum_eq_list]

/-- The prefix of length `j` of a word of length `r`. -/
def wordPrefix {r : ℕ} (v : Fin r → Bool) (j : Fin (r + 1)) :
    Fin j → Bool :=
  fun i => v (Fin.castLE (Nat.le_of_lt_succ j.isLt) i)

@[simp] theorem wordIncrementSum_wordPrefix_zero
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum x (wordPrefix v (0 : Fin (r + 1))) = 0 := by
  unfold wordIncrementSum
  apply Finset.sum_eq_zero
  intro i _hi
  exact Fin.elim0 i

theorem wordIncrementSum_wordPrefix_succ
    {r : ℕ} (x : Bool → ℝ) (v : Fin (r + 1) → Bool)
    (j : Fin (r + 1)) :
    wordIncrementSum x (wordPrefix v j.succ) =
      x (v 0) + wordIncrementSum x
        (wordPrefix (fun i => v i.succ) j) := by
  rw [show wordPrefix v j.succ = Fin.cons (v 0)
      (wordPrefix (fun i => v i.succ) j) by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [wordPrefix]
    · intro k
      simp [wordPrefix]]
  rw [wordIncrementSum_cons]

/-- A lower bound at every finite prefix is exactly the input needed for the
recursive survival predicate. -/
theorem wordSurvivesFrom_of_prefix
    {r : ℕ} {lo z : ℝ} {x : Bool → ℝ} {v : Fin r → Bool}
    (h : ∀ j : Fin (r + 1),
      lo ≤ z + wordIncrementSum x (wordPrefix v j)) :
    wordSurvivesFrom lo x r z v := by
  induction r generalizing z with
  | zero =>
      simpa [wordSurvivesFrom] using h (0 : Fin 1)
  | succ r ih =>
      constructor
      · simpa only [wordIncrementSum_wordPrefix_zero, add_zero] using
          h (0 : Fin (r + 2))
      · apply ih
        intro j
        have hj := h j.succ
        rw [wordIncrementSum_wordPrefix_succ] at hj
        linarith

/-- Exact finite product mass of lower-barrier-surviving words. -/
noncomputable def weightedSurvivalWordMass
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) (r : ℕ) (z : ℝ) : ℝ := by
  classical
  exact ∑ v : Fin r → Bool,
    bernoulliWordWeight p v * if wordSurvivesFrom lo x r z v then 1 else 0

@[simp] theorem bernoulliWordWeight_cons
    {p : ℝ} {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    bernoulliWordWeight p (Fin.cons b w) =
      (if b then p else 1 - p) * bernoulliWordWeight p w := by
  unfold bernoulliWordWeight
  rw [Fin.prod_univ_succ]
  simp

@[simp] theorem bernoulliWordWeight_append
    {p : ℝ} {r s : ℕ} (v : Fin r → Bool) (w : Fin s → Bool) :
    bernoulliWordWeight p (Fin.append v w) =
      bernoulliWordWeight p v * bernoulliWordWeight p w := by
  unfold bernoulliWordWeight
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _hi
    simp [Fin.append]
  · apply Finset.prod_congr rfl
    intro i _hi
    simp [Fin.append]

/-- Reversing a finite word preserves its Bernoulli product weight. -/
theorem bernoulliWordWeight_rev
    {p : ℝ} {a : ℕ} (w : Fin a → Bool) :
    bernoulliWordWeight p (fun i => w (Fin.rev i)) =
      bernoulliWordWeight p w := by
  unfold bernoulliWordWeight
  exact Equiv.prod_comp Fin.revPerm
    (fun i => if w i then p else 1 - p)

/-- Bernoulli word weights have total mass one, proved on the finite word
tree rather than through a measure-theoretic product-space interface. -/
theorem sum_bernoulliWordWeight_eq_one (p : ℝ) :
    ∀ r : ℕ, ∑ v : Fin r → Bool, bernoulliWordWeight p v = 1 := by
  intro r
  induction r with
  | zero => simp [bernoulliWordWeight]
  | succ r ihr =>
      rw [← Equiv.sum_comp
        (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_bool]
      change
        (∑ w : Fin r → Bool, bernoulliWordWeight p (Fin.cons true w)) +
          ∑ w : Fin r → Bool, bernoulliWordWeight p (Fin.cons false w) = 1
      simp only [bernoulliWordWeight_cons, if_true, if_false]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ihr]
      norm_num

theorem bernoulliWordWeight_eq_support_card
    {p : ℝ} {r : ℕ} (v : Fin r → Bool) :
    bernoulliWordWeight p v =
      p ^ (boolSupport v).card *
        (1 - p) ^ (r - (boolSupport v).card) := by
  classical
  unfold bernoulliWordWeight boolSupport
  rw [show (∏ i : Fin r, if v i then p else 1 - p) =
      ∏ i ∈ (Finset.univ : Finset (Fin r)),
        if v i = true then p else 1 - p by simp]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin r))) (fun i => v i = true)
  have huniv : (Finset.univ : Finset (Fin r)).card = r := by simp
  rw [huniv] at hcard
  have hfalse :
      ((Finset.univ : Finset (Fin r)).filter
        (fun i => ¬v i = true)).card =
        r - ((Finset.univ : Finset (Fin r)).filter
          (fun i => v i = true)).card := by
    omega
  rw [hfalse]

theorem card_boolWords_support_eq (n k : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun v => (boolSupport v).card = k)).card = n.choose k := by
  classical
  let e :
      {v : Fin n → Bool // (boolSupport v).card = k} ≃
        {s : Finset (Fin n) // s.card = k} :=
    (boolWordFinsetEquiv n).subtypeEquiv (fun _ => Iff.rfl)
  have hc := Fintype.card_congr e
  have hfinsets :
      ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun s => s.card = k)) =
        (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext s
    simp [Finset.mem_powersetCard]
  simpa [Fintype.card_subtype, hfinsets, Finset.card_powersetCard] using hc

/-- Exact tilted mass carried by Boolean words with `k` true letters. -/
theorem sum_bernoulliWordWeight_support_eq
    (p : ℝ) (n k : ℕ) :
    ∑ v : Fin n → Bool,
        bernoulliWordWeight p v *
          (if (boolSupport v).card = k then 1 else 0) =
      tiltedBinomialMass p n k := by
  classical
  rw [show (∑ v : Fin n → Bool,
        bernoulliWordWeight p v *
          (if (boolSupport v).card = k then 1 else 0)) =
      ∑ v : Fin n → Bool,
        if (boolSupport v).card = k then
          p ^ k * (1 - p) ^ (n - k) else 0 by
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases hcard : (boolSupport v).card = k
    · simp only [hcard, if_true, mul_one]
      rw [bernoulliWordWeight_eq_support_card, hcard]
    · simp [hcard]]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_boolWords_support_eq]
  unfold tiltedBinomialMass
  norm_cast
  ring

/-- The middle-block terminal interval costs at most one tilted binomial
atom.  This is the lattice component of the three-block timeout estimate. -/
theorem exists_collatzMiddleIntervalMass_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ a : ℝ, 0 < n →
      ∑ v : Fin n → Bool,
          bernoulliWordWeight collatzTilt v *
            collatzMiddleIntervalIndicator a v ≤
        C / Real.sqrt n := by
  obtain ⟨C, hC, hAtom⟩ :=
    exists_tiltedBinomialMass_le_sqrt
      collatzTilt_half_lt collatzTilt_lt_two_thirds
  refine ⟨C, hC, ?_⟩
  intro n a hn
  classical
  by_cases hex : ∃ v : Fin n → Bool, collatzMiddleInterval a v
  · obtain ⟨v₀, hv₀⟩ := hex
    let k₀ := (boolSupport v₀).card
    calc
      (∑ v : Fin n → Bool,
          bernoulliWordWeight collatzTilt v *
            collatzMiddleIntervalIndicator a v) ≤
          ∑ v : Fin n → Bool,
            bernoulliWordWeight collatzTilt v *
              (if (boolSupport v).card = k₀ then 1 else 0) := by
            apply Finset.sum_le_sum
            intro v _hv
            by_cases hinterval : collatzMiddleInterval a v
            · have hcard : (boolSupport v).card = k₀ := by
                exact collatzMiddleInterval_support_unique hinterval hv₀
              simp [collatzMiddleIntervalIndicator, hinterval, hcard]
            · simp only [collatzMiddleIntervalIndicator, hinterval,
                if_false, mul_zero, zero_le]
              exact mul_nonneg
                (bernoulliWordWeight_nonneg
                  collatzTilt_pos.le collatzTilt_lt_one.le v)
                (by split <;> norm_num)
      _ = tiltedBinomialMass collatzTilt n k₀ :=
        sum_bernoulliWordWeight_support_eq collatzTilt n k₀
      _ ≤ C / Real.sqrt n := hAtom n k₀ hn
  · have hzero :
        (∑ v : Fin n → Bool,
          bernoulliWordWeight collatzTilt v *
            collatzMiddleIntervalIndicator a v) = 0 := by
        apply Finset.sum_eq_zero
        intro v _hv
        have hv : ¬collatzMiddleInterval a v := by
          intro hv
          exact hex ⟨v, hv⟩
        simp [collatzMiddleIntervalIndicator, hv]
    rw [hzero]
    exact div_nonneg hC.le (Real.sqrt_nonneg _)

@[simp] theorem wordSurvivesFrom_cons
    {lo : ℝ} {x : Bool → ℝ} {r : ℕ} {z : ℝ}
    (b : Bool) (w : Fin r → Bool) :
    wordSurvivesFrom lo x (r + 1) z (Fin.cons b w) ↔
      lo ≤ z ∧ wordSurvivesFrom lo x r (z + x b) w := by
  simp [wordSurvivesFrom]

theorem weightedSurvivalWordMass_succ
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) (r : ℕ) (z : ℝ) :
    weightedSurvivalWordMass p x lo (r + 1) z =
      if lo ≤ z then bernoulliAverage p
        (weightedSurvivalWordMass p x lo r (z + x false))
        (weightedSurvivalWordMass p x lo r (z + x true))
      else 0 := by
  classical
  rw [weightedSurvivalWordMass]
  rw [← Equiv.sum_comp
    (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
  rw [Fintype.sum_prod_type]
  by_cases hz : lo ≤ z
  · simp [Fin.consEquiv, wordSurvivesFrom, hz, bernoulliWordWeight_cons,
      weightedSurvivalWordMass, bernoulliAverage, Finset.mul_sum]
    ring
  · simp [Fin.consEquiv, wordSurvivesFrom, hz]

theorem weightedSurvivalWordMass_eq_lowerSurvivalMass
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) :
    ∀ r z, weightedSurvivalWordMass p x lo r z =
      lowerSurvivalMass p x lo r z := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hz : lo ≤ z <;>
        simp [weightedSurvivalWordMass, bernoulliWordWeight,
          wordSurvivesFrom, lowerSurvivalMass, hz]
  | succ r ihr =>
      intro z
      rw [weightedSurvivalWordMass_succ, lowerSurvivalMass]
      split
      · rw [ihr, ihr]
      · rfl

/-! ## The three-block tilted envelope -/

noncomputable def collatzMiddleIntervalMass (n : ℕ) (a : ℝ) : ℝ :=
  ∑ v : Fin n → Bool,
    bernoulliWordWeight collatzTilt v * collatzMiddleIntervalIndicator a v

theorem collatzMiddleIntervalMass_nonneg (n : ℕ) (a : ℝ) :
    0 ≤ collatzMiddleIntervalMass n a := by
  unfold collatzMiddleIntervalMass
  exact Finset.sum_nonneg fun v _hv ↦
    mul_nonneg
      (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le v)
      (by
        classical
        unfold collatzMiddleIntervalIndicator
        split <;> norm_num)

theorem exists_collatzMiddleIntervalMass_uniform_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ a : ℝ, 0 < n →
      collatzMiddleIntervalMass n a ≤ C / Real.sqrt n := by
  simpa [collatzMiddleIntervalMass] using
    exists_collatzMiddleIntervalMass_le_sqrt

/-- Exponential tilt parameter used to compare fair word mass with the
critical Bernoulli product mass. -/
def collatzTiltLambda : ℝ :=
  (Real.log collatzTilt - Real.log (1 - collatzTilt)) / Real.log 3

/-- Natural-log decay rate in the exact fair-to-critical change of finite
word weights.  It is identified with the paper's entropy rate downstream. -/
def collatzFairTiltRate : ℝ :=
  collatzTiltLambda * Real.log 2 + Real.log 2 + Real.log (1 - collatzTilt)

theorem collatzTiltLambda_pos : 0 < collatzTiltLambda := by
  unfold collatzTiltLambda
  apply div_pos
  · apply sub_pos.mpr
    exact Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (sub_pos.mpr collatzTilt_lt_one))
      (Set.mem_Ioi.mpr collatzTilt_pos)
      (by linarith [collatzTilt_half_lt])
  · exact Real.log_pos (by norm_num)

theorem exists_collatzTiltTerminalSeries_bound :
    ∃ S : ℝ, 0 < S ∧ ∀ Q : ℕ,
      ∑ q ∈ Finset.range Q,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) ≤ S := by
  have hsum1 : Summable (fun q : ℕ ↦
      (q : ℝ) * Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    simpa [mul_comm] using
      (Real.summable_pow_mul_exp_neg_nat_mul 1 collatzTiltLambda_pos)
  have hsum0 : Summable (fun q : ℕ ↦
      Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    simpa using
      (Real.summable_pow_mul_exp_neg_nat_mul 0 collatzTiltLambda_pos)
  have hsum : Summable (fun q : ℕ ↦
      ((q : ℝ) + 2) *
        Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    convert hsum1.add (hsum0.mul_left 2) using 1
    funext q
    ring
  let S := 1 + ∑' q : ℕ,
    ((q : ℝ) + 2) * Real.exp (-collatzTiltLambda * (q : ℝ))
  have htsum : 0 ≤ ∑' q : ℕ,
      ((q : ℝ) + 2) * Real.exp (-collatzTiltLambda * (q : ℝ)) := by
    exact tsum_nonneg fun q ↦
      mul_nonneg (by positivity) (Real.exp_pos _).le
  refine ⟨S, by dsimp [S]; linarith, ?_⟩
  intro Q
  have hpartial :
      ∑ q ∈ Finset.range Q,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) ≤
        ∑' q : ℕ,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) := by
    exact hsum.sum_le_tsum (Finset.range Q)
      (fun q _hq ↦ mul_nonneg (by positivity) (Real.exp_pos _).le)
  dsimp [S]
  linarith

theorem collatzFairTiltRate_eq_entropy :
    collatzFairTiltRate = Real.log 2 - Real.binEntropy collatzTilt := by
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold collatzFairTiltRate collatzTiltLambda Real.binEntropy collatzTilt
  rw [Real.log_inv, Real.log_inv]
  field_simp [hlog3]
  ring

/-- Exact finite-word change of weights.  This is the algebraic identity
behind equation (B.5), stated without any infinite product measure. -/
theorem fair_word_weight_change {m : ℕ} (v : Fin m → Bool) :
    (1 / 2 : ℝ) ^ m =
      bernoulliWordWeight collatzTilt v *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) := by
  have hp : 0 < collatzTilt := collatzTilt_pos
  have hp1 : 0 < 1 - collatzTilt := sub_pos.mpr collatzTilt_lt_one
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  rw [bernoulliWordWeight_eq_support_card, wordIncrementSum_collatz]
  rw [show (1 / 2 : ℝ) ^ m =
      Real.exp ((m : ℝ) * Real.log (1 / 2 : ℝ)) by
    calc
      (1 / 2 : ℝ) ^ m = Real.exp (Real.log (1 / 2 : ℝ)) ^ m := by
        rw [Real.exp_log hhalf]
      _ = Real.exp ((m : ℝ) * Real.log (1 / 2 : ℝ)) :=
        (Real.exp_nat_mul _ _).symm]
  rw [show collatzTilt ^ (boolSupport v).card =
      Real.exp (((boolSupport v).card : ℝ) * Real.log collatzTilt) by
    calc
      collatzTilt ^ (boolSupport v).card =
          Real.exp (Real.log collatzTilt) ^ (boolSupport v).card := by
        rw [Real.exp_log hp]
      _ = Real.exp (((boolSupport v).card : ℝ) * Real.log collatzTilt) :=
        (Real.exp_nat_mul _ _).symm]
  rw [show (1 - collatzTilt) ^ (m - (boolSupport v).card) =
      Real.exp (((m - (boolSupport v).card : ℕ) : ℝ) *
        Real.log (1 - collatzTilt)) by
    calc
      (1 - collatzTilt) ^ (m - (boolSupport v).card) =
          Real.exp (Real.log (1 - collatzTilt)) ^
            (m - (boolSupport v).card) := by
        rw [Real.exp_log hp1]
      _ = Real.exp (((m - (boolSupport v).card : ℕ) : ℝ) *
          Real.log (1 - collatzTilt)) :=
        (Real.exp_nat_mul _ _).symm]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  have hcard : (boolSupport v).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (boolSupport v))
  rw [Nat.cast_sub hcard]
  unfold collatzFairTiltRate collatzTiltLambda
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog3]
  ring

theorem bernoulliWordWeight_half_eq {m : ℕ} (v : Fin m → Bool) :
    bernoulliWordWeight (1 / 2) v = (1 / 2 : ℝ) ^ m := by
  rw [bernoulliWordWeight_eq_support_card]
  norm_num only [one_div, one_sub_div, Nat.cast_ofNat]
  rw [← pow_add]
  congr 1
  have hcard : (boolSupport v).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (boolSupport v))
  omega

theorem fair_bernoulliWordWeight_change {m : ℕ} (v : Fin m → Bool) :
    bernoulliWordWeight (1 / 2) v =
      bernoulliWordWeight collatzTilt v *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) := by
  rw [bernoulliWordWeight_half_eq]
  exact fair_word_weight_change v

/-- Pointwise three-block form of the fair-to-critical tilt.  A lower bound
on the combined terminal sum gives the exponential bin weight. -/
theorem fair_three_word_weight_le
    {a b : ℕ} {center : ℝ}
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool)
    (hterminal : center ≤
      wordIncrementSum collatzLogIncrement u +
        wordIncrementSum collatzLogIncrement v +
        wordIncrementSum collatzLogIncrement w) :
    bernoulliWordWeight (1 / 2) u *
        bernoulliWordWeight (1 / 2) v *
        bernoulliWordWeight (1 / 2) w ≤
      (bernoulliWordWeight collatzTilt u *
        bernoulliWordWeight collatzTilt v *
        bernoulliWordWeight collatzTilt w) *
      Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * center) := by
  have htilt : 0 ≤
      bernoulliWordWeight collatzTilt u *
        bernoulliWordWeight collatzTilt v *
        bernoulliWordWeight collatzTilt w := by
    exact mul_nonneg
      (mul_nonneg
        (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le u)
        (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le v))
      (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le w)
  have hexp :
      -(collatzFairTiltRate * (a : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement u +
        (-(collatzFairTiltRate * (b : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) +
        (-(collatzFairTiltRate * (a : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement w) ≤
      -(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * center := by
    have hmul := mul_le_mul_of_nonneg_left hterminal collatzTiltLambda_pos.le
    push_cast
    linarith
  rw [fair_bernoulliWordWeight_change u,
    fair_bernoulliWordWeight_change v,
    fair_bernoulliWordWeight_change w]
  calc
    _ = (bernoulliWordWeight collatzTilt u *
          bernoulliWordWeight collatzTilt v *
          bernoulliWordWeight collatzTilt w) *
        Real.exp (
          (-(collatzFairTiltRate * (a : ℝ)) -
            collatzTiltLambda * wordIncrementSum collatzLogIncrement u) +
          (-(collatzFairTiltRate * (b : ℝ)) -
            collatzTiltLambda * wordIncrementSum collatzLogIncrement v) +
          (-(collatzFairTiltRate * (a : ℝ)) -
            collatzTiltLambda * wordIncrementSum collatzLogIncrement w)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) htilt

noncomputable def weightedSurvivalFactor
    (p : ℝ) (x : Bool → ℝ) (lo z : ℝ) {r : ℕ} (v : Fin r → Bool) : ℝ :=
  bernoulliWordWeight p v * wordSurvivalIndicator lo x z v

theorem weightedSurvivalFactor_nonneg
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo z : ℝ) {r : ℕ} (v : Fin r → Bool) :
    0 ≤ weightedSurvivalFactor p x lo z v :=
  mul_nonneg (bernoulliWordWeight_nonneg hp₀ hp₁ v)
    (wordSurvivalIndicator_nonneg lo x z v)

theorem sum_weightedSurvivalFactor_eq
    (p : ℝ) (x : Bool → ℝ) (lo z : ℝ) (r : ℕ) :
    ∑ v : Fin r → Bool, weightedSurvivalFactor p x lo z v =
      weightedSurvivalWordMass p x lo r z := by
  classical
  unfold weightedSurvivalFactor wordSurvivalIndicator weightedSurvivalWordMass
  rfl

/-- Product mass of the first-survival, reversed-last-survival, and
middle-interval envelope.  The last word is already written in reversed
order, which preserves its Bernoulli weight. -/
noncomputable def collatzThreeBlockEnvelopeMass
    (a b : ℕ) (B q center : ℝ) : ℝ :=
  ∑ u : Fin a → Bool,
    weightedSurvivalFactor collatzTilt collatzLogIncrement (-B) 0 u *
      ∑ w : Fin a → Bool,
        weightedSurvivalFactor collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
          collatzMiddleIntervalMass b
            (center - wordIncrementSum collatzLogIncrement u +
              wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w)

/-- The finite three-block envelope has the `a⁻¹ b⁻¹ʲ` mass predicted by
two outer survival estimates and one middle binomial atom. -/
theorem exists_collatzThreeBlockEnvelopeMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ a b : ℕ, ∀ B q center : ℝ,
        0 < a → 0 < b → 0 ≤ B → 0 ≤ q →
          collatzThreeBlockEnvelopeMass a b B q center ≤
            C * (B + 1) * (q + 2) /
              (Real.sqrt a * Real.sqrt a * Real.sqrt b) := by
  obtain ⟨Cmid, hCmid, hmid⟩ :=
    exists_collatzMiddleIntervalMass_uniform_le_sqrt
  let Csurv : ℝ := 1 + 2 / collatzTiltVariance
  have hCsurv : 0 < Csurv := by
    dsimp [Csurv]
    have hdiv : 0 < (2 : ℝ) / collatzTiltVariance :=
      div_pos (by norm_num) collatzTiltVariance_pos
    linarith
  refine ⟨Csurv ^ 2 * Cmid, mul_pos (sq_pos_of_pos hCsurv) hCmid, ?_⟩
  intro a b B q center ha hb hB hq
  have hsFirst :
      weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 ≤
        Csurv * (B + 1) / Real.sqrt a := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    simpa [Csurv] using collatzLowerSurvivalMass_le hB ha
  have hsLast :
      weightedSurvivalWordMass collatzTilt
          (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 ≤
        Csurv * (q + 2) / Real.sqrt a := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    dsimp [Csurv]
    convert collatzNegLowerSurvivalMass_le
      (B := q + 1) (by linarith) ha using 1
    all_goals ring
  have hfirstNonneg :
      0 ≤ weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    exact (lowerSurvivalMass_mem_unit collatzTilt_pos.le collatzTilt_lt_one.le
      collatzLogIncrement (-B) a 0).1
  have hlastNonneg :
      0 ≤ weightedSurvivalWordMass collatzTilt
        (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 := by
    rw [weightedSurvivalWordMass_eq_lowerSurvivalMass]
    exact (lowerSurvivalMass_mem_unit collatzTilt_pos.le collatzTilt_lt_one.le
      (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0).1
  have hinner : ∀ u : Fin a → Bool,
      (∑ w : Fin a → Bool,
        weightedSurvivalFactor collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
          collatzMiddleIntervalMass b
            (center - wordIncrementSum collatzLogIncrement u +
              wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w)) ≤
        weightedSurvivalWordMass collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
          (Cmid / Real.sqrt b) := by
    intro u
    calc
      (∑ w : Fin a → Bool,
        weightedSurvivalFactor collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
          collatzMiddleIntervalMass b
            (center - wordIncrementSum collatzLogIncrement u +
              wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w)) ≤
          ∑ w : Fin a → Bool,
            weightedSurvivalFactor collatzTilt
                (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) 0 w *
              (Cmid / Real.sqrt b) := by
            apply Finset.sum_le_sum
            intro w _hw
            exact mul_le_mul_of_nonneg_left (hmid b _ hb)
              (weightedSurvivalFactor_nonneg
                collatzTilt_pos.le collatzTilt_lt_one.le _ _ _ w)
      _ = weightedSurvivalWordMass collatzTilt
            (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
          (Cmid / Real.sqrt b) := by
            rw [← Finset.sum_mul, sum_weightedSurvivalFactor_eq]
  have hmass :
      collatzThreeBlockEnvelopeMass a b B q center ≤
        weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 *
          (weightedSurvivalWordMass collatzTilt
              (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
            (Cmid / Real.sqrt b)) := by
    unfold collatzThreeBlockEnvelopeMass
    calc
      _ ≤ ∑ u : Fin a → Bool,
          weightedSurvivalFactor collatzTilt collatzLogIncrement (-B) 0 u *
            (weightedSurvivalWordMass collatzTilt
                (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
              (Cmid / Real.sqrt b)) := by
            apply Finset.sum_le_sum
            intro u _hu
            exact mul_le_mul_of_nonneg_left (hinner u)
              (weightedSurvivalFactor_nonneg
                collatzTilt_pos.le collatzTilt_lt_one.le _ _ _ u)
      _ = _ := by
        rw [← Finset.sum_mul, sum_weightedSurvivalFactor_eq]
  have hCmidNonneg : 0 ≤ Cmid / Real.sqrt b :=
    div_nonneg hCmid.le (Real.sqrt_nonneg _)
  calc
    collatzThreeBlockEnvelopeMass a b B q center ≤
        weightedSurvivalWordMass collatzTilt collatzLogIncrement (-B) a 0 *
          (weightedSurvivalWordMass collatzTilt
              (fun bit ↦ -collatzLogIncrement bit) (-(q + 1)) a 0 *
            (Cmid / Real.sqrt b)) := hmass
    _ ≤ (Csurv * (B + 1) / Real.sqrt a) *
          ((Csurv * (q + 2) / Real.sqrt a) * (Cmid / Real.sqrt b)) := by
      gcongr
    _ = (Csurv ^ 2 * Cmid) * (B + 1) * (q + 2) /
          (Real.sqrt a * Real.sqrt a * Real.sqrt b) := by ring

/-- Necessary three-block conditions for a surviving word in terminal bin
`[q,q+1)`.  The final block is supplied in reversed order. -/
def collatzThreeBlockEnvelopeEvent
    {a b : ℕ} (B q : ℝ)
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) : Prop :=
  wordSurvivesFrom (-B) collatzLogIncrement a 0 u ∧
    wordSurvivesFrom (-(q + 1))
      (fun bit ↦ -collatzLogIncrement bit) a 0 w ∧
    collatzMiddleInterval
      (q - B - wordIncrementSum collatzLogIncrement u +
        wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w) v

/-- Reconstruct a full word from its first quarter, middle block, and the
reverse of its final quarter. -/
def collatzThreeBlockWord {a b : ℕ}
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) :
    Fin (a + (b + a)) → Bool :=
  Fin.append u (Fin.append v (fun i => w (Fin.rev i)))

/-- Reversal as a permutation of finite Boolean words. -/
def reverseBoolWordEquiv (a : ℕ) :
    (Fin a → Bool) ≃ (Fin a → Bool) :=
  Function.Involutive.toPerm
    (fun w : Fin a → Bool => fun i => w (Fin.rev i))
    (by
      intro w
      funext i
      simp)

/-- The unique first-block, reversed-last-block, middle-block coordinates,
ordered to match the nested sums in `collatzFullThreeBlockMass`. -/
def collatzThreeBlockSummationEquiv (a b : ℕ) :
    ((Fin a → Bool) × ((Fin a → Bool) × (Fin b → Bool))) ≃
      (Fin (a + (b + a)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.prodComm _ _).trans
        (Equiv.prodCongr (Equiv.refl _) (reverseBoolWordEquiv a)))).trans
    ((Equiv.prodCongr (Equiv.refl _) (Fin.appendEquiv b a)).trans
      (Fin.appendEquiv a (b + a)))

@[simp] theorem collatzThreeBlockSummationEquiv_apply
    {a b : ℕ}
    (u : Fin a → Bool) (w : Fin a → Bool) (v : Fin b → Bool) :
    collatzThreeBlockSummationEquiv a b (u, w, v) =
      collatzThreeBlockWord u v w := by
  simp [collatzThreeBlockSummationEquiv, reverseBoolWordEquiv,
    collatzThreeBlockWord]
  funext i
  rfl

theorem wordIncrementSum_collatzThreeBlockWord
    {a b : ℕ} (x : Bool → ℝ)
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) :
    wordIncrementSum x (collatzThreeBlockWord u v w) =
      wordIncrementSum x u + wordIncrementSum x v +
        wordIncrementSum x w := by
  simp [collatzThreeBlockWord, wordIncrementSum_rev, add_assoc]

/-- The literal full-word barrier-and-terminal-bin event. -/
def collatzFullBarrierBinEvent {m : ℕ} (B q : ℝ)
    (v : Fin m → Bool) : Prop :=
  wordSurvivesFrom (-B) collatzLogIncrement m 0 v ∧
    collatzMiddleInterval (q - B) v

/-- A full surviving word in terminal bin `[q-B,q-B+1)` satisfies the three
conditions used in the independent-block estimate. -/
theorem collatzThreeBlockEnvelopeEvent_of_full
    {a b : ℕ} {B q : ℝ}
    {u : Fin a → Bool} {v : Fin b → Bool} {w : Fin a → Bool}
    (hfull : collatzFullBarrierBinEvent B q
      (collatzThreeBlockWord u v w)) :
    collatzThreeBlockEnvelopeEvent B q u v w := by
  rcases hfull with ⟨hsurv, hterminal⟩
  have hslist : listSurvivesFrom (-B) collatzLogIncrement 0
      (List.ofFn u ++ List.ofFn v ++ (List.ofFn w).reverse) := by
    have h := (wordSurvivesFrom_iff_list (-B) collatzLogIncrement 0
      (collatzThreeBlockWord u v w)).mp hsurv
    simpa [collatzThreeBlockWord, ofFn_rev, List.append_assoc] using h
  have hfirstList : listSurvivesFrom (-B) collatzLogIncrement 0
      (List.ofFn u) :=
    ((listSurvivesFrom_append (-B) collatzLogIncrement 0
      (List.ofFn u) (List.ofFn v ++ (List.ofFn w).reverse)).mp
        (by simpa [List.append_assoc] using hslist)).1
  have hfirst : wordSurvivesFrom (-B) collatzLogIncrement a 0 u :=
    (wordSurvivesFrom_iff_list (-B) collatzLogIncrement 0 u).mpr
      hfirstList
  have hterminal' :
      q - B ≤ wordIncrementSum collatzLogIncrement u +
          wordIncrementSum collatzLogIncrement v +
          wordIncrementSum collatzLogIncrement w ∧
        wordIncrementSum collatzLogIncrement u +
          wordIncrementSum collatzLogIncrement v +
          wordIncrementSum collatzLogIncrement w < q - B + 1 := by
    simpa [collatzMiddleInterval, wordIncrementSum_collatzThreeBlockWord]
      using hterminal
  have htotalList :
      listIncrementSum collatzLogIncrement
          (List.ofFn u ++ List.ofFn v ++ (List.ofFn w).reverse) <
        q - B + 1 := by
    rw [listIncrementSum_append, listIncrementSum_append,
      listIncrementSum_reverse, ← wordIncrementSum_eq_list,
      ← wordIncrementSum_eq_list, ← wordIncrementSum_eq_list]
    linarith [hterminal'.2]
  have hrevList := listSurvivesFrom_reverse_neg hslist
    (hi := q - B + 1) (by simpa using htotalList)
  have hrevList' :
      listSurvivesFrom (-(q + 1))
        (fun bit => -collatzLogIncrement bit) 0
        (List.ofFn w ++
          ((List.ofFn v).reverse ++ (List.ofFn u).reverse)) := by
    convert hrevList using 1
    · ring
    · simp [List.reverse_append, List.append_assoc]
  have hlastList :
      listSurvivesFrom (-(q + 1))
        (fun bit => -collatzLogIncrement bit) 0 (List.ofFn w) :=
    ((listSurvivesFrom_append (-(q + 1))
      (fun bit => -collatzLogIncrement bit) 0 (List.ofFn w)
      ((List.ofFn v).reverse ++ (List.ofFn u).reverse)).mp hrevList').1
  have hlast :
      wordSurvivesFrom (-(q + 1))
        (fun bit => -collatzLogIncrement bit) a 0 w :=
    (wordSurvivesFrom_iff_list (-(q + 1))
      (fun bit => -collatzLogIncrement bit) 0 w).mpr hlastList
  refine ⟨hfirst, hlast, ?_⟩
  unfold collatzMiddleInterval
  rw [wordIncrementSum_neg]
  constructor <;> linarith [hterminal'.1, hterminal'.2]

noncomputable def collatzThreeBlockEnvelopeIndicator
    {a b : ℕ} (B q : ℝ)
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) : ℝ := by
  classical
  exact if collatzThreeBlockEnvelopeEvent B q u v w then 1 else 0

theorem collatzThreeBlockEnvelopeIndicator_nonneg
    {a b : ℕ} (B q : ℝ)
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) :
    0 ≤ collatzThreeBlockEnvelopeIndicator B q u v w := by
  classical
  unfold collatzThreeBlockEnvelopeIndicator
  split <;> norm_num

/-- Flat three-block product mass, used with `p=1/2` for fair words and
with `p=collatzTilt` after the exact change of weights. -/
noncomputable def collatzThreeBlockFlatMass
    (p : ℝ) (a b : ℕ) (B q : ℝ) : ℝ :=
  ∑ u : Fin a → Bool, ∑ w : Fin a → Bool, ∑ v : Fin b → Bool,
    (bernoulliWordWeight p u * bernoulliWordWeight p v *
      bernoulliWordWeight p w) *
        collatzThreeBlockEnvelopeIndicator B q u v w

noncomputable def collatzFullBarrierBinIndicator
    {m : ℕ} (B q : ℝ) (v : Fin m → Bool) : ℝ := by
  classical
  exact if collatzFullBarrierBinEvent B q v then 1 else 0

/-- Fair or tilted mass of the literal full-word event, written in its unique
three-block coordinates. -/
noncomputable def collatzFullThreeBlockMass
    (p : ℝ) (a b : ℕ) (B q : ℝ) : ℝ :=
  ∑ u : Fin a → Bool, ∑ w : Fin a → Bool, ∑ v : Fin b → Bool,
    (bernoulliWordWeight p u * bernoulliWordWeight p v *
      bernoulliWordWeight p w) *
        collatzFullBarrierBinIndicator B q
          (collatzThreeBlockWord u v w)

/-- The same literal event summed directly over full words. -/
noncomputable def collatzFullWordMass
    (p : ℝ) (m : ℕ) (B q : ℝ) : ℝ :=
  ∑ word : Fin m → Bool,
    bernoulliWordWeight p word * collatzFullBarrierBinIndicator B q word

/-- Splitting a full word into its two outer blocks and middle block preserves
the exact Bernoulli mass. -/
theorem collatzFullWordMass_eq_threeBlock
    (p : ℝ) (a b : ℕ) (B q : ℝ) :
    collatzFullWordMass p (a + (b + a)) B q =
      collatzFullThreeBlockMass p a b B q := by
  classical
  unfold collatzFullWordMass collatzFullThreeBlockMass
  rw [← (collatzThreeBlockSummationEquiv a b).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro w _hw
  apply Finset.sum_congr rfl
  intro v _hv
  rw [collatzThreeBlockSummationEquiv_apply]
  simp only [collatzThreeBlockWord, bernoulliWordWeight_append,
    bernoulliWordWeight_rev]
  ring

/-- Full surviving words form a subset of the three-block envelope. -/
theorem collatzFullThreeBlockMass_le_envelope
    (a b : ℕ) (B q : ℝ) :
    collatzFullThreeBlockMass (1 / 2) a b B q ≤
      collatzThreeBlockFlatMass (1 / 2) a b B q := by
  classical
  unfold collatzFullThreeBlockMass collatzThreeBlockFlatMass
  apply Finset.sum_le_sum
  intro u _hu
  apply Finset.sum_le_sum
  intro w _hw
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hfull : collatzFullBarrierBinEvent B q
      (collatzThreeBlockWord u v w)
  · have henv := collatzThreeBlockEnvelopeEvent_of_full hfull
    simp [collatzFullBarrierBinIndicator, hfull,
      collatzThreeBlockEnvelopeIndicator, henv]
  · simp [collatzFullBarrierBinIndicator, hfull]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) u)
          (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v))
        (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) w))
      (collatzThreeBlockEnvelopeIndicator_nonneg B q u v w)

theorem collatzThreeBlockFlatMass_tilt_eq
    (a b : ℕ) (B q : ℝ) :
    collatzThreeBlockFlatMass collatzTilt a b B q =
      collatzThreeBlockEnvelopeMass a b B q (q - B) := by
  classical
  unfold collatzThreeBlockFlatMass collatzThreeBlockEnvelopeMass
    weightedSurvivalFactor wordSurvivalIndicator collatzMiddleIntervalMass
    collatzMiddleIntervalIndicator collatzThreeBlockEnvelopeIndicator
    collatzThreeBlockEnvelopeEvent
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases hfirst : wordSurvivesFrom (-B) collatzLogIncrement a 0 u
  · simp only [hfirst, true_and, if_true, mul_one]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _hw
    by_cases hlast : wordSurvivesFrom (-(q + 1))
        (fun bit ↦ -collatzLogIncrement bit) a 0 w
    · simp only [hlast, true_and, if_true, mul_one]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hmid : collatzMiddleInterval
          (q - B - wordIncrementSum collatzLogIncrement u +
            wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w) v
      · simp [hmid]
        ring
      · simp [hmid]
    · simp only [hlast, false_and, if_false, mul_zero,
        Finset.sum_const_zero]
      ring
  · simp [hfirst]

/-- The fair mass of a terminal bin is its critical tilted envelope times
the exact exponential change-of-weight factor. -/
theorem collatzThreeBlockFlatMass_fair_le_tilt
    {a b : ℕ} {B q : ℝ} :
    collatzThreeBlockFlatMass (1 / 2) a b B q ≤
      Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * (q - B)) *
        collatzThreeBlockFlatMass collatzTilt a b B q := by
  classical
  unfold collatzThreeBlockFlatMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _hu
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _hw
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hevent : collatzThreeBlockEnvelopeEvent B q u v w
  · have hmid := hevent.2.2
    unfold collatzMiddleInterval at hmid
    have hneg := wordIncrementSum_neg collatzLogIncrement w
    have hterminal : q - B ≤
        wordIncrementSum collatzLogIncrement u +
          wordIncrementSum collatzLogIncrement v +
          wordIncrementSum collatzLogIncrement w := by
      linarith [hmid.1]
    have hw := fair_three_word_weight_le u v w hterminal
    simpa [collatzThreeBlockEnvelopeIndicator, hevent, mul_assoc,
      mul_comm, mul_left_comm] using hw
  · simp [collatzThreeBlockEnvelopeIndicator, hevent]

/-- Fair mass of one terminal bin.  This is the fully normalized finite-word
form of equation (B.6), before replacing the exact block sizes by `m/8` and
`m/2`. -/
theorem exists_collatzThreeBlockFairBinMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ a b : ℕ, ∀ B q : ℝ,
        0 < a → 0 < b → 0 ≤ B → 0 ≤ q →
          collatzThreeBlockFlatMass (1 / 2) a b B q ≤
            C * (B + 1) * (q + 2) /
                (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
              Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
                collatzTiltLambda * (q - B)) := by
  obtain ⟨C, hC, hEnvelope⟩ := exists_collatzThreeBlockEnvelopeMass_le
  refine ⟨C, hC, ?_⟩
  intro a b B q ha hb hB hq
  have htilt := hEnvelope a b B q (q - B) ha hb hB hq
  calc
    collatzThreeBlockFlatMass (1 / 2) a b B q ≤
        Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) *
          collatzThreeBlockFlatMass collatzTilt a b B q :=
      collatzThreeBlockFlatMass_fair_le_tilt
    _ = Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) *
          collatzThreeBlockEnvelopeMass a b B q (q - B) := by
      rw [collatzThreeBlockFlatMass_tilt_eq]
    _ ≤ Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) *
          (C * (B + 1) * (q + 2) /
            (Real.sqrt a * Real.sqrt a * Real.sqrt b)) :=
      mul_le_mul_of_nonneg_left htilt (Real.exp_pos _).le
    _ = C * (B + 1) * (q + 2) /
          (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
        Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) := by ring

/-- Summation of all terminal bins up to an arbitrary finite cutoff.  The
constant is independent of that cutoff. -/
theorem exists_sum_collatzThreeBlockFairBinMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ a b Q : ℕ, ∀ B : ℝ,
        0 < a → 0 < b → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzThreeBlockFlatMass (1 / 2) a b B q ≤
            C * (B + 1) /
                (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
              Real.exp (-(collatzFairTiltRate *
                ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B) := by
  obtain ⟨C₀, hC₀, hBin⟩ := exists_collatzThreeBlockFairBinMass_le
  obtain ⟨S, hS, hSeries⟩ := exists_collatzTiltTerminalSeries_bound
  refine ⟨C₀ * S, mul_pos hC₀ hS, ?_⟩
  intro a b Q B ha hb hB
  let D : ℝ := Real.sqrt a * Real.sqrt a * Real.sqrt b
  let K : ℝ := C₀ * (B + 1) / D *
    Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) +
      collatzTiltLambda * B)
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos
      (mul_pos (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_pos.2 (by positivity)))
      (Real.sqrt_pos.2 (by positivity))
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ q ∈ Finset.range Q,
      collatzThreeBlockFlatMass (1 / 2) a b B q ≤
        K * (((q : ℝ) + 2) *
          Real.exp (-collatzTiltLambda * (q : ℝ))) := by
    intro q _hq
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hqBin := hBin a b B (q : ℝ) ha hb hB hq
    have hexp :
        Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
            collatzTiltLambda * ((q : ℝ) - B)) =
          Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) +
              collatzTiltLambda * B) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hqBin
    dsimp [K, D]
    calc
      collatzThreeBlockFlatMass (1 / 2) a b B (q : ℝ) ≤
          C₀ * (B + 1) * ((q : ℝ) + 2) /
              (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
            (Real.exp (-(collatzFairTiltRate *
                ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B) *
              Real.exp (-collatzTiltLambda * (q : ℝ))) := hqBin
      _ = (C₀ * (B + 1) /
              (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
            Real.exp (-(collatzFairTiltRate *
                ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B)) *
          (((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ))) := by ring
  calc
    (∑ q ∈ Finset.range Q,
        collatzThreeBlockFlatMass (1 / 2) a b B q) ≤
        ∑ q ∈ Finset.range Q,
          K * (((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ))) :=
      Finset.sum_le_sum hpoint
    _ = K * (∑ q ∈ Finset.range Q,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ K * S := mul_le_mul_of_nonneg_left (hSeries Q) hK
    _ = (C₀ * S) * (B + 1) /
          (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
        Real.exp (-(collatzFairTiltRate *
          ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B) := by
      dsimp [K, D]
      ring

/-! ### Quarter-scale specialization -/

/-- Outer block length in the canonical three-block decomposition. -/
def collatzBallotOuterLength (m : ℕ) : ℕ := m / 4

/-- Middle block length left after removing two equal outer quarters. -/
def collatzBallotMiddleLength (m : ℕ) : ℕ :=
  m - 2 * collatzBallotOuterLength m

theorem collatzBallot_split (m : ℕ) :
    2 * collatzBallotOuterLength m + collatzBallotMiddleLength m = m := by
  simp only [collatzBallotMiddleLength, collatzBallotOuterLength]
  have h : m / 4 * 4 ≤ m := Nat.div_mul_le_self m 4
  omega

theorem collatzBallotOuterLength_pos {m : ℕ} (hm : 8 ≤ m) :
    0 < collatzBallotOuterLength m := by
  unfold collatzBallotOuterLength
  omega

theorem collatzBallotMiddleLength_pos {m : ℕ} (hm : 8 ≤ m) :
    0 < collatzBallotMiddleLength m := by
  simp only [collatzBallotMiddleLength, collatzBallotOuterLength]
  have h : m / 4 * 4 ≤ m := Nat.div_mul_le_self m 4
  omega

theorem collatzBallotOuterLength_lower {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) / 8 ≤ collatzBallotOuterLength m := by
  have hle : m < 4 * (m / 4 + 1) :=
    Nat.lt_mul_div_succ m (by omega : 0 < 4)
  have hnat : m ≤ 8 * (m / 4) := by omega
  have hreal : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simp only [collatzBallotOuterLength]
  norm_num at hreal ⊢
  linarith

theorem collatzBallotMiddleLength_lower {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) / 4 ≤ collatzBallotMiddleLength m := by
  simp only [collatzBallotMiddleLength, collatzBallotOuterLength]
  have h : m / 4 * 4 ≤ m := Nat.div_mul_le_self m 4
  have hnat : m ≤ 4 * (m - 2 * (m / 4)) := by omega
  have hreal : (m : ℝ) ≤ 4 * ((m - 2 * (m / 4) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  linarith

/-- The exact square-root denominator supplied by the quarter-scale split is
bounded below by `m^(3/2)/16`. -/
theorem collatzBallot_denominator_lower {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) * Real.sqrt m / 16 ≤
      Real.sqrt (collatzBallotOuterLength m) *
        Real.sqrt (collatzBallotOuterLength m) *
          Real.sqrt (collatzBallotMiddleLength m) := by
  have ha : (m : ℝ) / 8 ≤ collatzBallotOuterLength m :=
    collatzBallotOuterLength_lower hm
  have hb : (m : ℝ) / 4 ≤ collatzBallotMiddleLength m :=
    collatzBallotMiddleLength_lower hm
  have hsqrtb : Real.sqrt ((m : ℝ) / 4) ≤
      Real.sqrt (collatzBallotMiddleLength m) := Real.sqrt_le_sqrt hb
  have hsqrta :
      Real.sqrt (collatzBallotOuterLength m) *
          Real.sqrt (collatzBallotOuterLength m) =
        (collatzBallotOuterLength m : ℝ) := by
    rw [← sq]
    exact Real.sq_sqrt (by positivity)
  have hsqrt_four : Real.sqrt ((m : ℝ) / 4) = Real.sqrt m / 2 := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ m)]
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs]
      norm_num
    rw [hs4]
  rw [hsqrt_four] at hsqrtb
  rw [hsqrta]
  have hprod := mul_le_mul ha hsqrtb (by positivity) (by positivity)
  nlinarith

/-- The summed three-block estimate in the canonical quarter-scale split.
This is the exact finite form of the `m^(-3/2)` prefactor, before proving
that every literal surviving word is represented by the three-block event. -/
theorem exists_sum_collatzQuarterSplitFairBinMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzThreeBlockFlatMass (1 / 2)
                (collatzBallotOuterLength m)
                (collatzBallotMiddleLength m) B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by
  obtain ⟨C₀, hC₀, hbase⟩ := exists_sum_collatzThreeBlockFairBinMass_le
  refine ⟨16 * C₀, by positivity, ?_⟩
  intro m Q B hm hB
  have ha : 0 < collatzBallotOuterLength m :=
    collatzBallotOuterLength_pos hm
  have hb : 0 < collatzBallotMiddleLength m :=
    collatzBallotMiddleLength_pos hm
  have hraw := hbase (collatzBallotOuterLength m)
    (collatzBallotMiddleLength m) Q B ha hb hB
  let D : ℝ := Real.sqrt (collatzBallotOuterLength m) *
    Real.sqrt (collatzBallotOuterLength m) *
      Real.sqrt (collatzBallotMiddleLength m)
  let d₀ : ℝ := (m : ℝ) * Real.sqrt m / 16
  let N : ℝ := C₀ * (B + 1)
  let E : ℝ := Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
    collatzTiltLambda * B)
  have hD : d₀ ≤ D := collatzBallot_denominator_lower hm
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hfrac : N / D ≤ N / d₀ :=
    div_le_div_of_nonneg_left hN hd₀ hD
  have hlen : 2 * collatzBallotOuterLength m +
      collatzBallotMiddleLength m = m := collatzBallot_split m
  have hexp :
      Real.exp (-(collatzFairTiltRate *
          ((2 * collatzBallotOuterLength m +
            collatzBallotMiddleLength m : ℕ) : ℝ)) +
          collatzTiltLambda * B) = E := by
    rw [hlen]
  rw [hexp] at hraw
  calc
    (∑ q ∈ Finset.range Q,
        collatzThreeBlockFlatMass (1 / 2)
          (collatzBallotOuterLength m)
          (collatzBallotMiddleLength m) B q) ≤ N / D * E := by
      simpa [N, D] using hraw
    _ ≤ N / d₀ * E :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
    _ = (16 * C₀) * (B + 1) / ((m : ℝ) * Real.sqrt m) *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
          collatzTiltLambda * B) := by
      dsimp [N, d₀, E]
      field_simp
      <;> ring

/-- The literal full-word event inherits the quarter-split
`m^(-3/2)` estimate.  Its coordinates are unique; the next timeout layer only
has to split the actual parity word and prove event containment. -/
theorem exists_sum_collatzQuarterSplitFullMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzFullThreeBlockMass (1 / 2)
                (collatzBallotOuterLength m)
                (collatzBallotMiddleLength m) B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by
  obtain ⟨C, hC, hEnvelope⟩ :=
    exists_sum_collatzQuarterSplitFairBinMass_le
  refine ⟨C, hC, ?_⟩
  intro m Q B hm hB
  calc
    (∑ q ∈ Finset.range Q,
        collatzFullThreeBlockMass (1 / 2)
          (collatzBallotOuterLength m)
          (collatzBallotMiddleLength m) B q) ≤
        ∑ q ∈ Finset.range Q,
          collatzThreeBlockFlatMass (1 / 2)
            (collatzBallotOuterLength m)
            (collatzBallotMiddleLength m) B q := by
      apply Finset.sum_le_sum
      intro q _hq
      exact collatzFullThreeBlockMass_le_envelope _ _ _ _
    _ ≤ C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
            collatzTiltLambda * B) := hEnvelope m Q B hm hB

/-- Direct full-word form of the quarter-split estimate.  The equivalence
above certifies that no word is lost or duplicated by the three-block
coordinates. -/
theorem exists_sum_collatzQuarterSplitFullWordMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzFullWordMass (1 / 2) m B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by
  obtain ⟨C, hC, hThreeBlock⟩ :=
    exists_sum_collatzQuarterSplitFullMass_le
  refine ⟨C, hC, ?_⟩
  intro m Q B hm hB
  have hlen : collatzBallotOuterLength m +
      (collatzBallotMiddleLength m + collatzBallotOuterLength m) = m := by
    have hsplit := collatzBallot_split m
    omega
  calc
    (∑ q ∈ Finset.range Q,
        collatzFullWordMass (1 / 2) m B q) =
        ∑ q ∈ Finset.range Q,
          collatzFullThreeBlockMass (1 / 2)
            (collatzBallotOuterLength m)
            (collatzBallotMiddleLength m) B q := by
      apply Finset.sum_congr rfl
      intro q _hq
      calc
        collatzFullWordMass (1 / 2) m B q =
            collatzFullWordMass (1 / 2)
              (collatzBallotOuterLength m +
                (collatzBallotMiddleLength m +
                  collatzBallotOuterLength m)) B q := by rw [hlen]
        _ = collatzFullThreeBlockMass (1 / 2)
              (collatzBallotOuterLength m)
              (collatzBallotMiddleLength m) B q :=
          collatzFullWordMass_eq_threeBlock _ _ _ _ _
    _ ≤ C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
            collatzTiltLambda * B) := hThreeBlock m Q B hm hB

/-! ## The finite multiplicative maximum -/

/-- The multiplicative factor contributed by one shortcut parity bit. -/
def ballotMultiplier (b : Bool) : ℝ :=
  if b then 3 / 2 else 1 / 2

@[simp] theorem ballotMultiplier_false : ballotMultiplier false = 1 / 2 := rfl
@[simp] theorem ballotMultiplier_true : ballotMultiplier true = 3 / 2 := rfl

/-- Whether a finite continuation crosses the open multiplicative barrier
`u`, including its current vertex. -/
def crossesMultiplicativeFrom (u : ℝ) :
    (r : ℕ) → ℝ → (Fin r → Bool) → Prop
  | 0, z, _ => u < z
  | r + 1, z, v =>
      u < z ∨
        crossesMultiplicativeFrom u r (z * ballotMultiplier (v 0))
          (fun i => v i.succ)

/-- Exact number of continuations crossing an open multiplicative barrier. -/
noncomputable def multiplicativeHitCount (u : ℝ) (r : ℕ) (z : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (crossesMultiplicativeFrom u r z)).card

theorem crossesMultiplicativeFrom_of_crossed
    {u z : ℝ} {r : ℕ} (hz : u < z) (v : Fin r → Bool) :
    crossesMultiplicativeFrom u r z v := by
  cases r <;> simp [crossesMultiplicativeFrom, hz]

theorem multiplicativeHitCount_of_crossed
    {u z : ℝ} {r : ℕ} (hz : u < z) :
    multiplicativeHitCount u r z = 2 ^ r := by
  classical
  rw [multiplicativeHitCount]
  have hfilter :
      Finset.univ.filter (crossesMultiplicativeFrom u r z) = Finset.univ := by
    exact Finset.filter_eq_self.mpr
      (fun v _ => crossesMultiplicativeFrom_of_crossed hz v)
  rw [hfilter]
  simp

/-- On a safe current state, expose the first bit of a crossing word. -/
noncomputable def safeMultiplicativeHitSuccEquiv
    {u z : ℝ} {r : ℕ} (hz : ¬u < z) :
    {v : Fin (r + 1) → Bool //
      crossesMultiplicativeFrom u (r + 1) z v} ≃
      Σ b : Bool,
        {w : Fin r → Bool //
          crossesMultiplicativeFrom u r (z * ballotMultiplier b) w} :=
  ((Fin.consEquiv (fun _ : Fin (r + 1) => Bool)).symm.subtypeEquiv
      (fun v => by
        change
          crossesMultiplicativeFrom u (r + 1) z v ↔
            crossesMultiplicativeFrom u r
              (z * ballotMultiplier (v 0)) (fun i => v i.succ)
        simp [crossesMultiplicativeFrom, hz])).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun b w => crossesMultiplicativeFrom u r
        (z * ballotMultiplier b) w))

theorem multiplicativeHitCount_succ_of_safe
    {u z : ℝ} {r : ℕ} (hz : ¬u < z) :
    multiplicativeHitCount u (r + 1) z =
      multiplicativeHitCount u r (z * (3 / 2)) +
        multiplicativeHitCount u r (z * (1 / 2)) := by
  classical
  unfold multiplicativeHitCount
  rw [← Fintype.card_subtype
        (crossesMultiplicativeFrom u (r + 1) z),
      ← Fintype.card_subtype
        (crossesMultiplicativeFrom u r (z * (3 / 2))),
      ← Fintype.card_subtype
        (crossesMultiplicativeFrom u r (z * (1 / 2)))]
  calc
    Fintype.card
        {v : Fin (r + 1) → Bool //
          crossesMultiplicativeFrom u (r + 1) z v} =
      Fintype.card
        (Σ b : Bool,
          {w : Fin r → Bool //
            crossesMultiplicativeFrom u r
              (z * ballotMultiplier b) w}) :=
      Fintype.card_congr (safeMultiplicativeHitSuccEquiv (r := r) hz)
    _ = Fintype.card
          {w : Fin r → Bool //
            crossesMultiplicativeFrom u r (z * (3 / 2)) w} +
        Fintype.card
          {w : Fin r → Bool //
            crossesMultiplicativeFrom u r (z * (1 / 2)) w} := by
      simp only [Fintype.card_sigma, Fintype.sum_bool,
        ballotMultiplier_true, ballotMultiplier_false]
      congr 1 <;> exact Fintype.card_congr (Equiv.refl _)

/-- Finite multiplicative maximal inequality on the Boolean tree.  The proof
uses only that the two child multipliers have sum two. -/
theorem multiplicativeHitCount_mul_le
    (u : ℝ) (r : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (multiplicativeHitCount u r z : ℝ) * u ≤ (2 : ℝ) ^ r * z := by
  induction r generalizing z with
  | zero =>
      by_cases hcross : u < z
      · rw [multiplicativeHitCount_of_crossed hcross]
        simpa using hcross.le
      · simp [multiplicativeHitCount, crossesMultiplicativeFrom, hcross, hz]
  | succ r ihr =>
      by_cases hcross : u < z
      · rw [multiplicativeHitCount_of_crossed hcross]
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        exact mul_le_mul_of_nonneg_left hcross.le (by positivity)
      · rw [multiplicativeHitCount_succ_of_safe hcross]
        push_cast
        have hright := ihr (z * (3 / 2)) (by positivity)
        have hleft := ihr (z * (1 / 2)) (by positivity)
        calc
          ((multiplicativeHitCount u r (z * (3 / 2)) : ℝ) +
              (multiplicativeHitCount u r (z * (1 / 2)) : ℝ)) * u =
              (multiplicativeHitCount u r (z * (3 / 2)) : ℝ) * u +
                (multiplicativeHitCount u r (z * (1 / 2)) : ℝ) * u := by ring
          _ ≤ (2 : ℝ) ^ r * (z * (3 / 2)) +
                (2 : ℝ) ^ r * (z * (1 / 2)) := add_le_add hright hleft
          _ = (2 : ℝ) ^ (r + 1) * z := by rw [pow_succ]; ring

/-- Appendix B.4 in exact finite-word form. -/
theorem normalized_multiplicativeHitCount_le_inv
    {u : ℝ} (hu : 0 < u) (M : ℕ) :
    (multiplicativeHitCount u M 1 : ℝ) / (2 : ℝ) ^ M ≤ u⁻¹ := by
  have htree := multiplicativeHitCount_mul_le u M 1 (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  rw [div_le_iff₀ hpow]
  have hcount :
      (multiplicativeHitCount u M 1 : ℝ) ≤ (2 : ℝ) ^ M / u :=
    (le_div_iff₀ hu).2 (by simpa using htree)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcount

/-! ## Reciprocal lower bound for the finite multiplicative maximum -/

@[simp] theorem card_boolSupport_cons
    {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    (boolSupport (Fin.cons b w)).card =
      (if b then 1 else 0) + (boolSupport w).card := by
  classical
  unfold boolSupport
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mem_univ, true_and]
  rw [Fin.sum_univ_succ]
  cases b <;> simp

/-- The centered support count has mean zero under the `3/4` Bernoulli
product weighting. -/
theorem sum_threeQuarter_centered_eq_zero :
    ∀ r : ℕ,
      ∑ v : Fin r → Bool,
          bernoulliWordWeight (3 / 4) v *
            (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) = 0 := by
  intro r
  induction r with
  | zero => simp [bernoulliWordWeight, boolSupport]
  | succ r ihr =>
      rw [← Equiv.sum_comp
        (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp [Fin.consEquiv, bernoulliWordWeight_cons,
        card_boolSupport_cons, Nat.cast_add, Nat.cast_succ]
      rw [← Finset.sum_add_distrib]
      calc
        (∑ w : Fin r → Bool,
            (3 / 4 * bernoulliWordWeight (3 / 4) w *
                  (1 + (↑(boolSupport w).card : ℝ) - 3 * (↑r + 1) / 4) +
              (1 - 3 / 4) * bernoulliWordWeight (3 / 4) w *
                  (↑(boolSupport w).card - 3 * (↑r + 1) / 4))) =
            ∑ w : Fin r → Bool,
              bernoulliWordWeight (3 / 4) w *
                (↑(boolSupport w).card - 3 * (r : ℝ) / 4) := by
          apply Finset.sum_congr rfl
          intro w _hw
          ring
        _ = 0 := ihr

/-- The centered support count has variance `3r/16` under the `3/4`
Bernoulli product weighting. -/
theorem sum_threeQuarter_centered_sq :
    ∀ r : ℕ,
      ∑ v : Fin r → Bool,
          bernoulliWordWeight (3 / 4) v *
            (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) ^ 2 =
        3 * (r : ℝ) / 16 := by
  intro r
  induction r with
  | zero => simp [bernoulliWordWeight, boolSupport]
  | succ r ihr =>
      rw [← Equiv.sum_comp
        (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp [Fin.consEquiv, bernoulliWordWeight_cons,
        card_boolSupport_cons, Nat.cast_add, Nat.cast_succ]
      rw [← Finset.sum_add_distrib]
      calc
        (∑ w : Fin r → Bool,
            (3 / 4 * bernoulliWordWeight (3 / 4) w *
                  (1 + (↑(boolSupport w).card : ℝ) - 3 * (↑r + 1) / 4) ^ 2 +
              (1 - 3 / 4) * bernoulliWordWeight (3 / 4) w *
                  (↑(boolSupport w).card - 3 * (↑r + 1) / 4) ^ 2)) =
            (∑ w : Fin r → Bool,
              bernoulliWordWeight (3 / 4) w *
                (↑(boolSupport w).card - 3 * (r : ℝ) / 4) ^ 2) +
              (3 / 16) *
                (∑ w : Fin r → Bool, bernoulliWordWeight (3 / 4) w) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w _hw
          ring
        _ = 3 * ((r : ℝ) + 1) / 16 := by
          rw [ihr, sum_bernoulliWordWeight_eq_one]
          norm_num
          ring

/-- Exact `3/4`-weighted lower-tail mass at a fixed linear displacement. -/
noncomputable def threeQuarterLowerTailMass
    (eps : ℝ) (r : ℕ) : ℝ := by
  classical
  exact ∑ v : Fin r → Bool,
    bernoulliWordWeight (3 / 4) v *
      if ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r then 1 else 0

/-- Finite Chebyshev bound for the `3/4`-weighted support count. -/
theorem threeQuarterLowerTailMass_le
    {eps : ℝ} (heps : 0 < eps) {r : ℕ} (hr : 0 < r) :
    threeQuarterLowerTailMass eps r ≤
      3 / (16 * eps ^ 2 * (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcoef : 0 < eps ^ 2 * (r : ℝ) ^ 2 := by positivity
  have hweighted : eps ^ 2 * (r : ℝ) ^ 2 *
        threeQuarterLowerTailMass eps r ≤
      ∑ v : Fin r → Bool,
        bernoulliWordWeight (3 / 4) v *
          (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) ^ 2 := by
    classical
    unfold threeQuarterLowerTailMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _hv
    have hw : 0 ≤ bernoulliWordWeight (3 / 4) v :=
      bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v
    by_cases hv : ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r
    · simp only [hv, if_true, mul_one]
      have hdev :
          ((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4 ≤
            -(eps * (r : ℝ)) := by
        linarith
      have hsq : eps ^ 2 * (r : ℝ) ^ 2 ≤
          (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) ^ 2 := by
        nlinarith [mul_pos heps hrR]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hsq)]
    · simp only [hv, if_false, mul_zero, mul_zero]
      exact mul_nonneg hw (sq_nonneg _)
  rw [sum_threeQuarter_centered_sq] at hweighted
  have hquot : 3 / (16 * eps ^ 2 * (r : ℝ)) =
      (3 * (r : ℝ) / 16) / (eps ^ 2 * (r : ℝ) ^ 2) := by
    field_simp
  rw [hquot]
  apply (le_div_iff₀ hcoef).2
  calc
    threeQuarterLowerTailMass eps r *
        (eps ^ 2 * (r : ℝ) ^ 2) =
        eps ^ 2 * (r : ℝ) ^ 2 *
          threeQuarterLowerTailMass eps r := by ring
    _ ≤ 3 * (r : ℝ) / 16 := hweighted

/-- Terminal multiplicative value of one finite Boolean word. -/
def ballotWordValue {r : ℕ} (z : ℝ) (v : Fin r → Bool) : ℝ :=
  z * ∏ i, ballotMultiplier (v i)

@[simp] theorem ballotWordValue_zero (z : ℝ) (v : Fin 0 → Bool) :
    ballotWordValue z v = z := by
  simp [ballotWordValue]

@[simp] theorem ballotWordValue_cons
    {r : ℕ} (z : ℝ) (b : Bool) (w : Fin r → Bool) :
    ballotWordValue z (Fin.cons b w) =
      ballotWordValue (z * ballotMultiplier b) w := by
  simp [ballotWordValue, Fin.prod_univ_succ]
  ring

/-- Multiplicative value stopped at the first open crossing, or at the word
horizon if no crossing occurs. -/
def stoppedBallotValue (u : ℝ) :
    (r : ℕ) → ℝ → (Fin r → Bool) → ℝ
  | 0, z, _ => z
  | r + 1, z, v =>
      if u < z then z
      else stoppedBallotValue u r
        (z * ballotMultiplier (v 0)) (fun i => v i.succ)

@[simp] theorem stoppedBallotValue_cons
    {u z : ℝ} {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    stoppedBallotValue u (r + 1) z (Fin.cons b w) =
      if u < z then z else
        stoppedBallotValue u r (z * ballotMultiplier b) w := by
  simp [stoppedBallotValue]

/-- Finite stopped-tree mean identity. -/
theorem sum_stoppedBallotValue_eq :
    ∀ (u : ℝ) (r : ℕ) (z : ℝ),
      ∑ v : Fin r → Bool, stoppedBallotValue u r z v =
        (2 : ℝ) ^ r * z := by
  intro u r
  induction r with
  | zero => intro z; simp [stoppedBallotValue]
  | succ r ihr =>
      intro z
      rw [← Equiv.sum_comp
        (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      by_cases hz : u < z
      · simp [Fin.consEquiv, stoppedBallotValue, hz, pow_succ]
        ring
      · simp [Fin.consEquiv, stoppedBallotValue_cons, hz]
        rw [ihr, ihr, pow_succ]
        norm_num [ballotMultiplier]
        ring

theorem stoppedBallotValue_nonneg :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      0 ≤ z → 0 ≤ stoppedBallotValue u r z v := by
  intro u r
  induction r with
  | zero => intro z v hz; simpa [stoppedBallotValue] using hz
  | succ r ihr =>
      intro z v hz
      by_cases hcross : u < z
      · simp [stoppedBallotValue, hcross, hz]
      · simp only [stoppedBallotValue, hcross, if_false]
        apply ihr
        have hmult : 0 ≤ ballotMultiplier (v 0) := by
          cases v 0 <;> norm_num [ballotMultiplier]
        exact mul_nonneg hz hmult

/-- A first crossing overshoots the open barrier by at most the upward
multiplier `3/2`. -/
theorem stoppedBallotValue_le_three_halves :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      0 ≤ u → 0 ≤ z → z ≤ 3 * u / 2 →
        stoppedBallotValue u r z v ≤ 3 * u / 2 := by
  intro u r
  induction r with
  | zero => intro z v hu hz hzUpper; simpa [stoppedBallotValue] using hzUpper
  | succ r ihr =>
      intro z v hu hz hzUpper
      by_cases hcross : u < z
      · simpa [stoppedBallotValue, hcross] using hzUpper
      · simp only [stoppedBallotValue, hcross, if_false]
        have hzu : z ≤ u := le_of_not_gt hcross
        have hmult0 : 0 ≤ ballotMultiplier (v 0) := by
          cases v 0 <;> norm_num [ballotMultiplier]
        apply ihr hu (mul_nonneg hz hmult0)
        cases hbit : v 0 <;> simp [ballotMultiplier, hbit]
        · nlinarith
        · nlinarith

theorem not_crosses_stopped_eq_wordValue :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      ¬crossesMultiplicativeFrom u r z v →
        stoppedBallotValue u r z v = ballotWordValue z v := by
  intro u r
  induction r with
  | zero => intro z v hsafe; simp [stoppedBallotValue, ballotWordValue]
  | succ r ihr =>
      intro z v hsafe
      have hparts : ¬u < z ∧
          ¬crossesMultiplicativeFrom u r
            (z * ballotMultiplier (v 0)) (fun i => v i.succ) := by
        simpa [crossesMultiplicativeFrom] using hsafe
      simp only [stoppedBallotValue, hparts.1, if_false]
      rw [ihr hparts.2]
      simp [ballotWordValue, Fin.prod_univ_succ]
      ring

noncomputable def safeTerminalSum (u : ℝ) (r : ℕ) (z : ℝ) : ℝ := by
  classical
  exact ∑ v : Fin r → Bool,
    if crossesMultiplicativeFrom u r z v then 0
    else ballotWordValue z v

/-- Optional-stopping inequality with the exact finite overshoot factor. -/
theorem stoppedTree_upper
    {u : ℝ} (hu : 1 ≤ u) (r : ℕ) :
    (2 : ℝ) ^ r ≤
      (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) +
        safeTerminalSum u r 1 := by
  classical
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hupper : (1 : ℝ) ≤ 3 * u / 2 := by nlinarith
  have hmean :
      ∑ v : Fin r → Bool, stoppedBallotValue u r 1 v =
        (2 : ℝ) ^ r := by
    simpa using sum_stoppedBallotValue_eq u r 1
  rw [← hmean]
  calc
    (∑ v : Fin r → Bool, stoppedBallotValue u r 1 v) ≤
        ∑ v : Fin r → Bool,
          (if crossesMultiplicativeFrom u r 1 v then 3 * u / 2
            else ballotWordValue 1 v) := by
      apply Finset.sum_le_sum
      intro v _hv
      by_cases hv : crossesMultiplicativeFrom u r 1 v
      · simp only [hv, if_true]
        exact stoppedBallotValue_le_three_halves hu0 (by norm_num) hupper
      · simp only [hv, if_false]
        exact (not_crosses_stopped_eq_wordValue hv).le
    _ = (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) +
        safeTerminalSum u r 1 := by
      unfold multiplicativeHitCount safeTerminalSum
      rw [show (∑ v : Fin r → Bool,
            (if crossesMultiplicativeFrom u r 1 v then 3 * u / 2
              else ballotWordValue 1 v)) =
          (∑ v : Fin r → Bool,
            (if crossesMultiplicativeFrom u r 1 v then 3 * u / 2 else 0)) +
          (∑ v : Fin r → Bool,
            (if crossesMultiplicativeFrom u r 1 v then 0
              else ballotWordValue 1 v)) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _hv
        split <;> simp_all]
      congr 1
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]

@[simp] theorem ballotWordValue_scale
    {r : ℕ} (z : ℝ) (v : Fin r → Bool) :
    ballotWordValue z v = z * ballotWordValue 1 v := by
  simp [ballotWordValue]

/-- Exact change from the terminal fair multiplicative value to the `3/4`
Bernoulli word weight. -/
theorem ballotWordValue_one_eq_two_pow_mul_weight :
    ∀ {r : ℕ} (v : Fin r → Bool),
      ballotWordValue 1 v =
        (2 : ℝ) ^ r * bernoulliWordWeight (3 / 4) v := by
  intro r
  induction r with
  | zero => intro v; simp [ballotWordValue, bernoulliWordWeight]
  | succ r ihr =>
      intro v
      let b := v 0
      let w : Fin r → Bool := fun i => v i.succ
      have hv : v = Fin.cons b w := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hv, ballotWordValue_cons,
        ballotWordValue_scale, ihr, bernoulliWordWeight_cons, pow_succ]
      cases b <;> norm_num [ballotMultiplier]
      <;> ring

theorem ballotWordValue_le_of_not_crosses :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      ¬crossesMultiplicativeFrom u r z v →
        ballotWordValue z v ≤ u := by
  intro u r
  induction r with
  | zero =>
      intro z v hsafe
      have hzu : z ≤ u := le_of_not_gt (by
        simpa [crossesMultiplicativeFrom] using hsafe)
      simpa [ballotWordValue] using hzu
  | succ r ihr =>
      intro z v hsafe
      have hparts : ¬u < z ∧
          ¬crossesMultiplicativeFrom u r
            (z * ballotMultiplier (v 0)) (fun i => v i.succ) := by
        simpa [crossesMultiplicativeFrom] using hsafe
      rw [show ballotWordValue z v =
          ballotWordValue (z * ballotMultiplier (v 0))
            (fun i => v i.succ) by
        simp [ballotWordValue, Fin.prod_univ_succ]
        ring]
      exact ihr hparts.2

theorem safeTerminalSum_le_lowerTail
    {u eps : ℝ} {r : ℕ}
    (hterminal : ∀ v : Fin r → Bool,
      ballotWordValue 1 v ≤ u →
        ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r) :
    safeTerminalSum u r 1 ≤
      (2 : ℝ) ^ r * threeQuarterLowerTailMass eps r := by
  classical
  unfold safeTerminalSum threeQuarterLowerTailMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _hv
  have hpow : 0 ≤ (2 : ℝ) ^ r := by positivity
  have hw : 0 ≤ bernoulliWordWeight (3 / 4) v :=
    bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v
  by_cases hcross : crossesMultiplicativeFrom u r 1 v
  · simp only [hcross, if_true]
    exact mul_nonneg hpow (mul_nonneg hw (by split <;> norm_num))
  · have hvalue := ballotWordValue_le_of_not_crosses hcross
    have hsupport := hterminal v hvalue
    simp only [hcross, if_false, hsupport, if_true, mul_one]
    rw [ballotWordValue_one_eq_two_pow_mul_weight]

theorem normalized_multiplicativeHitCount_ge
    {u eps : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 0 < r)
    (hterminal : ∀ v : Fin r → Bool,
      ballotWordValue 1 v ≤ u →
        ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r)
    (heps : 0 < eps) :
    (2 / (3 * u)) * (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) ≤
      (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r := by
  have hpow : 0 < (2 : ℝ) ^ r := by positivity
  have htail := threeQuarterLowerTailMass_le heps hr
  have hsafe := safeTerminalSum_le_lowerTail hterminal
  have htree := stoppedTree_upper hu r
  have hsafe' : safeTerminalSum u r 1 ≤
      (2 : ℝ) ^ r * (3 / (16 * eps ^ 2 * (r : ℝ))) :=
    hsafe.trans (mul_le_mul_of_nonneg_left htail hpow.le)
  have hmain : (2 : ℝ) ^ r *
        (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) ≤
      (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) := by
    linarith
  have hscalePos : 0 < 3 * u / 2 := by
    have : 0 < u := zero_lt_one.trans_le hu
    positivity
  have hnorm : 1 - 3 / (16 * eps ^ 2 * (r : ℝ)) ≤
      ((multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r) *
        (3 * u / 2) := by
    have hmain' :
        (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) * (2 : ℝ) ^ r ≤
          (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) := by
      simpa [mul_comm] using hmain
    have hdiv := (le_div_iff₀ hpow).2 hmain'
    calc
      1 - 3 / (16 * eps ^ 2 * (r : ℝ)) ≤
          (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) /
            (2 : ℝ) ^ r := hdiv
      _ = ((multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r) *
          (3 * u / 2) := by ring
  have hdivide := (div_le_iff₀ hscalePos).2 hnorm
  calc
    (2 / (3 * u)) * (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) =
        (1 - 3 / (16 * eps ^ 2 * (r : ℝ))) / (3 * u / 2) := by
      field_simp
    _ ≤ (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r := hdivide

/-- Fixed separation between the `3/4` change-of-measure mean and the
Collatz critical slope. -/
def reciprocalMaximumEpsilon : ℝ :=
  (3 / 4 - collatzTilt) / 2

def reciprocalMaximumConstant : ℝ :=
  3 / (16 * reciprocalMaximumEpsilon ^ 2)

theorem reciprocalMaximumEpsilon_pos :
    0 < reciprocalMaximumEpsilon := by
  unfold reciprocalMaximumEpsilon
  have h : collatzTilt < 3 / 4 :=
    collatzTilt_lt_two_thirds.trans (by norm_num)
  linarith

theorem reciprocalMaximumConstant_pos :
    0 < reciprocalMaximumConstant := by
  unfold reciprocalMaximumConstant
  have hsquare : 0 < reciprocalMaximumEpsilon ^ 2 :=
    sq_pos_of_pos reciprocalMaximumEpsilon_pos
  exact div_pos (by norm_num) (mul_pos (by norm_num) hsquare)

theorem collatzTilt_add_reciprocalMaximumEpsilon :
    collatzTilt + reciprocalMaximumEpsilon =
      3 / 4 - reciprocalMaximumEpsilon := by
  unfold reciprocalMaximumEpsilon
  ring

theorem ballotMultiplier_eq_exp_collatzLogIncrement (b : Bool) :
    ballotMultiplier b = Real.exp (collatzLogIncrement b) := by
  cases b with
  | false =>
      change (1 / 2 : ℝ) = Real.exp (-Real.log 2)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
  | true =>
      change (3 / 2 : ℝ) = Real.exp (Real.log 3 - Real.log 2)
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 3),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem ballotWordValue_one_eq_exp_incrementSum
    {r : ℕ} (v : Fin r → Bool) :
    ballotWordValue 1 v =
      Real.exp (wordIncrementSum collatzLogIncrement v) := by
  unfold ballotWordValue wordIncrementSum
  simp only [one_mul]
  rw [show (∏ i, ballotMultiplier (v i)) =
      ∏ i, Real.exp (collatzLogIncrement (v i)) by
    apply Finset.prod_congr rfl
    intro i _hi
    exact ballotMultiplier_eq_exp_collatzLogIncrement (v i)]
  exact (Real.exp_sum Finset.univ
    (fun i => collatzLogIncrement (v i))).symm

theorem log_ballotWordValue_one
    {r : ℕ} (v : Fin r → Bool) :
    Real.log (ballotWordValue 1 v) =
      ((boolSupport v).card : ℝ) * Real.log 3 -
        (r : ℝ) * Real.log 2 := by
  rw [ballotWordValue_one_eq_exp_incrementSum, Real.log_exp,
    wordIncrementSum_collatz]

theorem support_le_reciprocalMaximumSlope
    {u : ℝ} (hu : 1 ≤ u) {r : ℕ}
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3)
    (v : Fin r → Bool) (hv : ballotWordValue 1 v ≤ u) :
    ((boolSupport v).card : ℝ) ≤
      (3 / 4 - reciprocalMaximumEpsilon) * r := by
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hvalPos : 0 < ballotWordValue 1 v := by
    rw [ballotWordValue_one_eq_exp_incrementSum]
    exact Real.exp_pos _
  have hlogle : Real.log (ballotWordValue 1 v) ≤ Real.log u :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hvalPos) (Set.mem_Ioi.mpr huPos) hv
  rw [log_ballotWordValue_one] at hlogle
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htilt : collatzTilt * Real.log 3 = Real.log 2 := by
    unfold collatzTilt
    field_simp [ne_of_gt hlog3]
  have hmul : ((boolSupport v).card : ℝ) * Real.log 3 ≤
      (collatzTilt + reciprocalMaximumEpsilon) *
        (r : ℝ) * Real.log 3 := by
    calc
      ((boolSupport v).card : ℝ) * Real.log 3 ≤
          (r : ℝ) * Real.log 2 +
            reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3 := by
        linarith
      _ = (collatzTilt + reciprocalMaximumEpsilon) *
          (r : ℝ) * Real.log 3 := by
        rw [← htilt]
        ring
  have hslope : ((boolSupport v).card : ℝ) ≤
      (collatzTilt + reciprocalMaximumEpsilon) * (r : ℝ) := by
    exact le_of_mul_le_mul_right (by
      simpa [mul_assoc] using hmul) hlog3
  rw [collatzTilt_add_reciprocalMaximumEpsilon] at hslope
  exact hslope

/-- Manuscript Lemma B.5: reciprocal lower and upper bounds for the finite
multiplicative maximum.  All probabilities are exact finite-word weights. -/
theorem reciprocal_finite_multiplicative_maximum
    {u : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 0 < r)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (r : ℝ)) ≤
      (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r ∧
    (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r ≤ u⁻¹ := by
  have hlower := normalized_multiplicativeHitCount_ge hu hr
    (fun v hv ↦ support_le_reciprocalMaximumSlope hu hlog v hv)
    reciprocalMaximumEpsilon_pos
  have hconstant :
      3 / (16 * reciprocalMaximumEpsilon ^ 2 * (r : ℝ)) =
        reciprocalMaximumConstant / (r : ℝ) := by
    unfold reciprocalMaximumConstant
    ring
  rw [hconstant] at hlower
  exact ⟨hlower, normalized_multiplicativeHitCount_le_inv
    (zero_lt_one.trans_le hu) r⟩

end

end FirstPassageLinearTransport
