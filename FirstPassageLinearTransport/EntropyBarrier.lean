/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import FirstPassageLinearTransport.Barrier

/-!
# Entropy-sharp maximal Boolean barrier

This module keeps the exact `log cosh` potential from the pruned Boolean tree
instead of replacing it by the quadratic Hoeffding bound.  The optimizer and
its binary-entropy value are isolated as scalar identities.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- The exact Legendre rate before optimizing the cosh parameter. -/
def booleanLegendreRate (t θ : ℝ) : ℝ :=
  2 * t * θ - Real.log (Real.cosh θ)

/-- Binary relative-entropy rate at displacement `t` from one half. -/
def binaryBarrierRate (t : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy (1 / 2 + t)

/-- Optimizing cosh parameter for displacement `t`. -/
def booleanOptimizer (t : ℝ) : ℝ :=
  (Real.log (1 / 2 + t) - Real.log (1 / 2 - t)) / 2

/-- Exact finite cosh-potential estimate, with no quadratic relaxation. -/
theorem barrierHitCount_le_exact_cosh
    (a θ : ℝ) (M : ℕ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp ((M : ℝ) * Real.log (Real.cosh θ) - θ * a) := by
  have hpot := barrierHitCount_mul_cosh_le a θ M 0 ha hθ
  have hlower : Real.exp (θ * a) / 2 ≤ Real.cosh (θ * a) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(θ * a))]
  have hleft :
      (barrierHitCount a M 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (barrierHitCount a M 0 : ℝ) * Real.cosh (θ * a) :=
    mul_le_mul_of_nonneg_left hlower (by positivity)
  have hcoshpow :
      Real.cosh θ ^ M =
        Real.exp ((M : ℝ) * Real.log (Real.cosh θ)) := by
    calc
      Real.cosh θ ^ M =
          Real.exp (Real.log (Real.cosh θ)) ^ M := by
        rw [Real.exp_log (Real.cosh_pos θ)]
      _ = Real.exp ((M : ℝ) * Real.log (Real.cosh θ)) := by
        rw [← Real.exp_nat_mul]
  have hmain :
      (barrierHitCount a M 0 : ℝ) * Real.exp (θ * a) ≤
        2 * ((2 : ℝ) ^ M *
          Real.exp ((M : ℝ) * Real.log (Real.cosh θ))) := by
    have hhalf :
        (barrierHitCount a M 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
          (2 : ℝ) ^ M * Real.cosh θ ^ M := by
      calc
        _ ≤ (barrierHitCount a M 0 : ℝ) * Real.cosh (θ * a) := hleft
        _ ≤ (2 : ℝ) ^ M * Real.cosh (θ * (0 : ℝ)) *
            Real.cosh θ ^ M := by
          simpa only [Int.cast_zero] using hpot
        _ = (2 : ℝ) ^ M * Real.cosh θ ^ M := by norm_num
    rw [hcoshpow] at hhalf
    nlinarith
  have hdiv :
      (barrierHitCount a M 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ M *
          Real.exp ((M : ℝ) * Real.log (Real.cosh θ)))) /
            Real.exp (θ * a) :=
    (le_div_iff₀ (Real.exp_pos (θ * a))).2 (by
      simpa [mul_comm] using hmain)
  calc
    (barrierHitCount a M 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ M *
          Real.exp ((M : ℝ) * Real.log (Real.cosh θ)))) /
            Real.exp (θ * a) := hdiv
    _ = (2 : ℝ) ^ (M + 1) *
        Real.exp ((M : ℝ) * Real.log (Real.cosh θ) - θ * a) := by
      rw [Real.exp_sub, pow_succ]
      ring

/-- Exact barrier bound expressed by the unoptimized Legendre rate. -/
theorem barrierHitCount_le_legendre
    (t θ : ℝ) (M : ℕ) (ht : 0 ≤ t) (hθ : 0 ≤ θ) :
    (barrierHitCount (2 * t * M) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * booleanLegendreRate t θ)) := by
  have hraw := barrierHitCount_le_exact_cosh
    (2 * t * M) θ M (by positivity) hθ
  convert hraw using 1
  unfold booleanLegendreRate
  congr 2
  ring

theorem booleanOptimizer_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    0 ≤ booleanOptimizer t := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  have hqp : (1 / 2 : ℝ) - t ≤ 1 / 2 + t := by linarith
  have hlog := Real.log_le_log hq hqp
  unfold booleanOptimizer
  linarith

theorem exp_booleanOptimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.exp (booleanOptimizer t) =
      Real.sqrt ((1 / 2 + t) / (1 / 2 - t)) := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  unfold booleanOptimizer
  rw [Real.exp_half, Real.exp_sub, Real.exp_log hp, Real.exp_log hq]

theorem exp_neg_booleanOptimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.exp (-booleanOptimizer t) =
      Real.sqrt ((1 / 2 - t) / (1 / 2 + t)) := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  rw [show -booleanOptimizer t =
      (Real.log (1 / 2 - t) - Real.log (1 / 2 + t)) / 2 by
        unfold booleanOptimizer
        ring]
  rw [Real.exp_half, Real.exp_sub, Real.exp_log hq, Real.exp_log hp]

private theorem sqrt_ratio_average
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) :
    (Real.sqrt (p / q) + Real.sqrt (q / p)) / 2 =
      1 / (2 * Real.sqrt (p * q)) := by
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  rw [Real.sqrt_div hp.le, Real.sqrt_div hq.le,
    Real.sqrt_mul hp.le]
  field_simp [ne_of_gt hsp, ne_of_gt hsq]
  rw [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le, hpq]

theorem cosh_booleanOptimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.cosh (booleanOptimizer t) =
      1 / (2 * Real.sqrt ((1 / 2 + t) * (1 / 2 - t))) := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  rw [Real.cosh_eq, exp_booleanOptimizer ht0 ht1,
    exp_neg_booleanOptimizer ht0 ht1]
  exact sqrt_ratio_average hp hq (by ring)

theorem log_cosh_booleanOptimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.log (Real.cosh (booleanOptimizer t)) =
      -Real.log 2 -
        (Real.log (1 / 2 + t) + Real.log (1 / 2 - t)) / 2 := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  have hpq : 0 ≤ ((1 / 2 : ℝ) + t) * (1 / 2 - t) :=
    mul_nonneg hp.le hq.le
  have hsqrt : Real.sqrt (((1 / 2 : ℝ) + t) * (1 / 2 - t)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos hp hq))
  rw [cosh_booleanOptimizer ht0 ht1, one_div, Real.log_inv,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsqrt,
    Real.log_sqrt hpq, Real.log_mul (ne_of_gt hp) (ne_of_gt hq)]
  ring

/-- The optimized Legendre value is exactly binary relative entropy from one
half. -/
theorem booleanLegendreRate_optimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    booleanLegendreRate t (booleanOptimizer t) = binaryBarrierRate t := by
  rw [booleanLegendreRate, binaryBarrierRate,
    log_cosh_booleanOptimizer ht0 ht1]
  unfold booleanOptimizer Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- Entropy-sharp two-sided maximal Boolean-walk estimate. -/
theorem barrierHitCount_le_binaryEntropy
    (t : ℝ) (M : ℕ) (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    (barrierHitCount (2 * t * M) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * binaryBarrierRate t)) := by
  have hraw := barrierHitCount_le_legendre
    t (booleanOptimizer t) M ht0 (booleanOptimizer_nonneg ht0 ht1)
  simpa [booleanLegendreRate_optimizer ht0 ht1] using hraw

/-- Shellwise entropy-sharp maximal-parity exceptional count. -/
theorem card_shellMaximalParityBad_le_binaryEntropy
    (t : ℝ) (M : ℕ) (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    ((shellMaximalParityBad M (t * M)).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * binaryBarrierRate t)) := by
  have hcard :
      (shellMaximalParityBad M (t * M)).card ≤
        (shellBarrierHit M (t * M)).card :=
    Finset.card_le_card (shellMaximalParityBad_subset_hit M (t * M))
  have hcardR :
      ((shellMaximalParityBad M (t * M)).card : ℝ) ≤
        ((shellBarrierHit M (t * M)).card : ℝ) := by
    exact_mod_cast hcard
  rw [card_shellBarrierHit] at hcardR
  have htail := barrierHitCount_le_binaryEntropy t M ht0 ht1
  exact hcardR.trans (by simpa [mul_assoc] using htail)

end

end FirstPassageLinearTransport
