/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.EntropyBarrier
import FirstPassageLinearTransport.Envelope

/-!
# Adjustable maximal-barrier envelope

This module separates the deterministic orbit-envelope payload from the
scalar startup inequalities used by the entropy-sharp barrier.  No density or
independence hypothesis is introduced.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- Barrier height using an arbitrary fixed fraction `lambda` of the envelope
tolerance. -/
def adjustableBarrierHeight (lambda t : ℝ) (M : ℕ) : ℝ :=
  lambda * t * M / logTwoThree


theorem three_rpow_adjustableBarrierHeight
    (lambda t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M =
      (2 : ℝ) ^ (lambda * t * (M : ℝ)) := by
  rw [three_rpow_eq_two_rpow_logTwoThree]
  congr 1
  unfold adjustableBarrierHeight
  have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
  field_simp [hlog]

/-- The square of the affine-correction barrier has the exact exponent used by
the startup comparison. -/
theorem three_rpow_adjustableBarrierHeight_sq
    (lambda t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M =
      (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := by
  rw [three_rpow_adjustableBarrierHeight, ← Real.rpow_add (by norm_num)]
  congr 1
  ring

/-- Deterministic envelope from any fixed maximal-parity barrier once the two
phase inequalities and the affine-correction absorption are supplied. -/
theorem orbit_envelope_of_regularBarrier
    {n k M : ℕ} {h t : ℝ}
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg : MaximalParityRegular n M h)
    (hphase : (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hphaseTwo : 2 * (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hcorrAbsorb :
      2 * ((2 + Real.sqrt 3) * (3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnPos : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hp (mem_dyadicShell.mp hnShell).1
  have hbounds := hreg k hkM
  have hSlo : (k : ℝ) / 2 - h ≤ oddCount n k := by
    have := (abs_le.mp hbounds).1
    linarith
  have hShi : (oddCount n k : ℝ) ≤ (k : ℝ) / 2 + h := by
    have := (abs_le.mp hbounds).2
    linarith
  have hcorr := normalizedCorrection_scaled_le_maximal
    (n := n) (M := M) (k := k) (h := h) hkM hreg
  exact ⟨orbit_lower_of_fixed_barrier hnPos hSlo hphase,
    orbit_upper_of_fixed_barrier hnPos hShi hphaseTwo hcorr hcorrAbsorb⟩

/-- The multiplicative phase inequality for the adjustable height. -/
theorem adjustableBarrier_phase
    {lambda t : ℝ} {M n : ℕ}
    (hlambda1 : lambda ≤ 1)
    (ht : 0 ≤ t) (hnShell : n ∈ dyadicShell M) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M ≤ (n : ℝ) ^ t := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  rw [three_rpow_adjustableBarrierHeight]
  calc
    (2 : ℝ) ^ (lambda * t * (M : ℝ)) ≤
        (2 : ℝ) ^ (t * (M : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hM : (0 : ℝ) ≤ M := by positivity
      have hlt : lambda * t ≤ 1 * t :=
        mul_le_mul_of_nonneg_right hlambda1 ht
      exact mul_le_mul_of_nonneg_right (by simpa using hlt) hM
    _ = ((2 : ℝ) ^ M) ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ t := Real.rpow_le_rpow (by positivity) hnLower ht

/-- Once the unused multiplicative exponent is at least one bit, the factor
two needed by the upper main term is also absorbed. -/
theorem adjustableBarrier_phase_two
    {lambda t : ℝ} {M n : ℕ}
    (ht : 0 ≤ t)
    (hstartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hnShell : n ∈ dyadicShell M) :
    2 * (3 : ℝ) ^ adjustableBarrierHeight lambda t M ≤ (n : ℝ) ^ t := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  rw [three_rpow_adjustableBarrierHeight]
  calc
    2 * (2 : ℝ) ^ (lambda * t * (M : ℝ)) =
        (2 : ℝ) ^ (1 + lambda * t * (M : ℝ)) := by
      calc
        2 * (2 : ℝ) ^ (lambda * t * (M : ℝ)) =
            (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (lambda * t * (M : ℝ)) := by
              norm_num
        _ = (2 : ℝ) ^ (1 + lambda * t * (M : ℝ)) := by
              rw [Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (t * (M : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hsplit :
          (1 - lambda) * t * (M : ℝ) =
            t * (M : ℝ) - lambda * t * (M : ℝ) := by
        ring
      rw [hsplit] at hstartup
      linarith
    _ = ((2 : ℝ) ^ M) ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ t := Real.rpow_le_rpow (by positivity) hnLower ht

/-- The affine correction is absorbed once its fixed constant fits in the
unused exponent `a0 + t - 2 * lambda * t`.  This is the exact finite-startup
condition needed by the adjustable barrier; eventuality is kept separate. -/
theorem adjustableBarrier_correction_absorb
    {lambda t : ℝ} {M n k : ℕ}
    (ht : 0 ≤ t) (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hstartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    2 * ((2 + Real.sqrt 3) *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M) ≤
      centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hnPosNat : 0 < n := by
    exact lt_of_lt_of_le (pow_pos (by omega) M) hnLowerNat
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hnPosNat
  have hcentral := centralOrbitScale_ge_n_rpow_neg_gap hkM hnShell
  have hbarrierSq := three_rpow_adjustableBarrierHeight_sq lambda t M
  have hpowNonneg :
      0 ≤ (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := by positivity
  have hstartupMul := mul_le_mul_of_nonneg_right hstartup hpowNonneg
  have hleft :
      2 * ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M) ≤
        (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) := by
    calc
      2 * ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
          (3 : ℝ) ^ adjustableBarrierHeight lambda t M) =
          (2 * (2 + Real.sqrt 3)) *
            (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := by
              rw [← hbarrierSq]
              ring
      _ ≤ (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ)) *
          (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := hstartupMul
      _ = (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
  have hbase :
      (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) ≤ (n : ℝ) ^ (a0 + t) := by
    have hexp : 0 ≤ a0 + t := add_nonneg a0_pos.le ht
    calc
      (2 : ℝ) ^ ((a0 + t) * (M : ℝ)) =
          ((2 : ℝ) ^ M) ^ (a0 + t) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            congr 1
            ring
      _ ≤ (n : ℝ) ^ (a0 + t) :=
        Real.rpow_le_rpow (by positivity) hnLower hexp
  have hscale :
      (n : ℝ) ^ (a0 + t) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
    have hexp : a0 + t = -driftGap + (1 + t) := by
      unfold driftGap
      ring
    rw [hexp, Real.rpow_add hnPos]
    exact mul_le_mul_of_nonneg_right hcentral (by positivity)
  exact hleft.trans (hbase.trans hscale)

/-- Complete deterministic envelope for the adjustable maximal barrier under
the two explicit finite-startup inequalities.  This is the formal socket used
by the entropy-sharp shell estimate. -/
theorem orbit_envelope_of_adjustableBarrier
    {lambda t : ℝ} {M n k : ℕ}
    (hlambda1 : lambda ≤ 1) (ht : 0 ≤ t)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ)))
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg :
      MaximalParityRegular n M (adjustableBarrierHeight lambda t M)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  exact orbit_envelope_of_regularBarrier hkM hnShell hreg
    (adjustableBarrier_phase hlambda1 ht hnShell)
    (adjustableBarrier_phase_two ht hmainStartup hnShell)
    (adjustableBarrier_correction_absorb ht hkM hnShell hcorrectionStartup)

end

end FirstPassageLinearTransport
