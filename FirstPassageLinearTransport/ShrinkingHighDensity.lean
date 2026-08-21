/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingProfile
import FirstPassageLinearTransport.BarrierDensity

/-!
# Polynomial density of the shrinking high barrier

Above the linear-log switch the cap in `shrinkingHighTolerance` is inactive.
Consequently `t^2 m = D^2 log (M+2)` exactly, and the quadratic maximal-barrier
estimate becomes a fixed negative power of the outer shell.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- The high tolerance cap is inactive whenever the current rank dominates
`C log (M+2)` and `D / sqrt C` fits below the cap. -/
theorem shrinkingHighTolerance_eq_formula
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M m : ℕ} (hm : 1 ≤ m)
    (hCm : C * Real.log ((M : ℝ) + 2) ≤ (m : ℝ)) :
    shrinkingHighTolerance P M m =
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  have hsqrtC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hratio :
      (Real.log ((M : ℝ) + 2) / (m : ℝ)) * C ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hmR]
    simpa [mul_comm] using hCm
  have hroot :
      Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) ≤
        1 / Real.sqrt C := by
    apply (le_div_iff₀ hsqrtC).2
    rw [← Real.sqrt_mul (div_nonneg hlog0 hmR.le)]
    simpa using (Real.sqrt_le_one.mpr hratio)
  have hformula :
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) ≤
        P.tau := by
    calc
      _ ≤ P.D * (1 / Real.sqrt C) :=
        mul_le_mul_of_nonneg_left hroot P.D_pos.le
      _ = P.D / Real.sqrt C := by ring
      _ ≤ P.tau := hcap
  unfold shrinkingHighTolerance
  rw [if_neg (Nat.ne_of_gt hm), min_eq_right hformula]

/-- Exact quadratic exponent at every high rank. -/
theorem shrinkingHighTolerance_sq_mul
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M m : ℕ} (hm : 1 ≤ m)
    (hCm : C * Real.log ((M : ℝ) + 2) ≤ (m : ℝ)) :
    shrinkingHighTolerance P M m ^ 2 * (m : ℝ) =
      P.D ^ 2 * Real.log ((M : ℝ) + 2) := by
  rw [shrinkingHighTolerance_eq_formula P hC hcap hm hCm]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [mul_pow, Real.sq_sqrt (div_nonneg hlog0 hmR.le)]
  field_simp [ne_of_gt hmR]

/-- Outer-shell density bound for the initial shrinking certification. -/
theorem card_shellInitialWindowBad_shrinking_le
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M ≤ M) :
    ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤
      quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
          Real.log ((M : ℝ) + 2))) := by
  have hCM : C * Real.log ((M : ℝ) + 2) ≤ (M : ℝ) :=
    (shrinkingSwitchRank_lower C M).trans (by exact_mod_cast hSwitch)
  have htEq := shrinkingHighTolerance_eq_formula P hC hcap hM hCM
  have ht0 := shrinkingHighTolerance_pos P M M
  have ht1 := (shrinkingHighTolerance_le_tau P M M).trans P.pHi.eta_le_one
  have hcard := card_shellInitialWindowBad_le_quadratic
    (M := M) ht0 ht1
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  have hdiv := (div_le_iff₀ hpow).2 hcard
  have hexp := shrinkingHighTolerance_sq_mul P hC hcap hM hCM
  have hexpScaled :
      maximalBarrierC0 * shrinkingHighTolerance P M M ^ 2 * (M : ℝ) =
        maximalBarrierC0 * (P.D ^ 2 * Real.log ((M : ℝ) + 2)) := by
    calc
      _ = maximalBarrierC0 *
          (shrinkingHighTolerance P M M ^ 2 * (M : ℝ)) := by ring
      _ = _ := by rw [hexp]
  calc
    _ ≤ quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 *
            shrinkingHighTolerance P M M ^ 2 * M)) := by
      simpa [mul_assoc] using hdiv
    _ = quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
          Real.log ((M : ℝ) + 2))) := by
      rw [hexpScaled]
      ring

/-- Density bound for every high first-passage landing target, including the
single upper power-of-two boundary point. -/
theorem card_landingBad_shrinking_high_density_le
    (P : ShrinkingBarrierRunData) {C : ℝ}
    (hC : 0 < C) (hcap : P.D / Real.sqrt C ≤ P.tau)
    {M q : ℕ} (hq1 : 1 ≤ q)
    (hHigh : shrinkingSwitchRank C M ≤ q - 1) :
    ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤
      Real.exp (-(Real.log 2 * (q : ℝ))) +
        quadraticWindowShellConstant / 2 *
          Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
            Real.log ((M : ℝ) + 2))) := by
  have hm1 : 1 ≤ q - 1 := by
    have hSpos := shrinkingSwitchRank_pos hC M
    omega
  have hCm : C * Real.log ((M : ℝ) + 2) ≤ ((q - 1 : ℕ) : ℝ) :=
    (shrinkingSwitchRank_lower C M).trans (by exact_mod_cast hHigh)
  have ht0 := shrinkingHighTolerance_pos P M (q - 1)
  have ht1 := (shrinkingHighTolerance_le_tau P M (q - 1)).trans P.pHi.eta_le_one
  have hshell := card_shellInitialWindowBad_le_quadratic
    (M := q - 1) ht0 ht1
  have hexp := shrinkingHighTolerance_sq_mul P hC hcap hm1 hCm
  have hexpScaled :
      maximalBarrierC0 * shrinkingHighTolerance P M (q - 1) ^ 2 *
          (((q - 1 : ℕ) : ℝ)) =
        maximalBarrierC0 * (P.D ^ 2 * Real.log ((M : ℝ) + 2)) := by
    calc
      _ = maximalBarrierC0 *
          (shrinkingHighTolerance P M (q - 1) ^ 2 *
            (((q - 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [hexp]
  have hexpScaled' :
      maximalBarrierC0 * shrinkingHighTolerance P M (q - 1) ^ 2 *
          ((q : ℝ) - 1) =
        maximalBarrierC0 * (P.D ^ 2 * Real.log ((M : ℝ) + 2)) := by
    simpa [Nat.cast_sub hq1] using hexpScaled
  have hlandNat := card_landingBad_le_shellBad_add_one hq1
    (shrinkingHighTolerance P M (q - 1))
  have hland :
      ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) ≤
        ((shellInitialWindowBad (q - 1)
          (shrinkingHighTolerance P M (q - 1))).card : ℝ) + 1 := by
    exact_mod_cast hlandNat
  have hpowq : 0 < (2 : ℝ) ^ q := by positivity
  have hpowSub : (2 : ℝ) ^ (q - 1) / (2 : ℝ) ^ q = 1 / 2 := by
    rw [show q = (q - 1) + 1 by omega, pow_succ]
    field_simp
    simp
  calc
    _ ≤ (((shellInitialWindowBad (q - 1)
          (shrinkingHighTolerance P M (q - 1))).card : ℝ) + 1) /
          (2 : ℝ) ^ q := div_le_div_of_nonneg_right hland hpowq.le
    _ ≤ (quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 *
            shrinkingHighTolerance P M (q - 1) ^ 2 * (q - 1))) *
          (2 : ℝ) ^ (q - 1) + 1) / (2 : ℝ) ^ q := by
      apply div_le_div_of_nonneg_right _ hpowq.le
      simpa [Nat.cast_sub hq1] using add_le_add_right hshell 1
    _ = Real.exp (-(Real.log 2 * (q : ℝ))) +
        quadraticWindowShellConstant / 2 *
          Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
            Real.log ((M : ℝ) + 2))) := by
      rw [hexpScaled', add_div, one_div_two_pow_eq_exp]
      have hmain :
          quadraticWindowShellConstant *
              Real.exp (-(maximalBarrierC0 *
                (P.D ^ 2 * Real.log ((M : ℝ) + 2)))) *
              (2 : ℝ) ^ (q - 1) / (2 : ℝ) ^ q =
            quadraticWindowShellConstant / 2 *
              Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := by
        calc
          _ = (quadraticWindowShellConstant *
                Real.exp (-(maximalBarrierC0 *
                  (P.D ^ 2 * Real.log ((M : ℝ) + 2))))) *
                ((2 : ℝ) ^ (q - 1) / (2 : ℝ) ^ q) := by ring
          _ = (quadraticWindowShellConstant *
                Real.exp (-(maximalBarrierC0 *
                  (P.D ^ 2 * Real.log ((M : ℝ) + 2))))) * (1 / 2) := by
            rw [hpowSub]
          _ = _ := by ring
      rw [hmain]
      ring

end

end FirstPassageLinearTransport
