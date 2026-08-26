/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.MovingEndpointParameters
import FirstPassageLinearTransport.MovingEndpointScalars
import FirstPassageLinearTransport.MovingSharpTail
import FirstPassageLinearTransport.ShrinkingTailAsymptotics
import FirstPassageLinearTransport.TimeSupportScalars

/-!
# Scalar closure of the moving endpoint profile

The sharp entropy term is compared directly with the exact critical-buffer
identity.  The dyadic endpoint term is eventually dominated by that entropy
term, so no additional logarithmic loss is spent.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- The endpoint entropy term eventually dominates the faster dyadic term. -/
theorem eventually_dyadic_rank_term_le_endpoint_entropy_term :
    ∀ᶠ L : ℕ in atTop,
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        Real.sqrt L *
          Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
  let gap := Real.log 2 - firstPassageEndpointRate
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr firstPassageEndpointRate_lt_logTwo
  have hreal := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (1 / 2 : ℝ) gap hgap
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hsmall := hnat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with L hsmall hL
  have hLR : 0 < (L : ℝ) := by positivity
  have hroot : Real.sqrt (L : ℝ) = (L : ℝ) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  have hsmall' :
      (L : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(gap * (L : ℝ))) < 1 / 2 := by
    simpa [Function.comp_def] using hsmall
  have hfactor :
      2 * Real.sqrt L * Real.exp (-(gap * (L : ℝ))) ≤ 1 := by
    rw [hroot]
    linarith
  have hlin : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
    exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hsqrtSq : Real.sqrt L * Real.sqrt L = (L : ℝ) := by
    convert Real.sq_sqrt (show (0 : ℝ) ≤ L by positivity) using 1 <;> ring
  have hsplit :
      Real.exp (-(Real.log 2 * (L : ℝ))) =
        Real.exp (-(gap * (L : ℝ))) *
          Real.exp (-(firstPassageEndpointRate * (L : ℝ))) := by
    rw [← Real.exp_add]
    dsimp [gap]
    congr 1
    ring
  have hshift :
      Real.exp (-(firstPassageEndpointRate * (L : ℝ))) ≤
        Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hsub : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 1
    nlinarith [firstPassageEndpointRate_pos]
  calc
    ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        (2 * (L : ℝ)) * Real.exp (-(Real.log 2 * (L : ℝ))) := by
      gcongr
    _ = (2 * Real.sqrt L * Real.exp (-(gap * (L : ℝ)))) *
        (Real.sqrt L * Real.exp
          (-(firstPassageEndpointRate * (L : ℝ)))) := by
      rw [hsplit]
      calc
        (2 * (L : ℝ)) *
            (Real.exp (-(gap * (L : ℝ))) *
              Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) =
            (2 * (Real.sqrt L * Real.sqrt L)) *
              (Real.exp (-(gap * (L : ℝ))) *
                Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) := by
                  rw [hsqrtSq]
        _ = _ := by ring
    _ ≤ 1 * (Real.sqrt L * Real.exp
          (-(firstPassageEndpointRate * (L : ℝ)))) := by
      gcongr
    _ ≤ Real.sqrt L *
        Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
      simpa using mul_le_mul_of_nonneg_left hshift (Real.sqrt_nonneg _)

/-- The moving endpoint entropy term is bounded by the exact critical-buffer
factor, uniformly under a fixed upper bound for the shell exponent. -/
theorem moving_entropy_term_le_buffer
    {A : ℕ → ℝ} {Amax D : ℝ} {M : ℕ}
    (hAmax : 0 < Amax) (hD : 0 < D)
    (hA0 : 0 ≤ A M) (hAupper : A M ≤ Amax)
    (hL : 1 ≤ movingTerminalRank A M) :
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        Real.sqrt (movingTerminalRank A M) *
        Real.exp (-((firstPassageEndpointRate -
          D / (movingTerminalRank A M : ℝ)) *
            ((movingTerminalRank A M - 1 : ℕ) : ℝ))) ≤
      (Real.sqrt (Amax / Real.log 2 + 1) *
          Real.exp (firstPassageEndpointRate + D)) *
        ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by
  let x : ℝ := (M : ℝ) + 2
  let y : ℝ := Real.log ((M : ℝ) + 3)
  let L : ℕ := movingTerminalRank A M
  let K : ℝ := Amax / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 < x := by dsimp [x]; positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hx1 : 1 ≤ x := by
    dsimp [x]
    linarith
  have hy1 : 1 ≤ y := by
    dsimp [y]
    apply (Real.le_log_iff_exp_le (by linarith)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogxy : Real.log x ≤ y := by
    dsimp [x, y]
    apply Real.strictMonoOn_log.monotoneOn
    · exact (by linarith : 0 < (M : ℝ) + 2)
    · exact (by linarith : 0 < (M : ℝ) + 3)
    · linarith
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hLnat : 1 ≤ L := by simpa [L] using hL
  have hLr : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hLupper : (L : ℝ) ≤ K * y := by
    have hceil := movingTerminalRank_lt_add_one hA0
    have hAlog : A M * Real.logb 2 x ≤
        (Amax / Real.log 2) * y := by
      rw [Real.logb]
      have hAlogx : A M * Real.log x ≤ Amax * y := by
        calc
          A M * Real.log x ≤ Amax * Real.log x := by gcongr
          _ ≤ Amax * y := by gcongr
      calc
        A M * (Real.log x / Real.log 2) =
            (A M * Real.log x) / Real.log 2 := by ring
        _ ≤ (Amax * y) / Real.log 2 :=
          (div_le_div_iff_of_pos_right hlog2).2 hAlogx
        _ = (Amax / Real.log 2) * y := by ring
    exact (hceil.trans_le (by
      calc
        A M * Real.logb 2 x + 1 ≤
            (Amax / Real.log 2) * y + y := add_le_add hAlog hy1
        _ = K * y := by dsimp [K]; ring)).le
  have hsqrtPair : Real.sqrt (Real.log x) * Real.sqrt L ≤
      Real.sqrt K * y := by
    rw [← Real.sqrt_mul hlogx0]
    have hprod : Real.log x * (L : ℝ) ≤ K * y ^ 2 := by
      calc
        Real.log x * (L : ℝ) ≤ y * (K * y) := by gcongr
        _ = K * y ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hprod
    have hK0 : 0 ≤ K := hK.le
    rw [Real.sqrt_mul hK0, Real.sqrt_sq hy0] at hsqrt
    exact hsqrt
  have hsqrtSplit :
      Real.sqrt (x * Real.log x) = Real.sqrt x * Real.sqrt (Real.log x) := by
    rw [Real.sqrt_mul hx.le]
  have hexponent :
      -((firstPassageEndpointRate - D / (L : ℝ)) *
          ((L - 1 : ℕ) : ℝ)) ≤
        -(firstPassageEndpointRate * (L : ℝ)) +
          firstPassageEndpointRate + D := by
    have hsubCast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub hLnat]
      norm_num
    have hfrac : D * (((L : ℝ) - 1) / (L : ℝ)) ≤ D := by
      have hratio : ((L : ℝ) - 1) / (L : ℝ) ≤ 1 := by
        rw [div_le_one hLr]
        linarith
      simpa using mul_le_mul_of_nonneg_left hratio hD.le
    rw [hsubCast]
    calc
      -((firstPassageEndpointRate - D / (L : ℝ)) * ((L : ℝ) - 1)) =
          -(firstPassageEndpointRate * (L : ℝ)) +
            firstPassageEndpointRate +
              D * (((L : ℝ) - 1) / (L : ℝ)) := by ring
      _ ≤ _ := by linarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hbuffer := two_rpow_neg_movingRankBuffer_eq A M
  calc
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        Real.sqrt (movingTerminalRank A M) *
        Real.exp (-((firstPassageEndpointRate -
          D / (movingTerminalRank A M : ℝ)) *
            ((movingTerminalRank A M - 1 : ℕ) : ℝ))) =
      (Real.sqrt x *
        (Real.sqrt (Real.log x) * Real.sqrt L)) *
        Real.exp (-((firstPassageEndpointRate - D / (L : ℝ)) *
          ((L - 1 : ℕ) : ℝ))) := by
        dsimp [x, L]
        rw [hsqrtSplit]
        ring
    _ ≤ (Real.sqrt x * (Real.sqrt K * y)) *
        Real.exp (-(firstPassageEndpointRate * (L : ℝ)) +
          firstPassageEndpointRate + D) := by gcongr
    _ = (Real.sqrt K * Real.exp (firstPassageEndpointRate + D)) *
        (Real.sqrt x * y *
          Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) := by
      rw [show -(firstPassageEndpointRate * (L : ℝ)) +
          firstPassageEndpointRate + D =
        (firstPassageEndpointRate + D) +
          -(firstPassageEndpointRate * (L : ℝ)) by ring,
        Real.exp_add]
      ring
    _ = (Real.sqrt (Amax / Real.log 2 + 1) *
          Real.exp (firstPassageEndpointRate + D)) *
        ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by
      rw [hbuffer]

/-- Explicit coefficient in the final moving-endpoint shell profile. -/
def movingEndpointProfileConstant
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta) (C D : ℝ) : ℝ :=
  let K := 1 + quadraticWindowShellConstant
  let T := movingTimeSupportConstant P.run P.Cswitch + 1
  let R := 1 + 6 / (P.run.rStar : ℝ)
  let Q := exactSharpCriticalLowSeriesConstant
    (firstPassageEndpointRate / 2) (C / 2)
  let B := Real.sqrt (Amax / Real.log 2 + 1) *
    Real.exp (firstPassageEndpointRate + D)
  K + T * R * K + 2 * T * R * Q * B

/-- Scalar closure of the literal sharp moving profile.  The high-rank
terms are absorbed by the fixed negative power supplied by the parameter
package, while both low-rank terms are paid by the exact critical buffer. -/
theorem eventually_movingEndpointRawProfile_le_shellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ} {C D : ℝ}
    (hC : 0 < C) (hD : 0 < D)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
      let L := movingTerminalRank A M
      let H := (movingTimeSupportConstant P.run P.Cswitch + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
      let b := firstPassageEndpointRate - D / (L : ℝ)
      dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
          ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.run.rStar : ℝ)) *
          exactSharpCriticalLowSeriesConstant
            (firstPassageEndpointRate / 2) (C / 2) *
          (((L + 1 : ℕ) : ℝ) *
              Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L *
              Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) ≤
        movingEndpointProfileConstant P C D *
          ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by
  let pHi := min (P.Cswitch * Real.log 2)
    (maximalBarrierC0 * P.run.D ^ 2)
  let K := 1 + quadraticWindowShellConstant
  let T := movingTimeSupportConstant P.run P.Cswitch + 1
  let R := 1 + 6 / (P.run.rStar : ℝ)
  let Q := exactSharpCriticalLowSeriesConstant
    (firstPassageEndpointRate / 2) (C / 2)
  let B := Real.sqrt (Amax / Real.log 2 + 1) *
    Real.exp (firstPassageEndpointRate + D)
  have hHighBase := eventually_sqrtSupport_mul_quadratic_rpow_le_power
    (p := pHi) (kappa := P.epsilon) (by
      simpa [pHi] using P.high_rate_margin)
  have hTerminalT := tendsto_movingTerminalRank_atTop hbuffer
  have hDyadic := hTerminalT.eventually
    eventually_dyadic_rank_term_le_endpoint_entropy_term
  have hRank1 := (tendsto_atTop.1 hTerminalT) 1
  have hA0 := eventually_movingExponent_pos hbuffer
  filter_upwards [hHighBase, hDyadic, hRank1, hA0, hUpper]
    with M hHighBase hDyadic hRank1 hA0 hUpper
  let x : ℝ := (M : ℝ) + 2
  let L : ℕ := movingTerminalRank A M
  let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
  let b := firstPassageEndpointRate - D / (L : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hK0 : 0 ≤ K := by
    dsimp [K]
    linarith [quadraticWindowShellConstant_pos]
  have hT0 : 0 ≤ T := by
    have hrHi0 : 0 < (P.run.rHi : ℝ) := P.run.pHi.r_pos
    have hsqrtSq := Real.sq_sqrt hrHi0.le
    have hsqrt0 := Real.sqrt_nonneg (P.run.rHi : ℝ)
    have hsqrt1 : Real.sqrt (P.run.rHi : ℝ) < 1 := by
      nlinarith [P.run.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.rHi : ℝ) := sub_pos.mpr hsqrt1
    have hnum : 0 ≤ P.run.D + P.run.tau + 3 := by
      linarith [P.run.D_pos, P.run.pHi.eta_pos]
    have hfrac : 0 ≤
        (P.run.D + P.run.tau + 3) /
          (1 - Real.sqrt (P.run.rHi : ℝ)) :=
      div_nonneg hnum hden.le
    have hinner : 0 ≤
        (P.run.D + P.run.tau + 3) /
            (1 - Real.sqrt (P.run.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    dsimp [T, movingTimeSupportConstant]
    nlinarith [mul_nonneg hratio hinner]
  have hR0 : 0 ≤ R := by
    have hr : (0 : ℝ) < (P.run.rStar : ℝ) := by
      exact_mod_cast P.run.rStar_pos
    dsimp [R]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact (exactSharpCriticalLowSeriesConstant_spec
      (div_pos firstPassageEndpointRate_pos (by norm_num))
      (by positivity : 0 ≤ C / 2)).1.le
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdHi : dHi ≤ K * x ^ (-pHi) := by
    simpa [dHi, K, x, pHi] using
      shrinkingHighDensityProfile_le_rpow P.run P.Cswitch M
  have hdHi0 : 0 ≤ dHi := by
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad : 0 ≤ quadraticWindowShellConstant :=
      quadraticWindowShellConstant_pos.le
    positivity
  have hDirectPower : x ^ (-pHi) ≤ x ^ (-P.epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by
      have hmargin := P.high_rate_margin
      dsimp [pHi] at hmargin ⊢
      linarith)
  have hDirect : dHi ≤ K * x ^ (-P.epsilon) :=
    hdHi.trans (mul_le_mul_of_nonneg_left hDirectPower hK0)
  have hHighTerm :
      T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * dHi) ≤
        (T * R * K) * x ^ (-P.epsilon) := by
    calc
      _ ≤ T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * (K * x ^ (-pHi))) := by
        gcongr
      _ = T * R * K *
          (Real.sqrt (x * Real.log x) *
            (((M : ℝ) + 1) ^ 2 * x ^ (-pHi))) := by ring
      _ ≤ (T * R * K) * x ^ (-P.epsilon) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [x, pHi] using hHighBase)
          (mul_nonneg (mul_nonneg hT0 hR0) hK0)
  have hL1 : 1 ≤ L := by simpa [L] using hRank1
  have hLR : 0 < (L : ℝ) := by positivity
  have hEndpointToActual :
      Real.sqrt L * Real.exp
          (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) ≤
        Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    have hbLe : b ≤ firstPassageEndpointRate := by
      dsimp [b]
      have : 0 ≤ D / (L : ℝ) := div_nonneg hD.le hLR.le
      linarith
    have hshift0 : (0 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by positivity
    gcongr
  have hDyadic' :
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        Real.sqrt L *
          Real.exp (-(firstPassageEndpointRate * ((L - 1 : ℕ) : ℝ))) := by
    simpa [L] using hDyadic
  have hDyadicActual :
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) ≤
        Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) :=
    hDyadic'.trans hEndpointToActual
  have hLowScalar := moving_entropy_term_le_buffer
    P.Amax_pos hD hA0.le hUpper hL1
  have hLowTerm :
      T * Real.sqrt (x * Real.log x) * R * Q *
          (((L + 1 : ℕ) : ℝ) *
              Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) ≤
        (2 * T * R * Q * B) *
          ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by
    have hbracket :
        ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) ≤
          2 * (Real.sqrt L *
            Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
      linarith
    calc
      _ ≤ T * Real.sqrt (x * Real.log x) * R * Q *
          (2 * (Real.sqrt L *
            Real.exp (-(b * ((L - 1 : ℕ) : ℝ))))) := by
        gcongr
      _ = (2 * T * R * Q) *
          (Real.sqrt (x * Real.log x) * Real.sqrt L *
            Real.exp (-((firstPassageEndpointRate - D / (L : ℝ)) *
              ((L - 1 : ℕ) : ℝ)))) := by
        dsimp [b]
        ring
      _ ≤ (2 * T * R * Q) *
          (B * ((2 : ℝ) ^ (-(movingRankBuffer A M)))) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [x, L, B] using hLowScalar)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT0) hR0) hQ0)
      _ = (2 * T * R * Q * B) *
          ((2 : ℝ) ^ (-(movingRankBuffer A M))) := by ring
  dsimp only
  calc
    dHi + T * Real.sqrt (x * Real.log x) * R *
          ((M : ℝ) + 1) ^ 2 * dHi +
        T * Real.sqrt (x * Real.log x) * R * Q *
          (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
            Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) ≤
      K * x ^ (-P.epsilon) +
        (T * R * K) * x ^ (-P.epsilon) +
        (2 * T * R * Q * B) *
          ((2 : ℝ) ^ (-(movingRankBuffer A M))) :=
      add_le_add (add_le_add hDirect
        (by simpa [mul_assoc] using hHighTerm)) hLowTerm
    _ ≤ (K + T * R * K + 2 * T * R * Q * B) *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) + x ^ (-P.epsilon)) := by
      have hbuf0 : 0 ≤ (2 : ℝ) ^ (-(movingRankBuffer A M)) := by positivity
      have hxpow0 : 0 ≤ x ^ (-P.epsilon) := Real.rpow_nonneg hx0.le _
      have hTK0 : 0 ≤ T * R * K :=
        mul_nonneg (mul_nonneg hT0 hR0) hK0
      have hQB0 : 0 ≤ 2 * T * R * Q * B :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT0)
          hR0) hQ0) hB0
      calc
        _ ≤ K * (2 ^ (-movingRankBuffer A M) + x ^ (-P.epsilon)) +
            (T * R * K) *
              (2 ^ (-movingRankBuffer A M) + x ^ (-P.epsilon)) +
            (2 * T * R * Q * B) *
              (2 ^ (-movingRankBuffer A M) + x ^ (-P.epsilon)) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left hbuf0) hK0)
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left hbuf0) hTK0))
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right hxpow0) hQB0)
        _ = _ := by ring
    _ = movingEndpointProfileConstant P C D *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) := by
      rfl

end

end FirstPassageLinearTransport
