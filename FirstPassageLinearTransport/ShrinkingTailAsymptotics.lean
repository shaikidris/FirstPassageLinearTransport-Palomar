/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingParameters
import FirstPassageLinearTransport.TerminalTailAsymptotics

/-!
# Asymptotics for the compressed shrinking-barrier time support

The feasible-time support has size `O(sqrt (M log M))`.  This module proves
that multiplying the terminal tail by that support loses only one half of a
power of the outer shell, up to an arbitrarily small strict margin.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- A square-root logarithmic prefactor costs only one half power, with every
strict exponent below that endpoint available eventually. -/
theorem eventually_sqrt_mul_log_rpow_le
    {p kappa : ℝ} (hkappa : kappa < p - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (((M : ℝ) + 2) ^ (-p)) ≤
        ((M : ℝ) + 2) ^ (-kappa) := by
  let eps := p - 1 / 2 - kappa
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (s := eps) (1 / 2 : ℝ) heps).bound
      (by norm_num : (0 : ℝ) < 1)
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with M hsmall hM
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxeps0 : 0 ≤ x ^ eps := Real.rpow_nonneg hx0.le _
  have hlogHalf0 : 0 ≤ Real.log x ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hlog0 _
  rw [Real.norm_eq_abs, abs_of_nonneg hlogHalf0,
    Real.norm_eq_abs, abs_of_nonneg hxeps0, one_mul] at hsmall
  have hsqrtFactor :
      Real.sqrt (x * Real.log x) ≤ x ^ (1 / 2 : ℝ) * x ^ eps := by
    rw [Real.sqrt_mul hx0.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hx0.le _)
  calc
    Real.sqrt (x * Real.log x) * x ^ (-p) ≤
        (x ^ (1 / 2 : ℝ) * x ^ eps) * x ^ (-p) :=
      mul_le_mul_of_nonneg_right hsqrtFactor (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-kappa) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      dsimp [eps]
      ring

/-- The terminal profile multiplied by the compressed feasible-time support
loses exactly one half power of the shell rank. -/
theorem eventually_sqrtSupport_mul_terminalTail_polylog_le_power
    {A b b' c' kappa : ℝ}
    (hA : 0 < A)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (hkappa : kappa < A * min b' c' / Real.log 2 - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          terminalTailBound b b' c' (polylogTerminalRank A M) ≤
        terminalTailPrefactor b b' c' *
          (((M : ℝ) + 2) ^ (-kappa)) := by
  let p := A * min b' c' / Real.log 2
  have hsqrt := eventually_sqrt_mul_log_rpow_le
    (p := p) (kappa := kappa) (by simpa [p] using hkappa)
  filter_upwards [hsqrt] with M hsqrt
  have htail := terminalTailBound_polylog_le
    hA hb' hbb' hc' hc2 M
  have hsqrt0 : 0 ≤
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) :=
    Real.sqrt_nonneg _
  have hpref0 : 0 ≤ terminalTailPrefactor b b' c' :=
    (terminalTailPrefactor_pos hb' hbb' hc' hc2).le
  calc
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        terminalTailBound b b' c' (polylogTerminalRank A M) ≤
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
        (terminalTailPrefactor b b' c' *
          (((M : ℝ) + 2) ^ (-p))) :=
      mul_le_mul_of_nonneg_left (by simpa [p] using htail) hsqrt0
    _ = terminalTailPrefactor b b' c' *
        (Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (((M : ℝ) + 2) ^ (-p))) := by ring
    _ ≤ terminalTailPrefactor b b' c' *
        (((M : ℝ) + 2) ^ (-kappa)) :=
      mul_le_mul_of_nonneg_left hsqrt hpref0

/-- The explicit high-rank density profile used simultaneously for the
initial shell and every target above the switch. -/
def shrinkingHighDensityProfile
    (P : ShrinkingBarrierRunData) (C : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-(Real.log 2 * (shrinkingSwitchRank C M : ℝ))) +
    quadraticWindowShellConstant *
      Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
        Real.log ((M : ℝ) + 2)))

/-- The high-rank profile is a fixed negative power.  The slower of the
switch-boundary and quadratic-barrier rates is retained explicitly. -/
theorem shrinkingHighDensityProfile_le_rpow
    (P : ShrinkingBarrierRunData) (C : ℝ) (M : ℕ) :
    shrinkingHighDensityProfile P C M ≤
      (1 + quadraticWindowShellConstant) *
        (((M : ℝ) + 2) ^
          (-min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2))) := by
  let x : ℝ := (M : ℝ) + 2
  let p := min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hswitch := shrinkingSwitchRank_lower C M
  have hboundary :
      Real.exp (-(Real.log 2 * (shrinkingSwitchRank C M : ℝ))) ≤
        x ^ (-(C * Real.log 2)) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hswitch hlog2.le
    dsimp [x]
    linarith
  have hbarrier :
      Real.exp (-(maximalBarrierC0 * P.D ^ 2 * Real.log x)) =
        x ^ (-(maximalBarrierC0 * P.D ^ 2)) := by
    rw [Real.rpow_def_of_pos hx0]
    ring_nf
  have hpLeft : p ≤ C * Real.log 2 := min_le_left _ _
  have hpRight : p ≤ maximalBarrierC0 * P.D ^ 2 := min_le_right _ _
  have hboundaryP : x ^ (-(C * Real.log 2)) ≤ x ^ (-p) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hbarrierP : x ^ (-(maximalBarrierC0 * P.D ^ 2)) ≤ x ^ (-p) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hquad0 : 0 ≤ quadraticWindowShellConstant :=
    quadraticWindowShellConstant_pos.le
  calc
    shrinkingHighDensityProfile P C M ≤
        x ^ (-(C * Real.log 2)) +
          quadraticWindowShellConstant *
            x ^ (-(maximalBarrierC0 * P.D ^ 2)) := by
      unfold shrinkingHighDensityProfile
      rw [hbarrier]
      exact add_le_add hboundary le_rfl
    _ ≤ x ^ (-p) + quadraticWindowShellConstant * x ^ (-p) := by
      exact add_le_add hboundaryP
        (mul_le_mul_of_nonneg_left hbarrierP hquad0)
    _ = (1 + quadraticWindowShellConstant) * x ^ (-p) := by ring

/-- Multiplying a quadratic rank factor and the compressed time support
costs only `5/2` powers, again with every strict margin available. -/
theorem eventually_sqrtSupport_mul_quadratic_rpow_le_power
    {p kappa : ℝ} (hkappa : kappa < p - 5 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 2) ^ (-p))) ≤
        ((M : ℝ) + 2) ^ (-kappa) := by
  have hbase := eventually_sqrt_mul_log_rpow_le
    (p := p - 2) (kappa := kappa) (by linarith)
  filter_upwards [hbase] with M hbase
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hquad : ((M : ℝ) + 1) ^ 2 ≤ x ^ (2 : ℕ) := by
    gcongr
    dsimp [x]
    linarith
  have hpow0 : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx0.le _
  have hsqrt0 : 0 ≤ Real.sqrt (x * Real.log x) := Real.sqrt_nonneg _
  have hrewrite : x ^ (2 : ℕ) * x ^ (-p) = x ^ (-(p - 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    Real.sqrt (x * Real.log x) *
        (((M : ℝ) + 1) ^ 2 * x ^ (-p)) ≤
      Real.sqrt (x * Real.log x) * (x ^ (2 : ℕ) * x ^ (-p)) := by
        gcongr
    _ = Real.sqrt (x * Real.log x) * x ^ (-(p - 2)) := by rw [hrewrite]
    _ ≤ x ^ (-kappa) := by simpa [x] using hbase

/-- Explicit coefficient for the canonical shrinking-barrier terminal
profile. -/
def shrinkingPolylogProfileConstant
    (P : ShrinkingBarrierRunData) (C b b' c' : ℝ) : ℝ :=
  let K := 1 + quadraticWindowShellConstant
  let T := shrinkingTimeSupportConstant P C + 1
  let R := 1 + 6 / (P.rStar : ℝ)
  K + T * R * (K + terminalTailPrefactor b b' c')

/-- Scalar closure of the support-sensitive master profile.  The high-rank
term spends `5/2` powers because it carries the quadratic rank multiplier;
the low terminal tail spends only `1/2` through the feasible-time support. -/
theorem eventually_shrinkingPolylogTerminalProfile_le_power
    (P : ShrinkingBarrierRunData)
    {A C b b' c' kappa : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (hHigh : kappa <
      min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2) - 5 / 2)
    (hLow : kappa < A * min b' c' / Real.log 2 - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      let dHi := shrinkingHighDensityProfile P C M
      let H := (shrinkingTimeSupportConstant P C + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      dHi + H * (1 + 6 / (P.rStar : ℝ)) *
          (((M : ℝ) + 1) ^ 2 * dHi +
            terminalTailBound b b' c' (polylogTerminalRank A M)) ≤
        shrinkingPolylogProfileConstant P C b b' c' *
          (((M : ℝ) + 2) ^ (-kappa)) := by
  let pHi := min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2)
  let K := 1 + quadraticWindowShellConstant
  let T := shrinkingTimeSupportConstant P C + 1
  let R := 1 + 6 / (P.rStar : ℝ)
  let pref := terminalTailPrefactor b b' c'
  have hHighBase := eventually_sqrtSupport_mul_quadratic_rpow_le_power
    (p := pHi) (kappa := kappa) (by simpa [pHi] using hHigh)
  have hLowBase := eventually_sqrtSupport_mul_terminalTail_polylog_le_power
    hA hb' hbb' hc' hc2 hLow
  filter_upwards [hHighBase, hLowBase] with M hHighBase hLowBase
  let x : ℝ := (M : ℝ) + 2
  let dHi := shrinkingHighDensityProfile P C M
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have := quadraticWindowShellConstant_pos
    positivity
  have hT0 : 0 ≤ T := by
    dsimp [T]
    linarith [shrinkingTimeSupportConstant_pos P hC]
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have hr : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
    positivity
  have hpref0 : 0 ≤ pref := by
    dsimp [pref]
    exact (terminalTailPrefactor_pos hb' hbb' hc' hc2).le
  have hdHi : dHi ≤ K * x ^ (-pHi) := by
    simpa [dHi, K, x, pHi] using shrinkingHighDensityProfile_le_rpow P C M
  have hdHi0 : 0 ≤ dHi := by
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad : 0 ≤ quadraticWindowShellConstant :=
      quadraticWindowShellConstant_pos.le
    positivity
  have hDirectPower : x ^ (-pHi) ≤ x ^ (-kappa) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by
      dsimp [pHi] at hHigh ⊢
      linarith)
  have hDirect : dHi ≤ K * x ^ (-kappa) :=
    hdHi.trans (mul_le_mul_of_nonneg_left hDirectPower hK0)
  have hHighTerm :
      T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * dHi) ≤
        (T * R * K) * x ^ (-kappa) := by
    calc
      _ ≤ T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * (K * x ^ (-pHi))) := by
        gcongr
      _ = T * R * K *
          (Real.sqrt (x * Real.log x) *
            (((M : ℝ) + 1) ^ 2 * x ^ (-pHi))) := by ring
      _ ≤ (T * R * K) * x ^ (-kappa) := by
        exact mul_le_mul_of_nonneg_left (by simpa [x, pHi] using hHighBase)
          (mul_nonneg (mul_nonneg hT0 hR0) hK0)
  have hLowTerm :
      T * Real.sqrt (x * Real.log x) * R *
          terminalTailBound b b' c' (polylogTerminalRank A M) ≤
        (T * R * pref) * x ^ (-kappa) := by
    calc
      _ = T * R *
          (Real.sqrt (x * Real.log x) *
            terminalTailBound b b' c' (polylogTerminalRank A M)) := by ring
      _ ≤ (T * R) * (pref * x ^ (-kappa)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [x, pref] using hLowBase)
          (mul_nonneg hT0 hR0)
      _ = (T * R * pref) * x ^ (-kappa) := by ring
  dsimp only
  calc
    dHi + T * Real.sqrt (x * Real.log x) * R *
        (((M : ℝ) + 1) ^ 2 * dHi +
          terminalTailBound b b' c' (polylogTerminalRank A M)) =
      dHi +
        T * Real.sqrt (x * Real.log x) * R *
          (((M : ℝ) + 1) ^ 2 * dHi) +
        T * Real.sqrt (x * Real.log x) * R *
          terminalTailBound b b' c' (polylogTerminalRank A M) := by ring
    _ ≤ K * x ^ (-kappa) +
        (T * R * K) * x ^ (-kappa) +
        (T * R * pref) * x ^ (-kappa) :=
      add_le_add (add_le_add hDirect hHighTerm) hLowTerm
    _ = shrinkingPolylogProfileConstant P C b b' c' *
        (((M : ℝ) + 2) ^ (-kappa)) := by
      unfold shrinkingPolylogProfileConstant
      dsimp [K, T, R, pref, x]
      ring

end

end FirstPassageLinearTransport
