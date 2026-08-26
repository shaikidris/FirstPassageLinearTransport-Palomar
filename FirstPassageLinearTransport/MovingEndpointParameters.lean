/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.MovingLowParameters
import FirstPassageLinearTransport.ShrinkingParameters

/-!
# Parameter package for the moving endpoint

The high phase is any fixed shrinking-barrier package with positive scalar
margins.  The low phase uses the explicit moving parameters with `K₀ = 7`
and `K₁ = 8 / driftGap`; these choices discharge the quantitative startup and
the sharp landing-density reserve uniformly.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Fixed data needed by the moving endpoint construction. -/
structure MovingEndpointParameterPackage (Amax c beta : ℝ) where
  run : ShrinkingBarrierRunData
  Cswitch : ℝ
  epsilon : ℝ
  K₀ : ℝ
  K₁ : ℝ
  Amax_pos : 0 < Amax
  Cswitch_pos : 0 < Cswitch
  terminal_below_switch : Amax / Real.log 2 < Cswitch
  high_cap : run.D / Real.sqrt Cswitch ≤ run.tau
  high_rate_margin : epsilon <
    min (Cswitch * Real.log 2) (maximalBarrierC0 * run.D ^ 2) - 5 / 2
  clock_pressure : 1 / driftGap < c * Real.log 2
  tau_lt_beta : run.tau < beta
  epsilon_pos : 0 < epsilon
  K₀_gt_six : 6 < K₀
  K₁_pos : 0 < K₁
  K₁_reserve : 8 ≤ K₁ * driftGap

/-- Every admissible clock and ceiling pair admits fixed high data and moving
low constants with all required strict margins. -/
theorem exists_movingEndpointParameterPackage
    {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c) (hbeta : 0 < beta) :
    Nonempty (MovingEndpointParameterPackage Amax c beta) := by
  let Aaux := max Amax timeSupportCriticalExponent + 1
  have hAaux : timeSupportCriticalExponent < Aaux := by
    dsimp [Aaux]
    linarith [le_max_right Amax timeSupportCriticalExponent]
  have hAmaxAux : Amax < Aaux := by
    dsimp [Aaux]
    linarith [le_max_left Amax timeSupportCriticalExponent]
  let Q : ShrinkingPolylogParameterPackage Aaux c beta :=
    Classical.choice
      (exists_shrinkingPolylogParameterPackage hAaux hc hbeta)
  let K₀ : ℝ := 7
  let K₁ : ℝ := 8 / driftGap
  have hK₁ : 0 < K₁ := by
    dsimp [K₁]
    exact div_pos (by norm_num) driftGap_pos
  have hreserve : 8 ≤ K₁ * driftGap := by
    dsimp [K₁]
    field_simp [ne_of_gt driftGap_pos]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterminal : Amax / Real.log 2 < Q.Cswitch := by
    exact (div_lt_div_iff_of_pos_right hlog2).2 hAmaxAux |>.trans
      Q.terminal_below_switch
  have hclock : 1 / driftGap < c * Real.log 2 := by
    have hprod : 1 < c * (driftGap * Real.log 2) := by
      exact (div_lt_iff₀ (mul_pos driftGap_pos hlog2)).1
        (by simpa [fixedPolylogClockCritical] using hc)
    rw [div_lt_iff₀ driftGap_pos]
    nlinarith
  exact ⟨{
    run := Q.run
    Cswitch := Q.Cswitch
    epsilon := Q.kappa
    K₀ := K₀
    K₁ := K₁
    Amax_pos := hAmax
    Cswitch_pos := Q.Cswitch_pos
    terminal_below_switch := hterminal
    high_cap := Q.high_cap
    high_rate_margin := Q.high_rate_margin
    clock_pressure := hclock
    tau_lt_beta := Q.tau_lt_beta
    epsilon_pos := Q.kappa_pos
    K₀_gt_six := by norm_num [K₀]
    K₁_pos := hK₁
    K₁_reserve := hreserve }⟩

end

end FirstPassageLinearTransport
