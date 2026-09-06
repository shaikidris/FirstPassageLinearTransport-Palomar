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
  high_height_contraction :
    (run.rHi : ℝ) * (1 + run.tau) < 1
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
    high_height_contraction := Q.high_height_contraction
    tau_lt_beta := Q.tau_lt_beta
    epsilon_pos := Q.kappa_pos
    K₀_gt_six := by norm_num [K₀]
    K₁_pos := hK₁
    K₁_reserve := hreserve }⟩

/-- The high-rank polynomial error exponent may be prescribed arbitrarily.
The low timeout rate is unchanged: enlarge only the high tolerance coefficient
and switch constant of an existing package. -/
theorem exists_movingEndpointParameterPackage_epsilon_gt
    {Amax c beta N : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c) (hbeta : 0 < beta)
    (hN : 0 < N) :
    ∃ P : MovingEndpointParameterPackage Amax c beta, N < P.epsilon := by
  let P₀ : MovingEndpointParameterPackage Amax c beta :=
    Classical.choice (exists_movingEndpointParameterPackage hAmax hc hbeta)
  let target : ℝ := N + 1
  have htarget0 : 0 < target := by dsimp [target]; linarith
  have htargetN : N < target := by dsimp [target]; linarith
  have hc00 : 0 < maximalBarrierC0 := maximalBarrierC0_pos
  let Dfloor : ℝ := (target + 5 / 2) / maximalBarrierC0 + 2
  have hDfloor1 : 1 < Dfloor := by
    dsimp [Dfloor]
    have hnum : 0 < target + 5 / 2 := by linarith
    have : 0 < (target + 5 / 2) / maximalBarrierC0 :=
      div_pos hnum hc00
    linarith
  let D : ℝ := max P₀.run.D Dfloor
  have hDfloorD : Dfloor ≤ D := by dsimp [D]; exact le_max_right _ _
  have hD1 : 1 < D := hDfloor1.trans_le hDfloorD
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hDquot : (target + 5 / 2) / maximalBarrierC0 < D := by
    dsimp [Dfloor] at hDfloor1 hDfloorD ⊢
    linarith
  have hDsquare : D < D ^ 2 := by nlinarith
  have hDRate : target + 5 / 2 < maximalBarrierC0 * D ^ 2 := by
    have hquotSq : (target + 5 / 2) / maximalBarrierC0 < D ^ 2 :=
      hDquot.trans hDsquare
    simpa [mul_comm] using (div_lt_iff₀ hc00).1 hquotSq
  have htau0 : 0 < P₀.run.tau := P₀.run.pHi.eta_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Cfloor : ℝ := (D / P₀.run.tau) ^ 2 +
    (target + 5 / 2) / Real.log 2 + 2
  have hCfloorD : (D / P₀.run.tau) ^ 2 < Cfloor := by
    dsimp [Cfloor]
    have hrate0 : 0 < (target + 5 / 2) / Real.log 2 := by
      exact div_pos (by linarith) hlog2
    linarith
  have hCfloorRate : (target + 5 / 2) / Real.log 2 < Cfloor := by
    dsimp [Cfloor]
    have hsq0 : 0 ≤ (D / P₀.run.tau) ^ 2 := sq_nonneg _
    linarith
  let Cswitch : ℝ := max P₀.Cswitch Cfloor
  have hOldC : P₀.Cswitch ≤ Cswitch := by
    dsimp [Cswitch]
    exact le_max_left _ _
  have hFloorC : Cfloor ≤ Cswitch := by
    dsimp [Cswitch]
    exact le_max_right _ _
  have hC0 : 0 < Cswitch := P₀.Cswitch_pos.trans_le hOldC
  have hCD : (D / P₀.run.tau) ^ 2 < Cswitch :=
    hCfloorD.trans_le hFloorC
  have hCRate : target + 5 / 2 < Cswitch * Real.log 2 := by
    have hquot : (target + 5 / 2) / Real.log 2 < Cswitch :=
      hCfloorRate.trans_le hFloorC
    exact (div_lt_iff₀ hlog2).1 hquot
  have hcap : D / Real.sqrt Cswitch ≤ P₀.run.tau := by
    have hsqrtC : 0 < Real.sqrt Cswitch := Real.sqrt_pos.2 hC0
    have hleft : 0 ≤ D / P₀.run.tau := (div_pos hD0 htau0).le
    have hroot : D / P₀.run.tau < Real.sqrt Cswitch :=
      (Real.lt_sqrt hleft).2 hCD
    apply (div_le_iff₀ hsqrtC).2
    have hmul := mul_lt_mul_of_pos_left hroot htau0
    have heq : P₀.run.tau * (D / P₀.run.tau) = D := by
      field_simp [ne_of_gt htau0]
    rw [heq] at hmul
    exact hmul.le
  let run : ShrinkingBarrierRunData := { P₀.run with
    D := D
    D_pos := hD0 }
  let P : MovingEndpointParameterPackage Amax c beta := {
    run := run
    Cswitch := Cswitch
    epsilon := target
    K₀ := P₀.K₀
    K₁ := P₀.K₁
    Amax_pos := P₀.Amax_pos
    Cswitch_pos := hC0
    terminal_below_switch := P₀.terminal_below_switch.trans_le hOldC
    high_cap := by simpa [run] using hcap
    high_rate_margin := by
      rw [lt_sub_iff_add_lt, lt_min_iff]
      exact ⟨hCRate, hDRate⟩
    clock_pressure := P₀.clock_pressure
    high_height_contraction := by
      simpa [run] using P₀.high_height_contraction
    tau_lt_beta := by simpa [run] using P₀.tau_lt_beta
    epsilon_pos := htarget0
    K₀_gt_six := P₀.K₀_gt_six
    K₁_pos := P₀.K₁_pos
    K₁_reserve := P₀.K₁_reserve }
  exact ⟨P, by simpa [P] using htargetN⟩

end

end FirstPassageLinearTransport
