/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutEndpointProfile
import FirstPassageLinearTransport.RankTransportAsymptotics

/-!
# Scalar closure of the timeout endpoint profile

This module instantiates the literal timeout envelope with the sharp terminal
binomial tail.  The low phase needs no `StageSetup`: the only startup is the
explicit eventual admissibility of `timeoutTargetRank`.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- The explicit timeout displacement loss is eventually paid by the
terminal rank. -/
theorem eventually_timeoutDisplacementLoss_le_terminalScale
    (K₀ : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      2 * timeoutDisplacementLoss K₀ ≤
        firstPassageEndpointDisplacement * (L : ℝ) := by
  have hT : Tendsto
      (fun L : ℕ => firstPassageEndpointDisplacement * (L : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop
      firstPassageEndpointDisplacement_pos
  exact (tendsto_atTop.1 hT) (2 * timeoutDisplacementLoss K₀)

/-- Literal timeout shell profile before its last scalar simplification. -/
theorem exists_eventually_timeoutEndpointGood_rawProfile
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio (timeoutEndpointGood P A M) M ≤
          let L := movingTerminalRank A M
          let H :=
            (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
          let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
          let b := firstPassageEndpointRate - D / (L : ℝ)
          dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
              ((M : ℝ) + 1) ^ 2 * dHi +
            H * (1 + 6 / (P.run.rStar : ℝ)) *
              exactSharpCriticalLowSeriesConstant
                (firstPassageEndpointRate / 2) (C / 2) *
              (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
  obtain ⟨C, D, hC, hD, hLowBase⟩ :=
    exists_card_timeoutShellBad_endpointRate_le
      (show 0 ≤ P.K₀ by linarith [P.K₀_gt_six])
  refine ⟨C, D, hC, hD, ?_⟩
  have hTerminalT := tendsto_movingTerminalRank_atTop hbuffer
  have hAdmBase := eventually_movingLow_admissible
    (show 0 < P.K₀ by linarith [P.K₀_gt_six]) P.K₁_pos
  have hAdm := hTerminalT.eventually hAdmBase
  have hTimeoutAdmBase := eventually_timeoutTargetRank_admissible
    (show 0 < P.K₀ by linarith [P.K₀_gt_six])
  have hTimeoutAdm := hTerminalT.eventually hTimeoutAdmBase
  have hScaleBase := eventually_timeoutDisplacementLoss_le_terminalScale P.K₀
  have hScale := hTerminalT.eventually hScaleBase
  have hSmallBase := eventually_interval_rankTransport_small P.run.rStar_pos
  have hSmall := hTerminalT.eventually hSmallBase
  have hLS := eventually_movingTerminalRank_lt_shrinkingSwitchRank
    P.Amax_pos.le P.terminal_below_switch hUpper
  have hSM := eventually_shrinkingSwitchRank_lt_source P.Cswitch_pos.le
  have hTimes := eventually_timeoutFeasibleTimes_card_lt_sqrt
    P.run.toTimeoutHigh P.K₀ P.Cswitch_pos.le
  have hStarHi : P.run.rStar ≤ P.run.rHi := by
    rw [P.run.rStar_eq]
    exact min_le_left _ _
  have hStarLoBase : ∀ᶠ L : ℕ in atTop,
      (P.run.rStar : ℝ) ≤ movingLowRatio P.K₀ L := by
    have hrStarOne : (P.run.rStar : ℝ) < 1 := by
      have hStarHiR : (P.run.rStar : ℝ) ≤ (P.run.rHi : ℝ) := by
        exact_mod_cast hStarHi
      exact hStarHiR.trans_lt P.run.pHi.r_lt_one
    exact (tendsto_movingLowRatio P.K₀).eventually
      (Ici_mem_nhds hrStarOne)
  have hStarLo := hTerminalT.eventually hStarLoBase
  have hRateBase : ∀ᶠ L : ℕ in atTop,
      firstPassageEndpointRate / 2 ≤
        firstPassageEndpointRate - D / (L : ℝ) := by
    have hcast : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hcast
    have hdiv : Tendsto (fun L : ℕ => D / (L : ℝ)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul hinv :
          Tendsto (fun L : ℕ => D * ((L : ℝ))⁻¹) atTop (nhds (D * 0)))
    have hrate : Tendsto
        (fun L : ℕ => firstPassageEndpointRate - D / (L : ℝ))
        atTop (nhds firstPassageEndpointRate) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact hrate.eventually (Ici_mem_nhds (by
      linarith [firstPassageEndpointRate_pos]))
  have hRate := hTerminalT.eventually hRateBase
  have hRank2 := (tendsto_atTop.1 hTerminalT) 2
  filter_upwards [hAdm, hTimeoutAdm, hScale, hSmall, hLS, hSM, hTimes,
      hStarLo, hRate, hRank2,
      eventually_ge_atTop (max 2 P.run.pHi.M0)]
    with M hAdm hTimeoutAdm hScale hSmall hLS hSM hTimes hStarLo hRate
      hRank2 hM
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  let H :=
    (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
  let b := firstPassageEndpointRate - D / (L : ℝ)
  have hM1 : 1 ≤ M := by omega
  have hL2 : 2 ≤ L := by simpa [L] using hRank2
  have hLS' : L + 1 ≤ S := by simpa [L, S] using hLS
  have hSM' : S < M := by simpa [S] using hSM
  have hH0 : 0 ≤ H := by
    dsimp [H, timeoutTimeSupportConstant]
    have hrHi0 : 0 < (P.run.rHi : ℝ) := P.run.pHi.r_pos
    have hsqrt1 : Real.sqrt (P.run.rHi : ℝ) < 1 := by
      nlinarith [Real.sq_sqrt hrHi0.le, Real.sqrt_nonneg (P.run.rHi : ℝ),
        P.run.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.rHi : ℝ) := sub_pos.mpr hsqrt1
    have hnum : 0 ≤ P.run.D + P.run.tau + 3 := by
      linarith [P.run.D_pos, P.run.pHi.eta_pos]
    have hinner : 0 ≤
        (P.run.D + P.run.tau + 3) /
            (1 - Real.sqrt (P.run.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    positivity
  have hC2 : 0 ≤ C / 2 := by positivity
  have hb₀ : 0 < firstPassageEndpointRate / 2 :=
    div_pos firstPassageEndpointRate_pos (by norm_num)
  have hTimes' : ∀ q ∈ Finset.Icc L (M - 1),
      ((timeoutFeasibleTimes P.run.toTimeoutHigh P.K₀ L M S q).card : ℝ) ≤ H := by
    intro q hq
    exact (hTimes L q).le
  have hInitial :
      ((shellInitialWindowBad M
        (timeoutHighTolerance P.run.toTimeoutHigh M M)).card : ℝ) /
          (2 : ℝ) ^ M ≤ dHi := by
    have hbase := card_shellInitialWindowBad_shrinking_le P.run
      P.Cswitch_pos P.high_cap hM1 hSM.le
    dsimp [dHi, shrinkingHighDensityProfile]
    have hboundary : 0 ≤
        Real.exp (-(Real.log 2 * (shrinkingSwitchRank P.Cswitch M : ℝ))) :=
      Real.exp_pos _ |>.le
    simpa [timeoutHighTolerance, ShrinkingBarrierRunData.toTimeoutHigh,
      shrinkingHighTolerance] using (show
      ((shellInitialWindowBad M
        (shrinkingHighTolerance P.run M M)).card : ℝ) / (2 : ℝ) ^ M ≤
          Real.exp (-(Real.log 2 * (shrinkingSwitchRank P.Cswitch M : ℝ))) +
            quadraticWindowShellConstant *
              Real.exp (-(maximalBarrierC0 * P.run.D ^ 2 *
                Real.log ((M : ℝ) + 2))) by linarith)
  have hHighTargets : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q
        (timeoutHighTolerance P.run.toTimeoutHigh M (q - 1))).card : ℝ) /
          (2 : ℝ) ^ q ≤ dHi := by
    intro q hq
    have hqLower := (Finset.mem_Icc.mp hq).1
    have hq1 : 1 ≤ q := by omega
    have hSParent : shrinkingSwitchRank P.Cswitch M ≤ q - 1 := by
      simpa [S] using (show S ≤ q - 1 by omega)
    have hbase := card_landingBad_shrinking_high_density_le P.run
      P.Cswitch_pos P.high_cap hq1 hSParent
    have hqS : (S : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show S ≤ q by omega)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hexp : Real.exp (-(Real.log 2 * (q : ℝ))) ≤
        Real.exp (-(Real.log 2 * (S : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp [dHi, shrinkingHighDensityProfile]
    simpa [timeoutHighTolerance, ShrinkingBarrierRunData.toTimeoutHigh,
      shrinkingHighTolerance] using hbase.trans (by
      calc
        _ ≤ Real.exp (-(Real.log 2 * (S : ℝ))) +
            quadraticWindowShellConstant / 2 *
              Real.exp (-(maximalBarrierC0 * P.run.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := add_le_add hexp le_rfl
        _ ≤ Real.exp (-(Real.log 2 * (S : ℝ))) +
            quadraticWindowShellConstant *
              Real.exp (-(maximalBarrierC0 * P.run.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := by
          gcongr
          linarith [quadraticWindowShellConstant_pos])
  have hLow : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad P.K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        ((C / 2) / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))) := by
    intro p hp
    have hpI := Finset.mem_Icc.mp hp
    have hLm : L ≤ p - 1 := by omega
    have hbase := hLowBase L (p - 1) (by omega) hLm
      hAdm.2.2.1.le hAdm.2.2.2.1.le hScale
    have hp1 : 1 ≤ p := by omega
    have hpowp : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
      conv_lhs => rw [show p = (p - 1) + 1 by omega]
      rw [pow_succ]
    rw [timeoutLandingBad_eq_timeoutShellBad]
    calc
      ((timeoutShellBad P.K₀ L (p - 1)).card : ℝ) / (2 : ℝ) ^ p =
          (((timeoutShellBad P.K₀ L (p - 1)).card : ℝ) /
            (2 : ℝ) ^ (p - 1)) / 2 := by
        rw [hpowp]
        ring
      _ ≤ (((C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(((p - 1 : ℕ) : ℝ) *
            (firstPassageEndpointRate - D / (L : ℝ))))) / 2) := by
        gcongr
      _ = ((C / 2) / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))) := by
        dsimp [b]
        ring
  have hProfile := timeoutSeparatedFailureEnvelope_density_sharp_le
    P.run.rStar_pos hStarHi hStarLo hM1 hLS' hSM' hL2 hH0 hC2
    (fun p hp => (hTimeoutAdm (p - 1) (by
      have hpI := Finset.mem_Icc.mp hp
      omega)).1)
    (fun p hp => by
      have hpI := Finset.mem_Icc.mp hp
      exact (hTimeoutAdm (p - 1) (by omega)).2.trans (by omega))
    (fun q hq => hSmall (M - 1) q hq) hTimes' hInitial hHighTargets
    hLow hb₀ hRate
  rw [shellExceptionalRatio, shellBad_timeoutEndpointGood P A M]
  simpa [L, S, H, dHi, b] using hProfile

/-- The timeout shift costs at most one harmless factor two relative to the
already verified critical-buffer scalar profile. -/
def timeoutEndpointProfileConstant
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta) (C D : ℝ) : ℝ :=
  2 * movingEndpointProfileConstant P C D

/-- Scalar closure of the sharp timeout profile. -/
theorem eventually_timeoutEndpointRawProfile_le_shellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ} {C D : ℝ}
    (hC : 0 < C) (hD : 0 < D)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
      let L := movingTerminalRank A M
      let H :=
        (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
      let b := firstPassageEndpointRate - D / (L : ℝ)
      dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
          ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.run.rStar : ℝ)) *
          exactSharpCriticalLowSeriesConstant
            (firstPassageEndpointRate / 2) (C / 2) *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) ≤
        timeoutEndpointProfileConstant P C D *
          ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by
  have hScalar := eventually_movingEndpointRawProfile_le_shellError
    P hC hD hbuffer hUpper
  have hTerminalT := tendsto_movingTerminalRank_atTop hbuffer
  have hRank1 := (tendsto_atTop.1 hTerminalT) 1
  have hRateBase : ∀ᶠ L : ℕ in atTop,
      firstPassageEndpointRate / 2 ≤
        firstPassageEndpointRate - D / (L : ℝ) := by
    have hcast : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hcast
    have hdiv : Tendsto (fun L : ℕ => D / (L : ℝ)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul hinv :
          Tendsto (fun L : ℕ => D * ((L : ℝ))⁻¹) atTop (nhds (D * 0)))
    have hrate : Tendsto
        (fun L : ℕ => firstPassageEndpointRate - D / (L : ℝ))
        atTop (nhds firstPassageEndpointRate) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact hrate.eventually (Ici_mem_nhds (by
      linarith [firstPassageEndpointRate_pos]))
  have hRate := hTerminalT.eventually hRateBase
  filter_upwards [hScalar, hRank1, hRate] with M hScalar hRank1 hRate
  let x : ℝ := (M : ℝ) + 2
  let L : ℕ := movingTerminalRank A M
  let H :=
    (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
  let b := firstPassageEndpointRate - D / (L : ℝ)
  let R := 1 + 6 / (P.run.rStar : ℝ)
  let Q := exactSharpCriticalLowSeriesConstant
    (firstPassageEndpointRate / 2) (C / 2)
  let E := Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))
  let Etimeout := Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))
  let Edy := ((L + 1 : ℕ) : ℝ) *
    Real.exp (-(Real.log 2 * (L : ℝ)))
  let Ahi := dHi + H * R * ((M : ℝ) + 1) ^ 2 * dHi
  have hL1 : 1 ≤ L := by simpa [L] using hRank1
  have hb : 0 < b := by
    dsimp [b, L]
    linarith [firstPassageEndpointRate_pos]
  have hsqrt : Real.sqrt (L + 1) ≤ 2 * Real.sqrt L := by
    have hcast : (L : ℝ) + 1 ≤ 4 * (L : ℝ) := by
      exact_mod_cast (show L + 1 ≤ 4 * L by omega)
    calc
      Real.sqrt (L + 1) ≤ Real.sqrt (4 * (L : ℝ)) :=
        Real.sqrt_le_sqrt hcast
      _ = Real.sqrt (4 : ℝ) * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt L := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
        rw [hsqrt4]
  have hexp : Real.exp (-(b * (L : ℝ))) ≤
      Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hsub : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast Nat.sub_le L 1
    nlinarith
  have htimeout : Etimeout ≤ 2 * E := by
    dsimp [Etimeout, E]
    calc
      Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ))) ≤
          (2 * Real.sqrt L) * Real.exp (-(b * (L : ℝ))) := by
        gcongr
      _ ≤ (2 * Real.sqrt L) *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
        gcongr
      _ = 2 * (Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by ring
  have hT0 : 0 ≤ timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1 := by
    have hrHi0 : 0 < (P.run.toTimeoutHigh.rHi : ℝ) :=
      P.run.toTimeoutHigh.pHi.r_pos
    have hsqrt1 : Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ) < 1 := by
      nlinarith [Real.sq_sqrt hrHi0.le,
        Real.sqrt_nonneg (P.run.toTimeoutHigh.rHi : ℝ),
        P.run.toTimeoutHigh.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ) :=
      sub_pos.mpr hsqrt1
    have hnum : 0 ≤
        P.run.toTimeoutHigh.D + P.run.toTimeoutHigh.tau + 3 := by
      linarith [P.run.toTimeoutHigh.D_pos,
        P.run.toTimeoutHigh.pHi.eta_pos]
    have hinner : 0 ≤
        (P.run.toTimeoutHigh.D + P.run.toTimeoutHigh.tau + 3) /
            (1 - Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    dsimp [timeoutTimeSupportConstant]
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    nlinarith [mul_nonneg hratio hinner]
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg hT0 (Real.sqrt_nonneg _)
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
  have hdHi0 : 0 ≤ dHi := by
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad := quadraticWindowShellConstant_pos.le
    positivity
  have hAhi0 : 0 ≤ Ahi := by
    dsimp [Ahi]
    positivity
  have hHQ0 : 0 ≤ H * R * Q := by positivity
  have hlowMul : H * R * Q * Etimeout ≤ H * R * Q * (2 * E) :=
    mul_le_mul_of_nonneg_left htimeout hHQ0
  have hOldLower : Ahi + H * R * Q * E ≤
      Ahi + H * R * Q * (Edy + E) := by
    have hEdy0 : 0 ≤ Edy := by dsimp [Edy]; positivity
    have hEE : E ≤ Edy + E := le_add_of_nonneg_left hEdy0
    have hmul : H * R * Q * E ≤ H * R * Q * (Edy + E) :=
      mul_le_mul_of_nonneg_left hEE hHQ0
    linarith
  have hCompare : Ahi + H * R * Q * Etimeout ≤
      2 * (Ahi + H * R * Q * (Edy + E)) := by
    calc
      Ahi + H * R * Q * Etimeout ≤
          Ahi + H * R * Q * (2 * E) := by gcongr
      _ = Ahi + 2 * (H * R * Q * E) := by ring
      _ ≤ 2 * (Ahi + H * R * Q * E) := by linarith
      _ ≤ 2 * (Ahi + H * R * Q * (Edy + E)) := by gcongr
  have hScalar2 := mul_le_mul_of_nonneg_left hScalar (by norm_num : (0 : ℝ) ≤ 2)
  dsimp only
  calc
    dHi + H * R * ((M : ℝ) + 1) ^ 2 * dHi +
        H * R * Q * Etimeout = Ahi + H * R * Q * Etimeout := by rfl
    _ ≤ 2 * (Ahi + H * R * Q * (Edy + E)) := hCompare
    _ ≤ 2 * (movingEndpointProfileConstant P C D *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) + x ^ (-P.epsilon))) := by
      simpa [Ahi, H, R, Q, E, Edy, dHi, L, b, x,
        timeoutTimeSupportConstant, movingTimeSupportConstant,
        ShrinkingBarrierRunData.toTimeoutHigh] using hScalar2
    _ = timeoutEndpointProfileConstant P C D *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) := by
      dsimp [timeoutEndpointProfileConstant, x]
      ring

/-- The timeout shell family satisfies the same vanishing error profile as
the public moving endpoint theorem. -/
theorem exists_eventually_timeoutEndpointGood_shellError
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio (timeoutEndpointGood P A M) M ≤
          C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by
  obtain ⟨C, D, hC, hD, hRaw⟩ :=
    exists_eventually_timeoutEndpointGood_rawProfile P hbuffer hUpper
  refine ⟨timeoutEndpointProfileConstant P C D, ?_, ?_⟩
  · unfold timeoutEndpointProfileConstant movingEndpointProfileConstant
    dsimp only
    have hK : 0 < 1 + quadraticWindowShellConstant := by
      linarith [quadraticWindowShellConstant_pos]
    have hT : 0 ≤ movingTimeSupportConstant P.run P.Cswitch + 1 := by
      have hrHi0 : 0 < (P.run.rHi : ℝ) := P.run.pHi.r_pos
      have hsqrt1 : Real.sqrt (P.run.rHi : ℝ) < 1 := by
        nlinarith [Real.sq_sqrt hrHi0.le, Real.sqrt_nonneg (P.run.rHi : ℝ),
          P.run.pHi.r_lt_one]
      have hden : 0 < 1 - Real.sqrt (P.run.rHi : ℝ) := sub_pos.mpr hsqrt1
      have hnum : 0 ≤ P.run.D + P.run.tau + 3 := by
        linarith [P.run.D_pos, P.run.pHi.eta_pos]
      have hinner : 0 ≤
          (P.run.D + P.run.tau + 3) /
              (1 - Real.sqrt (P.run.rHi : ℝ)) +
            (P.Cswitch + 5) ^ 2 := by positivity
      have hratio : 0 ≤ 2 / driftGap :=
        div_nonneg (by norm_num) driftGap_pos.le
      dsimp [movingTimeSupportConstant]
      nlinarith [mul_nonneg hratio hinner]
    have hR : 0 ≤ 1 + 6 / (P.run.rStar : ℝ) := by
      have hr : (0 : ℝ) < (P.run.rStar : ℝ) := by
        exact_mod_cast P.run.rStar_pos
      positivity
    have hQ : 0 ≤ exactSharpCriticalLowSeriesConstant
        (firstPassageEndpointRate / 2) (C / 2) :=
      (exactSharpCriticalLowSeriesConstant_spec
        (div_pos firstPassageEndpointRate_pos (by norm_num))
        (by positivity : 0 ≤ C / 2)).1.le
    positivity
  · have hScalar := eventually_timeoutEndpointRawProfile_le_shellError
      P hC hD hbuffer hUpper
    filter_upwards [hRaw, hScalar] with M hRaw hScalar
    exact hRaw.trans hScalar

end

end FirstPassageLinearTransport
