/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingTailAsymptotics
import FirstPassageLinearTransport.PolylogExceptionalCount
import FirstPassageLinearTransport.RankTransportAsymptotics

/-!
# Canonical shrinking-barrier fixed-polylogarithmic profile

This module joins the literal first-bad envelope to the shrinking-time-support
scalar estimate.  Its hypotheses expose only the fixed parameter margins; no
generated-distribution or checkpoint-congestion input occurs.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Canonical shellwise exceptional-density estimate for the shrinking
barrier and linear-log switch. -/
theorem eventually_shrinkingFailureEnvelope_density_polylog_le
    (P : ShrinkingBarrierRunData)
    {A C lambdaLo bLo' c' kappa : ℝ}
    (hA : 0 < A) (hC : 0 < C)
    (hAC : A / Real.log 2 < C)
    (hcap : P.D / Real.sqrt C ≤ P.tau)
    (hlambdaLo0 : 0 ≤ lambdaLo) (hlambdaLo1 : lambdaLo < 1)
    (hbLo' : 0 < bLo')
    (hLoRate : bLo' < adjustableEntropyRate lambdaLo P.etaLo)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (hHigh : kappa <
      min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2) - 5 / 2)
    (hLow : kappa < A * min bLo' c' / Real.log 2 - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      ((shrinkingSeparatedFailureEnvelope P M
          (polylogTerminalRank A M) (shrinkingSwitchRank C M)).card : ℝ) /
          (2 : ℝ) ^ M ≤
        shrinkingPolylogProfileConstant P C
            (adjustableEntropyRate lambdaLo P.etaLo) bLo' c' *
          (((M : ℝ) + 2) ^ (-kappa)) := by
  let bLo := adjustableEntropyRate lambdaLo P.etaLo
  have hTerminalT := tendsto_polylogTerminalRank_atTop hA
  have hLowBase := eventually_interval_card_landingBad_adjustable_le
    hlambdaLo0 hlambdaLo1 P.pLo.eta_pos P.etaLo_lt_a0
  have hLowTargets := hTerminalT.eventually hLowBase
  have hSmallBase := eventually_interval_rankTransport_small P.rStar_pos
  have hSmall := hTerminalT.eventually hSmallBase
  have hLS := eventually_polylogTerminalRank_lt_shrinkingSwitchRank hA.le hAC
  have hSM := eventually_shrinkingSwitchRank_lt_source hC.le
  have hScalar := eventually_shrinkingPolylogTerminalProfile_le_power P
    hA hC.le hbLo' (by simpa [bLo] using hLoRate) hc' hc2 hHigh hLow
  filter_upwards [hLowTargets, hSmall, hLS, hSM, hScalar,
      eventually_ge_atTop (max 1 P.pHi.M0)]
    with M hLowTargets hSmall hLS hSM hScalar hM
  let L := polylogTerminalRank A M
  let S := shrinkingSwitchRank C M
  let H := (shrinkingTimeSupportConstant P C + 1) *
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let dHi := shrinkingHighDensityProfile P C M
  have hM1 : 1 ≤ M := (le_max_left 1 P.pHi.M0).trans hM
  have hM0 : P.pHi.M0 ≤ M := (le_max_right 1 P.pHi.M0).trans hM
  have hL1 : 1 ≤ L := by
    dsimp [L]
    exact polylogTerminalRank_pos hA M
  have hLS' : L ≤ S := by dsimp [L, S]; exact hLS.le
  have hSM' : S < M := by simpa [S] using hSM
  have hH0 : 0 ≤ H := by
    dsimp [H]
    have hT := shrinkingTimeSupportConstant_pos P hC.le
    positivity
  have hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((shrinkingFeasibleTimes P M S q).card : ℝ) ≤ H := by
    intro q hq
    have hSwitchSucc : S < M + 1 := by omega
    have hbound := shrinkingFeasibleTimes_card_lt_sqrt P hC.le hM1
      hSwitchSucc (q := q)
    exact hbound.le
  have hInitial :
      ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
          (2 : ℝ) ^ M ≤ dHi := by
    have hbase := card_shellInitialWindowBad_shrinking_le P hC hcap hM1 hSM.le
    dsimp [dHi, shrinkingHighDensityProfile]
    have hboundary : 0 ≤
        Real.exp (-(Real.log 2 * (shrinkingSwitchRank C M : ℝ))) :=
      Real.exp_pos _ |>.le
    linarith
  have hHighTargets : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) /
          (2 : ℝ) ^ q ≤ dHi := by
    intro q hq
    have hqLower := (Finset.mem_Icc.mp hq).1
    have hq1 : 1 ≤ q := by omega
    have hSParent : shrinkingSwitchRank C M ≤ q - 1 := by
      simpa [S] using (show S ≤ q - 1 by omega)
    have hbase := card_landingBad_shrinking_high_density_le
      P hC hcap hq1 hSParent
    have hqS : (S : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show S ≤ q by omega)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hexp :
        Real.exp (-(Real.log 2 * (q : ℝ))) ≤
          Real.exp (-(Real.log 2 * (S : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad : 0 ≤ quadraticWindowShellConstant / 2 *
        Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
          Real.log ((M : ℝ) + 2))) := by
      have := quadraticWindowShellConstant_pos
      positivity
    exact hbase.trans (by
      calc
        _ ≤ Real.exp (-(Real.log 2 * (S : ℝ))) +
            quadraticWindowShellConstant / 2 *
              Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := add_le_add hexp le_rfl
        _ ≤ Real.exp (-(Real.log 2 * (S : ℝ))) +
            quadraticWindowShellConstant *
              Real.exp (-(maximalBarrierC0 * P.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := by
          gcongr
          linarith [quadraticWindowShellConstant_pos]
        _ = _ := rfl)
  have hProfile := shrinkingSeparatedFailureEnvelope_density_terminalProfile
    P (M := M) (L := L) (S := S) (H := H) (dHi := dHi)
    (bLo := bLo) (bLo' := bLo') (c' := c')
    hLS' hSM' hL1 hH0
    (fun q hq => hSmall (M - 1) q hq)
    hTimes hInitial hHighTargets
    (fun q hq => hLowTargets S q hq)
    hbLo' (by simpa [bLo] using hLoRate) hc' hc2
  exact hProfile.trans (by simpa [L, S, H, dHi, bLo] using hScalar)

/-- Per-shell good set obtained by removing the literal shrinking-barrier
failure envelope. -/
def shrinkingPolylogGood
    (P : ShrinkingBarrierRunData) (A C : ℝ) (M : ℕ) : Set ℕ :=
  {n | n ∉ shrinkingSeparatedFailureEnvelope P M
    (polylogTerminalRank A M) (shrinkingSwitchRank C M)}

theorem shellBad_shrinkingPolylogGood
    (P : ShrinkingBarrierRunData) (A C : ℝ) (M : ℕ) :
    shellBad (shrinkingPolylogGood P A C M) M =
      shrinkingSeparatedFailureEnvelope P M
        (polylogTerminalRank A M) (shrinkingSwitchRank C M) := by
  classical
  ext n
  constructor
  · intro hn
    rw [shellBad, Finset.mem_filter] at hn
    have hnot : ¬ n ∉ shrinkingSeparatedFailureEnvelope P M
        (polylogTerminalRank A M) (shrinkingSwitchRank C M) := by
      simpa [shrinkingPolylogGood] using hn.2
    exact not_not.mp hnot
  · intro hn
    have hnShell : n ∈ dyadicShell M := by
      unfold shrinkingSeparatedFailureEnvelope at hn
      simp only [Finset.mem_union, Finset.mem_biUnion] at hn
      rcases hn with (hn | hn) | hn
      · exact (Finset.mem_filter.mp hn).1
      · rcases hn with ⟨q, _hq, hnq⟩
        exact (mem_shrinkingFirstBadSourcesAtRank.mp hnq).1
      · rcases hn with ⟨q, _hq, hnq⟩
        exact (mem_shrinkingFirstBadSourcesAtRank.mp hnq).1
    rw [shellBad, Finset.mem_filter]
    refine ⟨hnShell, ?_⟩
    simpa [shrinkingPolylogGood] using (show ¬ n ∉
      shrinkingSeparatedFailureEnvelope P M
        (polylogTerminalRank A M) (shrinkingSwitchRank C M) from
      not_not.mpr hn)

end

end FirstPassageLinearTransport
