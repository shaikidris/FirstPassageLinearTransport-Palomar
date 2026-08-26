/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutExecution
import FirstPassageLinearTransport.MovingEndpointParameters
import FirstPassageLinearTransport.MovingEndpointAsymptotics

/-!
# Literal shell profile for the timeout endpoint

This joins the fixed shrinking-high profile to the sharp timeout tail.  The
low target contains no dyadic endpoint atom, so its contribution is only the
critical `sqrt L * exp (-b L)` term.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped BigOperators Real Topology

noncomputable section

/-- Full separated timeout-envelope estimate retaining the exact low rate. -/
theorem timeoutSeparatedFailureEnvelope_density_sharp_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {M L S : ℕ} {H dHi C b₀ b : ℝ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 2 ≤ L)
    (hH0 : 0 ≤ H) (hC : 0 ≤ C)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ q ∈ Finset.Icc L (M - 1),
      ((((q + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) ≤ H)
    (hInitial :
      ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤ dHi)
    (hHigh : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (timeoutHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤ dHi)
    (hLow : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        (C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (rStar : ℝ)) *
          exactSharpCriticalLowSeriesConstant b₀ C *
            (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
  have hLowSum := timeout_low_firstBad_sharp_sum_canonical_le
    hrStar hStarHi hStarLo hM hLS hSM hL hnextPos hnextLt
    (fun p hp =>
      have hpi := Finset.mem_Icc.mp hp
      hsmall p (Finset.mem_Icc.mpr
        ⟨(Nat.le_succ L).trans hpi.1,
          hpi.2.trans (Nat.le_pred_of_lt hSM)⟩))
    (fun p hp =>
      have hpi := Finset.mem_Icc.mp hp
      hTimes p (Finset.mem_Icc.mpr
        ⟨(Nat.le_succ L).trans hpi.1,
          hpi.2.trans (Nat.le_pred_of_lt hSM)⟩))
    hLow hC hb₀ hb₀b
  have hcardNat := timeoutSeparatedFailureEnvelope_card_le P K₀ M L S
  have hcard :
      ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) ≤
        ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) +
        ∑ p ∈ Finset.Icc (L + 1) S,
          ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) := by
    exact_mod_cast hcardNat
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hHighEach : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * dHi := by
    intro q hq
    have hqi := Finset.mem_Icc.mp hq
    have hqAll : q ∈ Finset.Icc L (M - 1) :=
      Finset.mem_Icc.mpr
        ⟨(Nat.le_succ L).trans
            (hLS.trans ((Nat.le_succ S).trans hqi.1)), hqi.2⟩
    have hqM : q < M := Nat.lt_of_le_pred (by omega) hqi.2
    apply timeoutHighFirstBadSourcesAtRank_density_le
      hrStar hStarHi hStarLo hM hqM (hsmall q hqAll)
      (hTimes q hqAll)
    simpa [timeoutHighTargetTolerance] using hHigh q hq
  have hdHi0 : 0 ≤ dHi := by
    have hnonneg : 0 ≤
        ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
          (2 : ℝ) ^ M := by positivity
    linarith
  have hHighSum :
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
            (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
    calc
      _ ≤ ∑ _q ∈ Finset.Icc (S + 1) (M - 1),
          H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) * dHi := by
        apply Finset.sum_le_sum
        intro q hq
        have hqi := Finset.mem_Icc.mp hq
        have hq1 : ((q + 1 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
          exact_mod_cast (show q + 1 ≤ M + 1 by omega)
        exact (hHighEach q hq).trans (by
          have hcoef0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) := by
            have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
            positivity
          gcongr)
      _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcardI : ((Finset.Icc (S + 1) (M - 1)).card : ℝ) ≤
            (M : ℝ) + 1 := by
          rw [Nat.card_Icc]
          exact_mod_cast (show M - 1 + 1 - (S + 1) ≤ M + 1 by omega)
        have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
        have hcoef0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) *
            ((M : ℝ) + 1) * dHi := by positivity
        calc
          ((Finset.Icc (S + 1) (M - 1)).card : ℝ) *
              (H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) * dHi) ≤
            ((M : ℝ) + 1) *
              (H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) * dHi) :=
            mul_le_mul_of_nonneg_right hcardI hcoef0
          _ = _ := by ring
  have hdiv :
      ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) /
          (2 : ℝ) ^ M ≤
        ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
            (2 : ℝ) ^ M +
        ∑ p ∈ Finset.Icc (L + 1) S,
          ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
            (2 : ℝ) ^ M := by
    have h := div_le_div_of_nonneg_right hcard hpowM.le
    simpa [add_div, Finset.sum_div] using h
  exact hdiv.trans (add_le_add (add_le_add hInitial hHighSum) hLowSum)

/-- Shellwise good set supplied by the timeout proof.  No existential low
stage package occurs in this definition. -/
def timeoutEndpointGood
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (A : ℕ → ℝ) (M : ℕ) : Set ℕ :=
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  {n | n ∉ timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M L S}

/-- The shell complement of the canonical timeout good set is exactly the
separated timeout envelope. -/
theorem shellBad_timeoutEndpointGood
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (A : ℕ → ℝ) (M : ℕ) :
    shellBad (timeoutEndpointGood P A M) M =
      timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M
        (movingTerminalRank A M) (shrinkingSwitchRank P.Cswitch M) := by
  classical
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  let E := timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M L S
  have hEnvelopeShell : ∀ n, n ∈ E → n ∈ dyadicShell M := by
    intro n hn
    dsimp [E] at hn
    unfold timeoutSeparatedFailureEnvelope at hn
    simp only [Finset.mem_union, Finset.mem_biUnion] at hn
    rcases hn with (hn | hn) | hn
    · exact (Finset.mem_filter.mp hn).1
    · rcases hn with ⟨q, _hq, hnq⟩
      exact (mem_timeoutHighFirstBadSourcesAtRank.mp hnq).1
    · rcases hn with ⟨q, _hq, hnq⟩
      exact (mem_timeoutFirstBadSourcesAtRank.mp hnq).1
  ext n
  rw [shellBad, Finset.mem_filter]
  constructor
  · intro hn
    have hnot : ¬ n ∉ E := by
      simpa [timeoutEndpointGood, E, L, S] using hn.2
    simpa [E] using not_not.mp hnot
  · intro hn
    have hnE : n ∈ E := by simpa [E] using hn
    refine ⟨hEnvelopeShell n hnE, ?_⟩
    simpa [timeoutEndpointGood, E, L, S] using hnE

end

end FirstPassageLinearTransport
