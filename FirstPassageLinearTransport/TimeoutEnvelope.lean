/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutProfile

/-!
# Separated timeout failure envelope

Initial high failures, first failed high certifications, and first low
timeouts are kept as three literal pieces.  The low piece targets the
checkpoint before the failed timeout block.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

noncomputable section

/-- The high certification tolerance attached to a landing of threshold
rank `q`. -/
def timeoutHighTargetTolerance
    (P : TimeoutHighRunData) (M q : ℕ) : ℝ :=
  timeoutHighTolerance P M (q - 1)

/-- Generated endpoints whose next high certification fails. -/
noncomputable def timeoutHighFirstBadSourcesAtRank
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S q : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h q ∧
      orbit h n ∈ landingBad q (timeoutHighTargetTolerance P M q)

@[simp] theorem mem_timeoutHighFirstBadSourcesAtRank
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S q n : ℕ} :
    n ∈ timeoutHighFirstBadSourcesAtRank P K₀ L M S q ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h q ∧
          orbit h n ∈ landingBad q (timeoutHighTargetTolerance P M q) := by
  classical
  simp [timeoutHighFirstBadSourcesAtRank]

theorem timeoutHighFirstBadSourcesAtRank_subset_transport
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) :
    timeoutHighFirstBadSourcesAtRank P K₀ L M S q ⊆
      lossFilteredTransportedSourcesAtTimes M (2 ^ q)
        (timeoutFeasibleTimes P K₀ L M S q)
        (landingBad q (timeoutHighTargetTolerance P M q))
        (((q + 2 : ℕ) : ℚ) / rStar) := by
  classical
  intro n hn
  rcases mem_timeoutHighFirstBadSourcesAtRank.mp hn with
    ⟨hnShell, h, hrun, hbad⟩
  apply mem_lossFilteredTransportedSourcesAtTimes.mpr
  refine ⟨hnShell, h, ?_, hrun.directFirstPassage, hbad, ?_⟩
  · exact hrun.mem_timeoutFeasibleTimes hM hnShell
  · exact hrun.scaledReverseLoss_le hrStar hStarHi hStarLo

theorem timeoutHighFirstBadSourcesAtRank_card_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℚ) ≤
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℚ) *
        (1 + 3 * (((q + 2 : ℕ) : ℚ) / rStar)) *
          (2 : ℚ) ^ M / ((2 ^ q : ℕ) : ℚ) *
        ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℚ) := by
  have hsubset := timeoutHighFirstBadSourcesAtRank_subset_transport
    (S := S) (q := q) hrStar hStarHi hStarLo hM
  have hcardNat := Finset.card_le_card hsubset
  have hcardQ :
      ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℚ) ≤
        ((lossFilteredTransportedSourcesAtTimes M (2 ^ q)
          (timeoutFeasibleTimes P K₀ L M S q)
          (landingBad q (timeoutHighTargetTolerance P M q))
          (((q + 2 : ℕ) : ℚ) / rStar)).card : ℚ) := by
    exact_mod_cast hcardNat
  exact hcardQ.trans
    (lossFiltered_arbitraryTarget_transport_atTimes_uniform
      (timeoutFeasibleTimes P K₀ L M S q)
      (landingBad q (timeoutHighTargetTolerance P M q))
      (by positivity)
      (div_nonneg (by positivity) hrStar.le) hsmall
      (Nat.pow_lt_pow_right (by omega) hqM))

/-- Real rankwise density for a failed high certification. -/
theorem timeoutHighFirstBadSourcesAtRank_density_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) ≤ H)
    (hTarget :
      ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
        (2 : ℝ) ^ q ≤ d) :
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
  have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hcardQ := timeoutHighFirstBadSourcesAtRank_card_le
    (S := S) hrStar hStarHi hStarLo hM hqM hsmall
  have hcard :
      ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) ≤
        ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) := by
    exact_mod_cast hcardQ
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hmult := rank_transport_multiplier_le hrR q
  have hTimes0 : 0 ≤
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) := by positivity
  calc
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ)) /
            (2 : ℝ) ^ M := div_le_div_of_nonneg_right hcard hpowM.le
    _ = ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
        (1 + 3 * (((q + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
        (((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
          (2 : ℝ) ^ q) := by field_simp
    _ ≤ ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) *
        ((1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
        (((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
          (2 : ℝ) ^ q) := by
      have := hmult
      gcongr
    _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
      have hH0 : 0 ≤ H := hTimes0.trans hTimes
      have hT0 : 0 ≤
          ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
            (2 : ℝ) ^ q := by positivity
      calc
        _ ≤ H * ((1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
            (((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
              (2 : ℝ) ^ q) := by gcongr
        _ ≤ H * ((1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) * d := by
          gcongr
        _ = _ := by ring

/-- Initial high failure, high-rank first bad certification, and low first
timeout. -/
noncomputable def timeoutSeparatedFailureEnvelope
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (M L S : ℕ) : Finset ℕ := by
  classical
  exact shellInitialWindowBad M (timeoutHighTolerance P M M) ∪
    ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
      timeoutHighFirstBadSourcesAtRank P K₀ L M S q) ∪
    ((Finset.Icc (L + 1) S).biUnion fun p =>
      timeoutFirstBadSourcesAtRank P K₀ L M S p)

theorem timeoutSeparatedFailureEnvelope_card_le
    (P : TimeoutHighRunData) (K₀ : ℝ) (M L S : ℕ) :
    (timeoutSeparatedFailureEnvelope P K₀ M L S).card ≤
      (shellInitialWindowBad M (timeoutHighTolerance P M M)).card +
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
        (timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card +
      ∑ p ∈ Finset.Icc (L + 1) S,
        (timeoutFirstBadSourcesAtRank P K₀ L M S p).card := by
  classical
  unfold timeoutSeparatedFailureEnvelope
  calc
    _ ≤ (shellInitialWindowBad M (timeoutHighTolerance P M M) ∪
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          timeoutHighFirstBadSourcesAtRank P K₀ L M S q)).card +
        ((Finset.Icc (L + 1) S).biUnion fun p =>
          timeoutFirstBadSourcesAtRank P K₀ L M S p).card :=
      Finset.card_union_le _ _
    _ ≤ (shellInitialWindowBad M (timeoutHighTolerance P M M)).card +
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card +
        ((Finset.Icc (L + 1) S).biUnion fun p =>
          timeoutFirstBadSourcesAtRank P K₀ L M S p).card := by
      have hfirst := Finset.card_union_le
        (shellInitialWindowBad M (timeoutHighTolerance P M M))
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          timeoutHighFirstBadSourcesAtRank P K₀ L M S q)
      omega
    _ ≤ _ := by
      have hHigh := card_biUnion_le_sum (Finset.Icc (S + 1) (M - 1))
        (fun q => timeoutHighFirstBadSourcesAtRank P K₀ L M S q)
      have hLow := card_biUnion_le_sum (Finset.Icc (L + 1) S)
        (fun p => timeoutFirstBadSourcesAtRank P K₀ L M S p)
      omega

end

end FirstPassageLinearTransport
