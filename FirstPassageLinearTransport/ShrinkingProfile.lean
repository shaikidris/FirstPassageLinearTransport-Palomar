/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingFirstBad

/-!
# Support-sensitive shrinking-barrier terminal profile

The low-rank contribution is summed with the same exponential tail as the
fixed-tolerance proof, but its multiplicative time cost is now the feasible
support cardinality.  The high-rank and low-rank targets remain separate so
that the variable high tolerance is never replaced by a fixed one.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

noncomputable section

theorem shrinkingTargetTolerance_eq_high
    (P : ShrinkingBarrierRunData) {M S q : ℕ} (hSq : S < q) :
    shrinkingTargetTolerance P M S q =
      shrinkingHighTolerance P M (q - 1) := by
  unfold shrinkingTargetTolerance
  rw [if_pos (by omega)]

theorem shrinkingTargetTolerance_eq_low
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hq1 : 1 ≤ q) (hqS : q ≤ S) :
    shrinkingTargetTolerance P M S q = P.etaLo := by
  unfold shrinkingTargetTolerance
  rw [if_neg (by omega)]

/-- Three-piece envelope used by the paper proof: initial failure, high-rank
first failure, and low-rank first failure. -/
noncomputable def shrinkingSeparatedFailureEnvelope
    (P : ShrinkingBarrierRunData) (M L S : ℕ) : Finset ℕ := by
  classical
  exact shellInitialWindowBad M (shrinkingHighTolerance P M M) ∪
    ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
      shrinkingFirstBadSourcesAtRank P M S q) ∪
    ((Finset.Icc L S).biUnion fun q =>
      shrinkingFirstBadSourcesAtRank P M S q)

theorem shrinkingSeparatedFailureEnvelope_card_le
    (P : ShrinkingBarrierRunData) (M L S : ℕ) :
    (shrinkingSeparatedFailureEnvelope P M L S).card ≤
      (shellInitialWindowBad M (shrinkingHighTolerance P M M)).card +
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
        (shrinkingFirstBadSourcesAtRank P M S q).card +
      ∑ q ∈ Finset.Icc L S,
        (shrinkingFirstBadSourcesAtRank P M S q).card := by
  classical
  unfold shrinkingSeparatedFailureEnvelope
  calc
    _ ≤ (shellInitialWindowBad M (shrinkingHighTolerance P M M) ∪
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q)).card +
        ((Finset.Icc L S).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q).card :=
      Finset.card_union_le _ _
    _ ≤ ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card +
        ((Finset.Icc (S + 1) (M - 1)).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q).card) +
        ((Finset.Icc L S).biUnion fun q =>
          shrinkingFirstBadSourcesAtRank P M S q).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ (shellInitialWindowBad M (shrinkingHighTolerance P M M)).card +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          (shrinkingFirstBadSourcesAtRank P M S q).card +
        ∑ q ∈ Finset.Icc L S,
          (shrinkingFirstBadSourcesAtRank P M S q).card := by
      apply Nat.add_le_add
      · exact Nat.add_le_add_left
          (card_biUnion_le_sum (Finset.Icc (S + 1) (M - 1)) fun q =>
            shrinkingFirstBadSourcesAtRank P M S q) _
      · exact card_biUnion_le_sum (Finset.Icc L S) fun q =>
          shrinkingFirstBadSourcesAtRank P M S q

/-- Real rankwise density estimate after the support-sensitive transport
and the linear rank multiplier are applied. -/
theorem shrinkingFirstBadSourcesAtRank_density_le
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / P.rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((shrinkingFeasibleTimes P M S q).card : ℝ) ≤ H)
    (hTarget :
      ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
        (2 : ℝ) ^ q ≤ d) :
    ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
  have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
  have hcardQ := shrinkingFirstBadSourcesAtRank_card_le P
    (M := M) (S := S) (q := q) hqM hsmall
  have hcard :
      ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) ≤
        ((shrinkingFeasibleTimes P M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (P.rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) := by
    exact_mod_cast hcardQ
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hpowq : 0 < (2 : ℝ) ^ q := by positivity
  have hmult := rank_transport_multiplier_le hrR q
  have hTimes0 : 0 ≤
      ((shrinkingFeasibleTimes P M S q).card : ℝ) := by positivity
  have hTarget0 : 0 ≤
      ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
        (2 : ℝ) ^ q := by positivity
  calc
    ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((shrinkingFeasibleTimes P M S q).card : ℝ) *
          (1 + 3 * (((q + 2 : ℕ) : ℝ) / (P.rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ q *
          ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ)) /
            (2 : ℝ) ^ M := div_le_div_of_nonneg_right hcard hpowM.le
    _ = ((shrinkingFeasibleTimes P M S q).card : ℝ) *
        (1 + 3 * (((q + 2 : ℕ) : ℝ) / (P.rStar : ℝ))) *
        (((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
          (2 : ℝ) ^ q) := by field_simp
    _ ≤ ((shrinkingFeasibleTimes P M S q).card : ℝ) *
        ((1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
        (((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
          (2 : ℝ) ^ q) := by
      gcongr
    _ ≤ H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by
      have hC : 0 ≤ 1 + 6 / (P.rStar : ℝ) := by positivity
      have hq0 : 0 ≤ ((q + 1 : ℕ) : ℝ) := by positivity
      have hH0 : 0 ≤ H := hTimes0.trans hTimes
      calc
        _ ≤ H * ((1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) *
            (((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
              (2 : ℝ) ^ q) := by
          gcongr
        _ ≤ H * ((1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ)) * d := by
          gcongr
        _ = _ := by ring

/-- Conditional master profile.  Its hypotheses are exactly the initial,
high-target, low-target, and compressed-time estimates supplied separately
by the barrier and schedule modules. -/
theorem shrinkingSeparatedFailureEnvelope_density_terminalProfile
    (P : ShrinkingBarrierRunData)
    {M L S : ℕ} {H dHi bLo bLo' c' : ℝ}
    (hLS : L ≤ S) (hSM : S < M) (hL1 : 1 ≤ L)
    (hH0 : 0 ≤ H)
    (hsmall : ∀ q ∈ Finset.Icc L (M - 1),
      ((((q + 2 : ℕ) : ℚ) / P.rStar) /
        ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((shrinkingFeasibleTimes P M S q).card : ℝ) ≤ H)
    (hInitial :
      ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤ dHi)
    (hHigh : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤ dHi)
    (hLow : ∀ q ∈ Finset.Icc L S,
      ((landingBad q P.etaLo).card : ℝ) ≤
        1 + (2 : ℝ) ^ q * Real.exp (-(((q - 1 : ℕ) : ℝ) * bLo)))
    (hbLo' : 0 < bLo') (hLoRate : bLo' < bLo)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    ((shrinkingSeparatedFailureEnvelope P M L S).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (P.rStar : ℝ)) *
        (((M : ℝ) + 1) ^ 2 * dHi + terminalTailBound bLo bLo' c' L) := by
  have hcardNat := shrinkingSeparatedFailureEnvelope_card_le P M L S
  have hcard :
      ((shrinkingSeparatedFailureEnvelope P M L S).card : ℝ) ≤
        ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) +
        ∑ q ∈ Finset.Icc L S,
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) := by
    exact_mod_cast hcardNat
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hHighEach : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * dHi := by
    intro q hq
    have hqAll : q ∈ Finset.Icc L (M - 1) := by
      have hqi := Finset.mem_Icc.mp hq
      exact Finset.mem_Icc.mpr ⟨hLS.trans (by omega), hqi.2⟩
    apply shrinkingFirstBadSourcesAtRank_density_le P
      (by have := (Finset.mem_Icc.mp hqAll).2; omega) (hsmall q hqAll)
      (hTimes q hqAll)
    rw [shrinkingTargetTolerance_eq_high P (Finset.mem_Icc.mp hq).1]
    exact hHigh q hq
  have hLowEach : ∀ q ∈ Finset.Icc L S,
      ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Real.exp bLo * Real.exp (-(bLo * (q : ℝ)))) := by
    intro q hq
    have hqi := Finset.mem_Icc.mp hq
    have hqAll : q ∈ Finset.Icc L (M - 1) := by
      exact Finset.mem_Icc.mpr ⟨hqi.1, by omega⟩
    apply shrinkingFirstBadSourcesAtRank_density_le P
      (by omega) (hsmall q hqAll)
      (hTimes q hqAll)
    rw [shrinkingTargetTolerance_eq_low P (hL1.trans hqi.1) hqi.2]
    exact landingBad_density_le (hL1.trans hqi.1) (hLow q hq)
  have hHighSum :
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
            (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
    have hdHi0 : 0 ≤ dHi := by
      have hnonneg : 0 ≤
          ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M := by positivity
      linarith
    calc
      _ ≤ ∑ _q ∈ Finset.Icc (S + 1) (M - 1),
          H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) * dHi := by
        apply Finset.sum_le_sum
        intro q hq
        have hqM := (Finset.mem_Icc.mp hq).2
        have hq1 : ((q + 1 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
          exact_mod_cast (by omega : q + 1 ≤ M + 1)
        have hbase := hHighEach q hq
        have hnonneg : 0 ≤ H * (1 + 6 / (P.rStar : ℝ)) := by
          have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
          positivity
        exact hbase.trans (by gcongr)
      _ ≤ H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.Icc (S + 1) (M - 1)).card : ℝ) ≤
            (M : ℝ) + 1 := by
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : M - 1 + 1 - (S + 1) ≤ M + 1)
        have hcoef0 : 0 ≤ H * (1 + 6 / (P.rStar : ℝ)) *
            ((M : ℝ) + 1) * dHi := by
          have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
          positivity
        calc
          ((Finset.Icc (S + 1) (M - 1)).card : ℝ) *
              (H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) * dHi) ≤
            ((M : ℝ) + 1) *
              (H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) * dHi) :=
            mul_le_mul_of_nonneg_right hcard hcoef0
          _ = _ := by ring
  have hLowSum :
      ∑ q ∈ Finset.Icc L S,
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
            (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * terminalTailBound bLo bLo' c' L := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc L S,
          H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Real.exp bLo * Real.exp (-(bLo * (q : ℝ)))) := by
        exact Finset.sum_le_sum hLowEach
      _ = H * (1 + 6 / (P.rStar : ℝ)) *
          (∑ q ∈ Finset.Icc L S, ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Real.exp bLo * Real.exp (-(bLo * (q : ℝ))))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ H * (1 + 6 / (P.rStar : ℝ)) * terminalTailBound bLo bLo' c' L := by
        have htail := terminal_rank_sum_le hbLo' hLoRate hc' hc2 L S
        have hcoef0 : 0 ≤ H * (1 + 6 / (P.rStar : ℝ)) := by
          have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
          positivity
        exact mul_le_mul_of_nonneg_left htail hcoef0
  have hdiv :
      ((shrinkingSeparatedFailureEnvelope P M L S).card : ℝ) /
          (2 : ℝ) ^ M ≤
        ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc (S + 1) (M - 1),
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc L S,
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M := by
    have := div_le_div_of_nonneg_right hcard hpowM.le
    simpa [add_div, Finset.sum_div] using this
  calc
    _ ≤ ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc (S + 1) (M - 1),
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc L S,
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M := hdiv
    _ ≤ dHi +
        H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.rStar : ℝ)) * terminalTailBound bLo bLo' c' L :=
      add_le_add (add_le_add hInitial hHighSum) hLowSum
    _ = dHi + H * (1 + 6 / (P.rStar : ℝ)) *
        (((M : ℝ) + 1) ^ 2 * dHi + terminalTailBound bLo bLo' c' L) := by ring

end

end FirstPassageLinearTransport
