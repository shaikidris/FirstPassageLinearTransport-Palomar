/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TerminalTail

/-!
# Optimized terminal failure profile

This module connects the exact first-bad landing transport to the exponential
terminal-tail summation.  No checkpoint-congestion or suffix-balance hypothesis
is used.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

noncomputable section

/-- Real-valued form of the exact rank-by-rank generated first-bad transport
bound. -/
theorem generatedFirstBadSources_card_real_le
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((generatedFirstBadSources M L U H r t).card : ℝ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℝ) * (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
          (2 : ℝ) ^ M / (2 : ℝ) ^ q * ((landingBad q t).card : ℝ) := by
  have h := generatedFirstBadSources_card_le (H := H) t hr hUM hsmall
  exact_mod_cast h

/-- The rank-scaled transport multiplier is bounded by one linear factor. -/
theorem rank_transport_multiplier_le
    {r : ℝ} (hr : 0 < r) (q : ℕ) :
    1 + 3 * (((q + 2 : ℕ) : ℝ) / r) ≤
      (1 + 6 / r) * ((q + 1 : ℕ) : ℝ) := by
  have hq2 : ((q + 2 : ℕ) : ℝ) ≤ 2 * ((q + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q]
  have hdiv :
      ((q + 2 : ℕ) : ℝ) / r ≤
        (2 * ((q + 1 : ℕ) : ℝ)) / r :=
    (div_le_div_iff_of_pos_right hr).2 hq2
  calc
    1 + 3 * (((q + 2 : ℕ) : ℝ) / r) ≤
        1 + 3 * ((2 * ((q + 1 : ℕ) : ℝ)) / r) := by
      linarith
    _ = 1 + 6 * (((q + 1 : ℕ) : ℝ) / r) := by ring
    _ ≤ ((q + 1 : ℕ) : ℝ) +
        6 * (((q + 1 : ℕ) : ℝ) / r) := by
      norm_num
    _ = (1 + 6 / r) * ((q + 1 : ℕ) : ℝ) := by ring

theorem one_div_two_pow_eq_exp (q : ℕ) :
    1 / (2 : ℝ) ^ q = Real.exp (-(Real.log 2 * (q : ℝ))) := by
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  calc
    1 / (2 : ℝ) ^ q = 1 / (Real.exp (Real.log 2)) ^ q := by rw [htwo]
    _ = (Real.exp (Real.log 2) ^ q)⁻¹ := by rw [one_div]
    _ = Real.exp (-((q : ℝ) * Real.log 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
    _ = Real.exp (-(Real.log 2 * (q : ℝ))) := by ring_nf

/-- A shell-cardinality estimate becomes the sum of its one-point boundary
and entropy-density terms after division by the landing-shell size. -/
theorem landingBad_density_le
    {q : ℕ} (hq : 1 ≤ q) {t b : ℝ}
    (hcard : ((landingBad q t).card : ℝ) ≤
      1 + (2 : ℝ) ^ q *
        Real.exp (-(((q - 1 : ℕ) : ℝ) * b))) :
    ((landingBad q t).card : ℝ) / (2 : ℝ) ^ q ≤
      Real.exp (-(Real.log 2 * (q : ℝ))) +
        Real.exp b * Real.exp (-(b * (q : ℝ))) := by
  have hpow : 0 < (2 : ℝ) ^ q := by positivity
  have hdiv := (div_le_div_iff_of_pos_right hpow).2 hcard
  rw [add_div, mul_div_cancel_left₀ _ hpow.ne'] at hdiv
  rw [one_div_two_pow_eq_exp] at hdiv
  calc
    ((landingBad q t).card : ℝ) / (2 : ℝ) ^ q ≤
        Real.exp (-(Real.log 2 * (q : ℝ))) +
          Real.exp (-(((q - 1 : ℕ) : ℝ) * b)) := hdiv
    _ = Real.exp (-(Real.log 2 * (q : ℝ))) +
        Real.exp b * Real.exp (-(b * (q : ℝ))) := by
      rw [← Real.exp_add]
      congr 2
      rw [Nat.cast_sub hq]
      push_cast
      ring

/-- The dyadic boundary tail and entropy tail are both summable after one
linear rank loss, retaining arbitrary strict rate margins. -/
theorem terminal_rank_sum_le
    {b b' c' : ℝ}
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (L U : ℕ) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Real.exp b * Real.exp (-(b * (q : ℝ)))) ≤
      weightedTailConstant (Real.log 2) c' *
          Real.exp (-(c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(b' * (L : ℝ))) := by
  have hdyadic := weighted_exp_Icc_le hc' hc2 L U
  have hentropy := weighted_exp_Icc_le hb' hbb' L U
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Real.exp b * Real.exp (-(b * (q : ℝ)))) =
        (∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) *
            Real.exp (-(Real.log 2 * (q : ℝ)))) +
        Real.exp b *
          (∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) *
              Real.exp (-(b * (q : ℝ)))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        ∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) *
              (Real.exp b * Real.exp (-(b * (q : ℝ)))) =
            ∑ q ∈ Finset.Icc L U,
              Real.exp b * (((q + 1 : ℕ) : ℝ) *
                Real.exp (-(b * (q : ℝ)))) := by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ = Real.exp b *
            (∑ q ∈ Finset.Icc L U,
              ((q + 1 : ℕ) : ℝ) *
                Real.exp (-(b * (q : ℝ)))) :=
          (Finset.mul_sum (Finset.Icc L U)
            (fun q => ((q + 1 : ℕ) : ℝ) *
              Real.exp (-(b * (q : ℝ)))) (Real.exp b)).symm
    _ ≤ weightedTailConstant (Real.log 2) c' *
          Real.exp (-(c' * (L : ℝ))) +
        Real.exp b * weightedTailConstant b b' *
          Real.exp (-(b' * (L : ℝ))) := by
      have hscaled :=
        mul_le_mul_of_nonneg_left hentropy (Real.exp_pos b).le
      exact add_le_add hdyadic (by simpa [mul_assoc] using hscaled)

/-- Explicit terminal tail retained after spending strict entropy and dyadic
rate margins. -/
def terminalTailBound (b b' c' : ℝ) (L : ℕ) : ℝ :=
  weightedTailConstant (Real.log 2) c' *
      Real.exp (-(c' * (L : ℝ))) +
    Real.exp b * weightedTailConstant b b' *
      Real.exp (-(b' * (L : ℝ)))

/-- Complete terminal profile for generated first-bad sources, conditional
only on the displayed landing-shell cardinality estimate.  The conclusion
has no dependence on the number of recursive re-certification stages. -/
theorem generatedFirstBadSources_density_terminalProfile
    {M L U H : ℕ} {r : ℚ} {t b b' c' : ℝ}
    (hr : 0 < r) (hUM : U < M) (hL1 : 1 ≤ L)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hlanding : ∀ q ∈ Finset.Icc L U,
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) * b)))
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    ((generatedFirstBadSources M L U H r t).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (H : ℝ) * (1 + 6 / (r : ℝ)) *
        terminalTailBound b b' c' L := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hcard := generatedFirstBadSources_card_real_le (H := H) t hr hUM hsmall
  let C : ℝ := 1 + 6 / (r : ℝ)
  let profile : ℕ → ℝ := fun q =>
    ((q + 1 : ℕ) : ℝ) *
      (Real.exp (-(Real.log 2 * (q : ℝ))) +
        Real.exp b * Real.exp (-(b * (q : ℝ))))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hsummand : ∀ q ∈ Finset.Icc L U,
      (H : ℝ) * (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
          (2 : ℝ) ^ M / (2 : ℝ) ^ q *
            ((landingBad q t).card : ℝ) ≤
        (2 : ℝ) ^ M * ((H : ℝ) * C * profile q) := by
    intro q hq
    have hq1 : 1 ≤ q := hL1.trans (Finset.mem_Icc.mp hq).1
    have hmult := rank_transport_multiplier_le hrR q
    have hdensity := landingBad_density_le hq1 (hlanding q hq)
    have hHpow : 0 ≤ (H : ℝ) * (2 : ℝ) ^ M := by positivity
    have htargetDensity :
        0 ≤ ((landingBad q t).card : ℝ) / (2 : ℝ) ^ q := by
      positivity
    have hprofileBase :
        0 ≤ Real.exp (-(Real.log 2 * (q : ℝ))) +
          Real.exp b * Real.exp (-(b * (q : ℝ))) := by positivity
    calc
      (H : ℝ) * (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
          (2 : ℝ) ^ M / (2 : ℝ) ^ q *
            ((landingBad q t).card : ℝ) =
          ((H : ℝ) * (2 : ℝ) ^ M) *
            (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
            (((landingBad q t).card : ℝ) / (2 : ℝ) ^ q) := by ring
      _ ≤ ((H : ℝ) * (2 : ℝ) ^ M) *
          (C * ((q + 1 : ℕ) : ℝ)) *
            (((landingBad q t).card : ℝ) / (2 : ℝ) ^ q) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmult hHpow) htargetDensity
      _ ≤ ((H : ℝ) * (2 : ℝ) ^ M) *
          (C * ((q + 1 : ℕ) : ℝ)) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Real.exp b * Real.exp (-(b * (q : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left hdensity (by positivity)
      _ = (2 : ℝ) ^ M * ((H : ℝ) * C * profile q) := by
        dsimp [profile]
        ring
  have hsum :
      ((generatedFirstBadSources M L U H r t).card : ℝ) ≤
        (2 : ℝ) ^ M *
          ((H : ℝ) * C * ∑ q ∈ Finset.Icc L U, profile q) := by
    calc
      ((generatedFirstBadSources M L U H r t).card : ℝ) ≤
          ∑ q ∈ Finset.Icc L U,
            (H : ℝ) *
              (1 + 3 * (((q + 2 : ℕ) : ℝ) / (r : ℝ))) *
              (2 : ℝ) ^ M / (2 : ℝ) ^ q *
                ((landingBad q t).card : ℝ) := hcard
      _ ≤ ∑ q ∈ Finset.Icc L U,
          (2 : ℝ) ^ M * ((H : ℝ) * C * profile q) := by
        exact Finset.sum_le_sum hsummand
      _ = (2 : ℝ) ^ M *
          ((H : ℝ) * C * ∑ q ∈ Finset.Icc L U, profile q) := by
        rw [Finset.mul_sum, Finset.mul_sum]
  have hnormalized :
      ((generatedFirstBadSources M L U H r t).card : ℝ) /
          (2 : ℝ) ^ M ≤
        (H : ℝ) * C * ∑ q ∈ Finset.Icc L U, profile q := by
    apply (div_le_iff₀ hpowM).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  have htail := terminal_rank_sum_le hb' hbb' hc' hc2 L U
  have htailProfile :
      ∑ q ∈ Finset.Icc L U, profile q ≤
        weightedTailConstant (Real.log 2) c' *
            Real.exp (-(c' * (L : ℝ))) +
          Real.exp b * weightedTailConstant b b' *
            Real.exp (-(b' * (L : ℝ))) := by
    simpa [profile] using htail
  have hfinal := hnormalized.trans
    (mul_le_mul_of_nonneg_left htailProfile (mul_nonneg (Nat.cast_nonneg H) hC0))
  simpa [terminalTailBound] using hfinal

/-- Once the terminal rank is beyond the startup threshold, the
entropy-sharp landing bound holds simultaneously at every higher rank in a
finite re-certification interval. -/
theorem eventually_interval_card_landingBad_adjustable_le
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ L : ℕ in Filter.atTop, ∀ U q : ℕ, q ∈ Finset.Icc L U →
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have htail := eventually_card_landingBad_adjustable_le
    hlambda0 hlambda1 ht0 htA
  rw [Filter.eventually_atTop] at htail ⊢
  obtain ⟨q0, hq0⟩ := htail
  refine ⟨q0, ?_⟩
  intro L hL U q hq
  exact hq0 q (hL.trans (Finset.mem_Icc.mp hq).1)

end

end FirstPassageLinearTransport
