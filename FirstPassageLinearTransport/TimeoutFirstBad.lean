/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutTimeSupport
import FirstPassageLinearTransport.TimeSupportTransport

/-!
# First-timeout transport

A low timeout occurs at a checkpoint produced by the preceding successful
block.  This module counts that checkpoint as a direct first-passage target;
it never invents an endpoint for the failed block.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- Timeout checkpoints in the landing band below `2^p`. -/
noncomputable def timeoutLandingBad
    (K₀ : ℝ) (L p : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell (p - 1)).filter (LowStageTimeout K₀ L (p - 1))

theorem timeoutLandingBad_eq_timeoutShellBad
    (K₀ : ℝ) (L p : ℕ) :
    timeoutLandingBad K₀ L p = timeoutShellBad K₀ L (p - 1) := by
  rfl

/-- A timeout run endpoint at rank `p` that times out in its own shell lies
in the literal timeout landing target.  The dyadic upper endpoint is excluded
by its exact halving orbit. -/
theorem TimeoutRecertificationRun.endpoint_mem_timeoutLandingBad
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed p : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed p)
    (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (htimeout : LowStageTimeout K₀ L (p - 1) (orbit elapsed n)) :
    orbit elapsed n ∈ timeoutLandingBad K₀ L p := by
  classical
  have hband := hrun.landingBand
  have hne : orbit elapsed n ≠ 2 ^ p := by
    intro heq
    have hnot := not_lowStageTimeout_two_pow_succ
      (m := p - 1) hnextPos (by simpa [Nat.sub_add_cancel hp] using hnextLt)
    apply hnot
    simpa [heq, Nat.sub_add_cancel hp] using htimeout
  have hlower : 2 ^ (p - 1) ≤ orbit elapsed n := by
    have hmul : 2 ^ (p - 1) * 2 < orbit elapsed n * 2 := by
      calc
        2 ^ (p - 1) * 2 = 2 ^ ((p - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ p := by rw [Nat.sub_add_cancel hp]
        _ < 2 * orbit elapsed n := hband.1
        _ = orbit elapsed n * 2 := by omega
    exact (lt_of_mul_lt_mul_right hmul (by norm_num)).le
  have hupper : orbit elapsed n < 2 ^ p := lt_of_le_of_ne hband.2 hne
  rw [timeoutLandingBad, Finset.mem_filter, mem_dyadicShell]
  exact ⟨⟨hlower, by simpa [Nat.sub_add_cancel hp] using hupper⟩, htimeout⟩

/-- Sources in one outer shell whose generated checkpoint of rank `p` is the
first low timeout target. -/
noncomputable def timeoutFirstBadSourcesAtRank
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S p : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h p ∧
      LowStageTimeout K₀ L (p - 1) (orbit h n)

@[simp] theorem mem_timeoutFirstBadSourcesAtRank
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S p n : ℕ} :
    n ∈ timeoutFirstBadSourcesAtRank P K₀ L M S p ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, TimeoutRecertificationRun P K₀ L M S n h p ∧
          LowStageTimeout K₀ L (p - 1) (orbit h n) := by
  classical
  simp [timeoutFirstBadSourcesAtRank]

/-- Every first timeout is a direct, loss-filtered transport into the actual
timeout target, using only feasible times of successful prefixes. -/
theorem timeoutFirstBadSourcesAtRank_subset_transport
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S p : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p) :
    timeoutFirstBadSourcesAtRank P K₀ L M S p ⊆
      lossFilteredTransportedSourcesAtTimes M (2 ^ p)
        (timeoutFeasibleTimes P K₀ L M S p)
        (timeoutLandingBad K₀ L p)
        (((p + 2 : ℕ) : ℚ) / rStar) := by
  classical
  intro n hn
  rcases mem_timeoutFirstBadSourcesAtRank.mp hn with
    ⟨hnShell, h, hrun, htimeout⟩
  apply mem_lossFilteredTransportedSourcesAtTimes.mpr
  refine ⟨hnShell, h, ?_, hrun.directFirstPassage, ?_, ?_⟩
  · exact hrun.mem_timeoutFeasibleTimes hM hnShell
  · exact hrun.endpoint_mem_timeoutLandingBad hp hnextPos hnextLt htimeout
  · exact hrun.scaledReverseLoss_le hrStar hStarHi hStarLo

/-- Exact rankwise timeout count with compressed feasible-time support. -/
theorem timeoutFirstBadSourcesAtRank_card_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S p : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (hpM : p < M)
    (hsmall : ((((p + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3) :
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℚ) ≤
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℚ) *
        (1 + 3 * (((p + 2 : ℕ) : ℚ) / rStar)) *
          (2 : ℚ) ^ M / ((2 ^ p : ℕ) : ℚ) *
        ((timeoutLandingBad K₀ L p).card : ℚ) := by
  have hsubset := timeoutFirstBadSourcesAtRank_subset_transport
    (S := S) hrStar hStarHi hStarLo hM hp hnextPos hnextLt
  have hcardNat := Finset.card_le_card hsubset
  have hcardQ :
      ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℚ) ≤
        ((lossFilteredTransportedSourcesAtTimes M (2 ^ p)
          (timeoutFeasibleTimes P K₀ L M S p)
          (timeoutLandingBad K₀ L p)
          (((p + 2 : ℕ) : ℚ) / rStar)).card : ℚ) := by
    exact_mod_cast hcardNat
  exact hcardQ.trans
    (lossFiltered_arbitraryTarget_transport_atTimes_uniform
      (timeoutFeasibleTimes P K₀ L M S p)
      (timeoutLandingBad K₀ L p)
      (by positivity)
      (div_nonneg (by positivity) hrStar.le) hsmall
      (Nat.pow_lt_pow_right (by omega) hpM))

end

end FirstPassageLinearTransport
