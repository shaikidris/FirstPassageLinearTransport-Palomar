/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingBarrierCore
import FirstPassageLinearTransport.TwoRegimeClock

/-!
# Literal shrinking-barrier re-certification runs

The high-rank tolerance depends on the outer shell and the current parent
rank.  This module keeps that dependence in the literal stopped-map run while
retaining the common rank-scaled loss and geometric-clock interfaces.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- Fixed data used by the shrinking-barrier run.  The high package is built
at a cap `tau`; each actual high block reuses it at a smaller tolerance. -/
structure ShrinkingBarrierRunData where
  rHi : ℚ
  rLo : ℚ
  rStar : ℚ
  tau : ℝ
  etaLo : ℝ
  D : ℝ
  pHi : StageSetup (rHi : ℝ) tau
  pLo : StageSetup (rLo : ℝ) etaLo
  D_pos : 0 < D
  tau_lt_a0 : tau < a0
  etaLo_lt_a0 : etaLo < a0
  rStar_eq : rStar = min rHi rLo
  rStar_pos : 0 < rStar

/-- Paper tolerance `D * sqrt(log(M+2)/m)`, totalized at the irrelevant
rank `m=0` and capped by the fixed high package tolerance. -/
def shrinkingHighTolerance
    (P : ShrinkingBarrierRunData) (M m : ℕ) : ℝ :=
  if m = 0 then P.tau
  else min P.tau
    (P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)))

theorem shrinkingHighTolerance_pos
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    0 < shrinkingHighTolerance P M m := by
  unfold shrinkingHighTolerance
  split_ifs with hm
  · exact P.pHi.eta_pos
  · apply lt_min P.pHi.eta_pos
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hlog : 0 < Real.log ((M : ℝ) + 2) := by
      apply Real.log_pos
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    exact mul_pos P.D_pos (Real.sqrt_pos.2 (div_pos hlog hm0))

theorem shrinkingHighTolerance_le_tau
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    shrinkingHighTolerance P M m ≤ P.tau := by
  unfold shrinkingHighTolerance
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem shrinkingHighTolerance_lt_a0
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    shrinkingHighTolerance P M m < a0 :=
  (shrinkingHighTolerance_le_tau P M m).trans_lt P.tau_lt_a0

/-- The literal stage package at one high rank. -/
def shrinkingHighSetup
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    StageSetup (P.rHi : ℝ) (shrinkingHighTolerance P M m) :=
  P.pHi.lowerTolerance (shrinkingHighTolerance P M m)
    (shrinkingHighTolerance_pos P M m)
    (shrinkingHighTolerance_le_tau P M m)

@[simp] theorem shrinkingHighSetup_M0
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    (shrinkingHighSetup P M m).M0 = P.pHi.M0 := rfl

/-- Literal stopped-map chain for the paper's shrinking high barrier and
fixed low barrier. -/
inductive ShrinkingRecertificationRun
    (P : ShrinkingBarrierRunData) (M S n : ℕ) : ℕ → ℕ → Prop
  | first
      (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
      (hnShell : n ∈ dyadicShell M)
      (hnGood : n ∈ initialWindowGood (shrinkingHighTolerance P M M)) :
      ShrinkingRecertificationRun P M S n
        (stageLength (shrinkingHighSetup P M M) n)
        (rationalTargetRank P.rHi M)
  | nextHi {elapsed qPrev m : ℕ}
      (hrun : ShrinkingRecertificationRun P M S n elapsed qPrev)
      (hSm : S ≤ m) (hm0 : P.pHi.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈
        initialWindowGood (shrinkingHighTolerance P M m))
      (hgap : rationalTargetRank P.rHi m < qPrev) :
      ShrinkingRecertificationRun P M S n
        (elapsed + stageLength (shrinkingHighSetup P M m) (orbit elapsed n))
        (rationalTargetRank P.rHi m)
  | nextLo {elapsed qPrev m : ℕ}
      (hrun : ShrinkingRecertificationRun P M S n elapsed qPrev)
      (hmS : m < S) (hm0 : P.pLo.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈ initialWindowGood P.etaLo)
      (hgap : rationalTargetRank P.rLo m < qPrev) :
      ShrinkingRecertificationRun P M S n
        (elapsed + stageLength P.pLo (orbit elapsed n))
        (rationalTargetRank P.rLo m)

theorem ShrinkingRecertificationRun.elapsed_pos
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    0 < elapsed := by
  cases hrun with
  | first hSM hM0 hnShell hnGood =>
      exact stageLength_pos (shrinkingHighSetup P M M) hM0 hnShell hnGood
  | nextHi hrun hSm hm0 hsourceShell hsourceGood hgap =>
      have hstage := stageLength_pos (shrinkingHighSetup P M _) hm0
        hsourceShell hsourceGood
      omega
  | nextLo hrun hmS hm0 hsourceShell hsourceGood hgap =>
      have hstage := stageLength_pos P.pLo hm0 hsourceShell hsourceGood
      omega

theorem ShrinkingRecertificationRun.currentRank_pos
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    0 < q := by
  cases hrun with
  | first hSM hM0 hnShell hnGood =>
      have ht := P.pHi.target_one_lt M hM0
      rw [targetScale_rat] at ht
      by_contra hq
      have : rationalTargetRank P.rHi M = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at ht
  | @nextHi elapsed qPrev m hrun hSm hm0 hsourceShell hsourceGood hgap =>
      have ht := P.pHi.target_one_lt m hm0
      rw [targetScale_rat] at ht
      by_contra hq
      have : rationalTargetRank P.rHi m = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at ht
  | @nextLo elapsed qPrev m hrun hmS hm0 hsourceShell hsourceGood hgap =>
      have ht := P.pLo.target_one_lt m hm0
      rw [targetScale_rat] at ht
      by_contra hq
      have : rationalTargetRank P.rLo m = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at ht

/-- Forgetting the tolerance schedule retains the exact common-loss chain. -/
theorem ShrinkingRecertificationRun.toMixed
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    MixedRecertificationRun P.rStar n elapsed q := by
  rw [P.rStar_eq]
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      exact MixedRecertificationRun.first (shrinkingHighSetup P M M)
        (min_le_left _ _) hM0 hnShell hnGood
  | nextHi hrun hSm hm0 hsourceShell hsourceGood hgap ih =>
      exact MixedRecertificationRun.next ih (shrinkingHighSetup P M _)
        (min_le_left _ _) hm0 hsourceShell hsourceGood hgap
  | nextLo hrun hmS hm0 hsourceShell hsourceGood hgap ih =>
      exact MixedRecertificationRun.next ih P.pLo
        (min_le_right _ _) hm0 hsourceShell hsourceGood hgap

theorem ShrinkingRecertificationRun.directFirstPassage
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    IsFirstPassage (2 ^ q) n elapsed :=
  (hrun.toMixed.toCertifiedRankChain P.rStar_pos).directFirstPassage

/-- A certified checkpoint following a run is in the unique lower shell
`q-1`; this is the deterministic-rank input to time compression. -/
theorem ShrinkingRecertificationRun.certified_endpoint_shell_eq
    {P : ShrinkingBarrierRunData} {M S n elapsed q m : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q)
    {t : ℝ} (htA : t < a0)
    (hgood : orbit elapsed n ∈ initialWindowGood t)
    (hshell : orbit elapsed n ∈ dyadicShell m) :
    m = q - 1 := by
  have hband := firstPassage_band hrun.elapsed_pos hrun.directFirstPassage
  have hlowerBand : 2 ^ (q - 1) < orbit elapsed n := by
    have hmul : 2 ^ (q - 1) * 2 < orbit elapsed n * 2 := by
      calc
        2 ^ (q - 1) * 2 = 2 ^ ((q - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ q := by rw [Nat.sub_add_cancel hrun.currentRank_pos]
        _ < 2 * orbit elapsed n := hband.1
        _ = orbit elapsed n * 2 := by omega
    exact lt_of_mul_lt_mul_right hmul (by norm_num)
  have hlower := certified_landing_mem_lower_shell hrun.currentRank_pos htA
    ⟨hlowerBand, hband.2⟩ hgood
  have hlogm := log_two_eq_of_mem_dyadicShell hshell
  have hlogq := log_two_eq_of_mem_dyadicShell hlower
  omega

private theorem shrinking_rationalTargetRank_cast_le
    {r : ℚ} (hr : 0 ≤ r) (m : ℕ) :
    (rationalTargetRank r m : ℝ) ≤ (r : ℝ) * (m : ℝ) := by
  exact Nat.floor_le (mul_nonneg (by exact_mod_cast hr) (Nat.cast_nonneg m))

/-- The shrinking run retains the old geometric rank/time trace. -/
theorem ShrinkingRecertificationRun.toRankTrace
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    TwoRegimeRankTrace (P.rHi : ℝ) (P.rLo : ℝ) S M elapsed q := by
  have hrHi0 : (0 : ℚ) ≤ P.rHi := by exact_mod_cast P.pHi.r_pos.le
  have hrLo0 : (0 : ℚ) ≤ P.rLo := by exact_mod_cast P.pLo.r_pos.le
  induction hrun with
  | first hSM hM0 hnShell' hnGood =>
      exact TwoRegimeRankTrace.first
        (stageLength_le_shell (shrinkingHighSetup P M M) hM0 hnShell' hnGood)
        (shrinking_rationalTargetRank_cast_le hrHi0 M)
  | @nextHi elapsed qPrev m hrun hSm hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq
        (shrinkingHighTolerance_lt_a0 P M m) hsourceGood hsourceShell
      have hmPrev : m ≤ qPrev := by omega
      apply TwoRegimeRankTrace.next ih hmPrev
        (stageLength_le_shell (shrinkingHighSetup P M m) hm0
          hsourceShell hsourceGood)
      simpa [hSm] using shrinking_rationalTargetRank_cast_le hrHi0 m
  | @nextLo elapsed qPrev m hrun hmS hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq P.etaLo_lt_a0
        hsourceGood hsourceShell
      have hmPrev : m ≤ qPrev := by omega
      apply TwoRegimeRankTrace.next ih hmPrev
        (stageLength_le_shell P.pLo hm0 hsourceShell hsourceGood)
      simpa [show ¬ S ≤ m by omega] using
        shrinking_rationalTargetRank_cast_le hrLo0 m

theorem ShrinkingRecertificationRun.elapsed_le_horizon
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    elapsed ≤ twoRegimeHorizon P.rHi P.rLo S M := by
  have hreal := hrun.toRankTrace.elapsed_le
    P.pHi.r_pos.le P.pHi.r_lt_one P.pLo.r_lt_one
  have hceil := twoRegimeHorizon_lower P.rHi P.rLo S M
  exact_mod_cast hreal.trans hceil

end

end FirstPassageLinearTransport
