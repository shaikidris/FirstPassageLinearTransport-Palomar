/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutDensity
import FirstPassageLinearTransport.ShrinkingBarrierRun
import FirstPassageLinearTransport.RankScaledLoss

/-!
# Mixed shrinking-high and timeout-low runs

This is the separate low-rank semantic run for the timeout proof.  High blocks use
the existing shrinking certificate.  Low blocks carry only a literal first
passage completed by the parent-rank deadline; no low all-prefix certificate
or low `StageSetup` occurs in the state.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- Fixed high-rank data used by the timeout run.  Unlike
`ShrinkingBarrierRunData`, this structure deliberately carries no low-stage
`StageSetup`: the low phase is governed only by the literal timeout event. -/
structure TimeoutHighRunData where
  rHi : ℚ
  tau : ℝ
  D : ℝ
  pHi : StageSetup (rHi : ℝ) tau
  D_pos : 0 < D
  tau_lt_a0 : tau < a0

/-- Forget the fixed low-stage package from the legacy shrinking data.  The
timeout route reuses exactly the high fields and no low certification. -/
def ShrinkingBarrierRunData.toTimeoutHigh
    (P : ShrinkingBarrierRunData) : TimeoutHighRunData where
  rHi := P.rHi
  tau := P.tau
  D := P.D
  pHi := P.pHi
  D_pos := P.D_pos
  tau_lt_a0 := P.tau_lt_a0

/-- The shrinking high tolerance, capped by the fixed high-stage package. -/
def timeoutHighTolerance
    (P : TimeoutHighRunData) (M m : ℕ) : ℝ :=
  if m = 0 then P.tau
  else min P.tau
    (P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)))

theorem timeoutHighTolerance_pos
    (P : TimeoutHighRunData) (M m : ℕ) :
    0 < timeoutHighTolerance P M m := by
  unfold timeoutHighTolerance
  split_ifs with hm
  · exact P.pHi.eta_pos
  · apply lt_min P.pHi.eta_pos
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hlog : 0 < Real.log ((M : ℝ) + 2) := by
      apply Real.log_pos
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    exact mul_pos P.D_pos (Real.sqrt_pos.2 (div_pos hlog hm0))

theorem timeoutHighTolerance_le_tau
    (P : TimeoutHighRunData) (M m : ℕ) :
    timeoutHighTolerance P M m ≤ P.tau := by
  unfold timeoutHighTolerance
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem timeoutHighTolerance_lt_a0
    (P : TimeoutHighRunData) (M m : ℕ) :
    timeoutHighTolerance P M m < a0 :=
  (timeoutHighTolerance_le_tau P M m).trans_lt P.tau_lt_a0

/-- The high-stage package at one rank. -/
def timeoutHighSetup
    (P : TimeoutHighRunData) (M m : ℕ) :
    StageSetup (P.rHi : ℝ) (timeoutHighTolerance P M m) :=
  P.pHi.lowerTolerance (timeoutHighTolerance P M m)
    (timeoutHighTolerance_pos P M m)
    (timeoutHighTolerance_le_tau P M m)

/-- A completed low timeout block: the first passage occurs by the parent
shell deadline. -/
structure LowTimeoutPassage (K₀ : ℝ) (L m x : ℕ) where
  duration : ℕ
  duration_le : duration ≤ m
  firstPassage :
    IsFirstPassage (2 ^ timeoutTargetRank K₀ L m) x duration

/-- Failure of the literal timeout event produces a canonical finite first
passage, without assuming eventual Collatz descent. -/
theorem exists_lowTimeoutPassage_of_not_timeout
    {K₀ : ℝ} {L m x : ℕ}
    (hnot : ¬LowStageTimeout K₀ L m x) :
    Nonempty (LowTimeoutPassage K₀ L m x) := by
  classical
  rw [LowStageTimeout] at hnot
  push_neg at hnot
  obtain ⟨j, hj⟩ := hnot
  have hexists :
      ∃ h : ℕ,
        h ≤ m ∧ orbit h x ≤ 2 ^ timeoutTargetRank K₀ L m :=
    ⟨j, by omega, by omega⟩
  let h := Nat.find hexists
  have hspec := Nat.find_spec hexists
  refine ⟨⟨h, hspec.1, hspec.2, ?_⟩⟩
  intro i hi
  by_contra hle
  have hiTarget : orbit i x ≤ 2 ^ timeoutTargetRank K₀ L m :=
    Nat.le_of_not_gt hle
  exact Nat.find_min hexists hi ⟨hi.le.trans hspec.1, hiTarget⟩

/-- The literal mixed run.  The index `q` is the threshold rank reached at
the final successful block. -/
inductive TimeoutRecertificationRun
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S n : ℕ) : ℕ → ℕ → Prop
  | first
      (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
      (hnShell : n ∈ dyadicShell M)
      (hnGood : n ∈ initialWindowGood (timeoutHighTolerance P M M)) :
      TimeoutRecertificationRun P K₀ L M S n
        (stageLength (timeoutHighSetup P M M) n)
        (rationalTargetRank P.rHi M)
  | nextHi {elapsed qPrev m : ℕ}
      (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed qPrev)
      (hSm : S ≤ m) (hm0 : P.pHi.M0 ≤ m)
      (hmPrev : qPrev = m + 1)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈
        initialWindowGood (timeoutHighTolerance P M m))
      (hgap : rationalTargetRank P.rHi m < qPrev) :
      TimeoutRecertificationRun P K₀ L M S n
        (elapsed + stageLength (timeoutHighSetup P M m) (orbit elapsed n))
        (rationalTargetRank P.rHi m)
  | nextLo {elapsed qPrev m : ℕ}
      (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed qPrev)
      (hmS : m < S) (hLm : L ≤ m)
      (hmPrevLo : m ≤ qPrev) (hmPrevHi : qPrev ≤ m + 1)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hpass : LowTimeoutPassage K₀ L m (orbit elapsed n))
      (hqpos : 0 < timeoutTargetRank K₀ L m)
      (hqparent : timeoutTargetRank K₀ L m < m)
      (hgap : timeoutTargetRank K₀ L m < qPrev) :
      TimeoutRecertificationRun P K₀ L M S n
        (elapsed + hpass.duration) (timeoutTargetRank K₀ L m)

/-- Every literal run retains the original outer-shell source. -/
theorem TimeoutRecertificationRun.source_mem_dyadicShell
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    n ∈ dyadicShell M := by
  induction hrun with
  | first hSM hM0 hnShell hnGood => exact hnShell
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih => exact ih
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos hqparent
      hgap ih => exact ih

theorem TimeoutRecertificationRun.elapsed_pos
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    0 < elapsed := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      exact stageLength_pos (timeoutHighSetup P M M) hM0 hnShell hnGood
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      have hstage := stageLength_pos (timeoutHighSetup P M _) hm0
        hsourceShell hsourceGood
      omega
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos hqparent
      hgap ih =>
      exact Nat.lt_add_right _ ih

theorem TimeoutRecertificationRun.currentRank_pos
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    0 < q := by
  cases hrun with
  | first hSM hM0 hnShell hnGood =>
      have ht := P.pHi.target_one_lt M hM0
      rw [targetScale_rat] at ht
      by_contra hq
      have : rationalTargetRank P.rHi M = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at ht
  | @nextHi elapsed qPrev m hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap =>
      have ht := P.pHi.target_one_lt m hm0
      rw [targetScale_rat] at ht
      by_contra hq
      have : rationalTargetRank P.rHi m = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at ht
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos hqparent
      hgap =>
      exact hqpos

/-- Every literal timeout run is the direct first passage of the original
source through its final threshold. -/
theorem TimeoutRecertificationRun.directFirstPassage
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    IsFirstPassage (2 ^ q) n elapsed := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      simpa [targetScale_rat] using
        stageLength_isFirstPassage (timeoutHighSetup P M M)
          hM0 hnShell hnGood
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      have hthreshold : 2 ^ rationalTargetRank P.rHi _ < 2 ^ _ :=
        Nat.pow_lt_pow_right (by omega) hgap
      exact ih.nested hthreshold (by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (timeoutHighSetup P M _)
            hm0 hsourceShell hsourceGood)
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos hqparent
      hgap ih =>
      have hthreshold : 2 ^ timeoutTargetRank K₀ L _ < 2 ^ _ :=
        Nat.pow_lt_pow_right (by omega) hgap
      exact ih.nested hthreshold hpass.firstPassage

/-- Every reached endpoint lies in the first-passage landing band. -/
theorem TimeoutRecertificationRun.landingBand
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    2 ^ q < 2 * orbit elapsed n ∧ orbit elapsed n ≤ 2 ^ q :=
  firstPassage_band hrun.elapsed_pos hrun.directFirstPassage

/-- A rational lower contraction dominated by the high ratio supplies the
rank budget needed by the reverse-loss induction. -/
theorem parentRank_le_timeoutHighBudget
    {rStar r : ℚ} (hrStar : 0 < rStar) (hStar : rStar ≤ r) (m : ℕ) :
    (m : ℚ) ≤ ((rationalTargetRank r m + 1 : ℕ) : ℚ) / rStar := by
  apply (le_div_iff₀ hrStar).2
  have hrStarR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hStarR : (rStar : ℝ) ≤ (r : ℝ) := by exact_mod_cast hStar
  have hnonneg : (0 : ℝ) ≤ (r : ℝ) * (m : ℝ) :=
    mul_nonneg (hrStarR.le.trans hStarR) (Nat.cast_nonneg m)
  have hfloor := Nat.lt_floor_add_one ((r : ℝ) * (m : ℝ))
  have hfloor' : (r : ℝ) * (m : ℝ) ≤
      (rationalTargetRank r m + 1 : ℕ) := by
    simpa [rationalTargetRank] using hfloor.le
  have hbound : (rStar : ℝ) * (m : ℝ) ≤
      (rationalTargetRank r m + 1 : ℕ) :=
    (mul_le_mul_of_nonneg_right hStarR (Nat.cast_nonneg m)).trans hfloor'
  have hboundQ : rStar * (m : ℚ) ≤
      ((rationalTargetRank r m + 1 : ℕ) : ℚ) := by
    exact_mod_cast hbound
  simpa [mul_comm] using hboundQ

/-- The same rank budget for the real moving-low ratio used by the timeout
target.  No low certification package is involved. -/
theorem parentRank_le_timeoutLowBudget
    {K₀ : ℝ} {L m : ℕ} {rStar : ℚ}
    (hrStar : 0 < rStar)
    (hStar : (rStar : ℝ) ≤ movingLowRatio K₀ L) :
    (m : ℚ) ≤ ((timeoutTargetRank K₀ L m + 1 : ℕ) : ℚ) / rStar := by
  apply (le_div_iff₀ hrStar).2
  have hrStarR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hratio0 : 0 ≤ movingLowRatio K₀ L := hrStarR.le.trans hStar
  have hfloor := Nat.lt_floor_add_one
    (movingLowRatio K₀ L * (m : ℝ))
  have hfloor' : movingLowRatio K₀ L * (m : ℝ) ≤
      (timeoutTargetRank K₀ L m + 1 : ℕ) := by
    simpa [timeoutTargetRank] using hfloor.le
  have hbound : (rStar : ℝ) * (m : ℝ) ≤
      (timeoutTargetRank K₀ L m + 1 : ℕ) :=
    (mul_le_mul_of_nonneg_right hStar (Nat.cast_nonneg m)).trans hfloor'
  have hboundQ : rStar * (m : ℚ) ≤
      ((timeoutTargetRank K₀ L m + 1 : ℕ) : ℚ) := by
    exact_mod_cast hbound
  simpa [mul_comm] using hboundQ

/-- Every timeout run is a rank-scaled chain for any fixed positive rational
contraction dominated by both the high and moving-low ratios. -/
theorem TimeoutRecertificationRun.toCertifiedRankChain
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S n elapsed q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    CertifiedRankChain rStar n elapsed q := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      apply CertifiedRankChain.first
      · simpa [targetScale_rat] using
          stageLength_isFirstPassage (timeoutHighSetup P M M)
            hM0 hnShell hnGood
      · exact stageLength_le_shell (timeoutHighSetup P M M)
          hM0 hnShell hnGood
      · exact parentRank_le_timeoutHighBudget hrStar hStarHi M
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      apply CertifiedRankChain.next ih hgap
      · simpa [targetScale_rat] using
          stageLength_isFirstPassage (timeoutHighSetup P M _)
            hm0 hsourceShell hsourceGood
      · exact stageLength_le_shell (timeoutHighSetup P M _)
          hm0 hsourceShell hsourceGood
      · exact parentRank_le_timeoutHighBudget hrStar hStarHi _
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos hqparent
      hgap ih =>
      apply CertifiedRankChain.next ih hgap
      · exact hpass.firstPassage
      · exact hpass.duration_le
      · exact parentRank_le_timeoutLowBudget hrStar hStarLo

/-- Complete sourcewise reverse-loss budget for the timeout route. -/
theorem TimeoutRecertificationRun.scaledReverseLoss_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S n elapsed q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    scaledReverseLoss (2 ^ q) n elapsed ≤ ((q + 2 : ℕ) : ℚ) / rStar :=
  (hrun.toCertifiedRankChain hrStar hStarHi hStarLo).scaledReverseLoss_le hrStar

end

end FirstPassageLinearTransport
