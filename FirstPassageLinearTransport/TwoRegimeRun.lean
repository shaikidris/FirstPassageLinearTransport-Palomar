/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TerminalProfile

/-!
# Variable-regime certified runs

The optimized construction uses different stage parameters at high and low
shell ranks.  This module proves that every such literal stopped-map run is
still one `CertifiedRankChain` for a common lower contraction parameter
`rStar`.  Consequently the exact direct-first-passage and rank-scaled loss
theorems apply without inspecting how often the regime changes.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- A floor target formed with `r` satisfies the parent-rank budget for every
positive common parameter `rStar ≤ r`. -/
theorem parentRank_le_commonTargetBudget
    {rStar r : ℚ} (hrStar : 0 < rStar) (hStar : rStar ≤ r) (m : ℕ) :
    (m : ℚ) ≤ ((rationalTargetRank r m + 1 : ℕ) : ℚ) / rStar := by
  apply (le_div_iff₀ hrStar).2
  have hrStarR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hStarR : (rStar : ℝ) ≤ (r : ℝ) := by exact_mod_cast hStar
  have hrR : (0 : ℝ) ≤ (r : ℝ) := hrStarR.le.trans hStarR
  have hnonneg : (0 : ℝ) ≤ (r : ℝ) * (m : ℝ) := by positivity
  have hfloor := Nat.lt_floor_add_one ((r : ℝ) * (m : ℝ))
  have hfloor' : (r : ℝ) * (m : ℝ) ≤
      (rationalTargetRank r m + 1 : ℕ) := by
    simpa [rationalTargetRank] using hfloor.le
  have hbound : (rStar : ℝ) * (m : ℝ) ≤
      (rationalTargetRank r m + 1 : ℕ) := by
    have hfirst : (rStar : ℝ) * (m : ℝ) ≤
        (r : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hStarR (Nat.cast_nonneg m)
    exact hfirst.trans hfloor'
  have hboundQ : rStar * (m : ℚ) ≤
      ((rationalTargetRank r m + 1 : ℕ) : ℚ) := by
    exact_mod_cast hbound
  simpa [mul_comm] using hboundQ

/-- One literal stage initializes the common-budget rank chain. -/
theorem CertifiedRankChain.first_of_stage_common
    {rStar r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hrStar : 0 < rStar) (hStar : rStar ≤ r) {m n : ℕ}
    (hm0 : p.M0 ≤ m) (hnShell : n ∈ dyadicShell m)
    (hnGood : n ∈ initialWindowGood eta) :
    CertifiedRankChain rStar n (stageLength p n) (rationalTargetRank r m) := by
  apply CertifiedRankChain.first
  · simpa [targetScale_rat] using
      stageLength_isFirstPassage p hm0 hnShell hnGood
  · exact stageLength_le_shell p hm0 hnShell hnGood
  · exact parentRank_le_commonTargetBudget hrStar hStar m

/-- One further literal stage extends the same common-budget rank chain. -/
theorem CertifiedRankChain.next_of_stage_common
    {rStar r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hrStar : 0 < rStar) (hStar : rStar ≤ r)
    {n elapsed qprev m : ℕ}
    (hchain : CertifiedRankChain rStar n elapsed qprev)
    (hm0 : p.M0 ≤ m) (hsourceShell : orbit elapsed n ∈ dyadicShell m)
    (hsourceGood : orbit elapsed n ∈ initialWindowGood eta)
    (hgap : rationalTargetRank r m < qprev) :
    CertifiedRankChain rStar n
      (elapsed + stageLength p (orbit elapsed n))
      (rationalTargetRank r m) := by
  apply CertifiedRankChain.next hchain hgap
  · simpa [targetScale_rat] using
      stageLength_isFirstPassage p hm0 hsourceShell hsourceGood
  · exact stageLength_le_shell p hm0 hsourceShell hsourceGood
  · exact parentRank_le_commonTargetBudget hrStar hStar m

/-- A finite certified run whose successive blocks may use different stage
packages, all dominating the common contraction parameter `rStar`. -/
inductive MixedRecertificationRun (rStar : ℚ) (n : ℕ) : ℕ → ℕ → Prop
  | first {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
      {m : ℕ}
      (hStar : rStar ≤ r)
      (hm0 : p.M0 ≤ m)
      (hnShell : n ∈ dyadicShell m)
      (hnGood : n ∈ initialWindowGood eta) :
      MixedRecertificationRun rStar n
        (stageLength p n) (rationalTargetRank r m)
  | next {elapsed qprev : ℕ} (hrun : MixedRecertificationRun rStar n elapsed qprev)
      {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
      {m : ℕ}
      (hStar : rStar ≤ r)
      (hm0 : p.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈ initialWindowGood eta)
      (hgap : rationalTargetRank r m < qprev) :
      MixedRecertificationRun rStar n
        (elapsed + stageLength p (orbit elapsed n))
        (rationalTargetRank r m)

/-- Every variable-regime run is one exact rank chain for `rStar`. -/
theorem MixedRecertificationRun.toCertifiedRankChain
    {rStar : ℚ} (hrStar : 0 < rStar) {n elapsed q : ℕ}
    (hrun : MixedRecertificationRun rStar n elapsed q) :
    CertifiedRankChain rStar n elapsed q := by
  induction hrun with
  | first p hStar hm0 hnShell hnGood =>
      exact CertifiedRankChain.first_of_stage_common
        p hrStar hStar hm0 hnShell hnGood
  | next hrun p hStar hm0 hsourceShell hsourceGood hgap ih =>
      exact CertifiedRankChain.next_of_stage_common
        p hrStar hStar ih hm0 hsourceShell hsourceGood hgap

end

end FirstPassageLinearTransport
