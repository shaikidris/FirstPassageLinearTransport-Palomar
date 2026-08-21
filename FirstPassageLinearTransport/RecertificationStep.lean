/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.FirstBadEnvelope
import FirstPassageLinearTransport.Pullback

/-!
# Certified re-certification steps

This module connects the manuscript's literal stopped map to the finite
`CertifiedRankChain` consumed by the rank-scaled loss theorem.  A rational
contraction parameter is used internally so the exact reverse-loss budget
remains rational.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- Target exponent for a rational contraction parameter. -/
def rationalTargetRank (r : ℚ) (m : ℕ) : ℕ :=
  ⌊(r : ℝ) * (m : ℝ)⌋₊

theorem targetScale_rat (r : ℚ) (m : ℕ) :
    targetScale (r : ℝ) m = 2 ^ rationalTargetRank r m := rfl

/-- The floor target supplies the parent-rank inequality required by the
rank-scaled loss induction. -/
theorem parentRank_le_rationalTargetBudget
    {r : ℚ} (hr : 0 < r) (m : ℕ) :
    (m : ℚ) ≤ ((rationalTargetRank r m + 1 : ℕ) : ℚ) / r := by
  apply (le_div_iff₀ hr).2
  have hnonneg : (0 : ℝ) ≤ (r : ℝ) * (m : ℝ) := by positivity
  have hlt := Nat.lt_floor_add_one ((r : ℝ) * (m : ℝ))
  have hleR : (m : ℝ) * (r : ℝ) ≤
      (rationalTargetRank r m + 1 : ℕ) := by
    simpa [rationalTargetRank, mul_comm] using hlt.le
  exact_mod_cast hleR

theorem rationalTargetRank_lt_parent
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m : ℕ} (hm : 0 < m) :
    rationalTargetRank r m < m := by
  have hnonneg : (0 : ℝ) ≤ (r : ℝ) * (m : ℝ) := by positivity
  rw [rationalTargetRank, Nat.floor_lt hnonneg]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (r : ℝ) < 1 := by exact_mod_cast hr1
  nlinarith

/-- The first certified stopped-map block initializes the exact rank chain. -/
theorem CertifiedRankChain.first_of_stage
    {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hr : 0 < r) {m n : ℕ}
    (hm0 : p.M0 ≤ m) (hnShell : n ∈ dyadicShell m)
    (hnGood : n ∈ initialWindowGood eta) :
    CertifiedRankChain r n (stageLength p n) (rationalTargetRank r m) := by
  apply CertifiedRankChain.first
  · simpa [targetScale_rat] using
      stageLength_isFirstPassage p hm0 hnShell hnGood
  · exact stageLength_le_shell p hm0 hnShell hnGood
  · exact parentRank_le_rationalTargetBudget hr m

/-- One further certified stopped-map block extends an existing exact rank
chain once its target rank is strictly lower. -/
theorem CertifiedRankChain.next_of_stage
    {r : ℚ} {eta : ℝ} (p : StageSetup (r : ℝ) eta)
    (hr : 0 < r) {n elapsed qprev m : ℕ}
    (hchain : CertifiedRankChain r n elapsed qprev)
    (hm0 : p.M0 ≤ m) (hsourceShell : orbit elapsed n ∈ dyadicShell m)
    (hsourceGood : orbit elapsed n ∈ initialWindowGood eta)
    (hgap : rationalTargetRank r m < qprev) :
    CertifiedRankChain r n
      (elapsed + stageLength p (orbit elapsed n))
      (rationalTargetRank r m) := by
  apply CertifiedRankChain.next hchain hgap
  · simpa [targetScale_rat] using
      stageLength_isFirstPassage p hm0 hsourceShell hsourceGood
  · exact stageLength_le_shell p hm0 hsourceShell hsourceGood
  · exact parentRank_le_rationalTargetBudget hr m

/-- A first bad endpoint following a certified rank chain is a generated
first-bad witness in the exact envelope coordinates. -/
theorem hasGeneratedFirstBadLanding_of_chain
    {r : ℚ} {t : ℝ} {n h q L U H : ℕ}
    (hLq : L ≤ q) (hqU : q ≤ U) (hh1 : 1 ≤ h) (hhH : h ≤ H)
    (hchain : CertifiedRankChain r n h q)
    (hbad : orbit h n ∈ landingBad q t) :
    HasGeneratedFirstBadLanding r t n L U H :=
  ⟨h, q, hLq, hqU, hh1, hhH, hchain, hbad⟩

end

end FirstPassageLinearTransport
