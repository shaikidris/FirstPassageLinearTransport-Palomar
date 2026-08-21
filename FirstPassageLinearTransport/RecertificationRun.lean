/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.RecertificationStep

/-!
# Recursive certified re-certification runs

This is the semantic induction omitted by the finite first-bad envelope.  Each
constructor executes the manuscript's literal stopped map from a certified
source.  The resulting run is converted to `CertifiedRankChain`, so nested
direct first passage and the rank-scaled reverse-loss budget are inherited.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- A nonempty finite run of certified stopped-map blocks. -/
inductive RecertificationRun {r : ℚ} {eta : ℝ}
    (p : StageSetup (r : ℝ) eta) (n : ℕ) : ℕ → ℕ → Prop
  | first {m : ℕ}
      (hm0 : p.M0 ≤ m)
      (hnShell : n ∈ dyadicShell m)
      (hnGood : n ∈ initialWindowGood eta) :
      RecertificationRun p n (stageLength p n) (rationalTargetRank r m)
  | next {elapsed qprev m : ℕ}
      (hrun : RecertificationRun p n elapsed qprev)
      (hm0 : p.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈ initialWindowGood eta) :
      RecertificationRun p n
        (elapsed + stageLength p (orbit elapsed n))
        (rationalTargetRank r m)

theorem RecertificationRun.currentRank_pos
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q) : 0 < q := by
  cases hrun with
  | @first m hm0 hnShell hnGood =>
      have ht := p.target_one_lt m hm0
      rw [targetScale_rat] at ht
      by_contra hq
      have : rationalTargetRank r m = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at ht
  | @next elapsed qprev m hrun hm0 hsourceShell hsourceGood =>
      have ht := p.target_one_lt m hm0
      rw [targetScale_rat] at ht
      by_contra hq
      have : rationalTargetRank r m = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at ht

theorem RecertificationRun.elapsed_pos
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q) : 0 < elapsed := by
  cases hrun with
  | @first m hm0 hnShell hnGood =>
      exact stageLength_pos p hm0 hnShell hnGood
  | @next elapsed qprev m hrun hm0 hsourceShell hsourceGood =>
      have hstage := stageLength_pos p hm0 hsourceShell hsourceGood
      omega

/-- Every literal certified run is an exact certified rank chain. -/
theorem RecertificationRun.toCertifiedRankChain
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q) :
    CertifiedRankChain r n elapsed q := by
  have hr : 0 < r := by exact_mod_cast p.r_pos
  have hr1 : r < 1 := by exact_mod_cast p.r_lt_one
  induction hrun with
  | @first m hm0 hnShell hnGood =>
      exact CertifiedRankChain.first_of_stage p hr hm0 hnShell hnGood
  | @next elapsed qprev m hrun hm0 hsourceShell hsourceGood ih =>
      have hfp := ih.directFirstPassage
      have hpow : 2 ^ m ≤ 2 ^ qprev :=
        (mem_dyadicShell.mp hsourceShell).1.trans hfp.1
      have hmq : m ≤ qprev := by
        by_contra hnot
        have hstrict : 2 ^ qprev < 2 ^ m :=
          Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      have hmpos : 0 < m := by
        have ht := p.target_one_lt m hm0
        by_contra hm
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        norm_num [targetScale] at ht
      have htargetlt : rationalTargetRank r m < m :=
        rationalTargetRank_lt_parent hr.le hr1 hmpos
      have hgap : rationalTargetRank r m < qprev := htargetlt.trans_le hmq
      exact CertifiedRankChain.next_of_stage p hr ih hm0 hsourceShell
        hsourceGood hgap

/-- If the endpoint of a certified run is not certified, it belongs to the
exact first-bad landing band at the run's final threshold rank. -/
theorem RecertificationRun.endpoint_mem_landingBad
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q)
    (hbad : orbit elapsed n ∉ initialWindowGood eta) :
    orbit elapsed n ∈ landingBad q eta := by
  have hchain := hrun.toCertifiedRankChain
  have hfp := hchain.directFirstPassage
  have htime := hrun.elapsed_pos
  have hband := firstPassage_band htime hfp
  have hq := hrun.currentRank_pos
  apply mem_landingBad.mpr
  refine ⟨?_, hband.2, hbad⟩
  rw [show q = (q - 1) + 1 by omega, pow_succ] at hband
  omega

/-- A failed endpoint of a complete certified run supplies the exact generated
first-bad witness consumed by `generatedFirstBadSources_subset_envelope`. -/
theorem RecertificationRun.toGeneratedFirstBadLanding
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta}
    {n elapsed q L U H : ℕ}
    (hrun : RecertificationRun p n elapsed q)
    (hLq : L ≤ q) (hqU : q ≤ U) (hhH : elapsed ≤ H)
    (hbad : orbit elapsed n ∉ initialWindowGood eta) :
    HasGeneratedFirstBadLanding r eta n L U H :=
  hasGeneratedFirstBadLanding_of_chain hLq hqU hrun.elapsed_pos hhH
    hrun.toCertifiedRankChain (hrun.endpoint_mem_landingBad hbad)

end

end FirstPassageLinearTransport
