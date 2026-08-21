/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingPolylogProfile
import FirstPassageLinearTransport.FirstPassageLandingShell

/-!
# Termination of shrinking-barrier re-certification

The next block is invoked only after its endpoint passes the rank-dependent
certification test.  Hence the recursion never treats a bad landing as a
certified source.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- Successful terminal rank reached by a literal shrinking-barrier run. -/
def HasShrinkingTerminalLanding
    (P : ShrinkingBarrierRunData) (M S n L : ℕ) : Prop :=
  ∃ elapsed q : ℕ,
    q < L ∧ ShrinkingRecertificationRun P M S n elapsed q


/-- Failure of the certification selected at a run endpoint is exactly
membership in the corresponding landing target. -/
theorem ShrinkingRecertificationRun.endpoint_mem_landingBad
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q)
    (hbad : orbit elapsed n ∉
      initialWindowGood (shrinkingTargetTolerance P M S q)) :
    orbit elapsed n ∈
      landingBad q (shrinkingTargetTolerance P M S q) := by
  have hband := firstPassage_band hrun.elapsed_pos hrun.directFirstPassage
  have hq := hrun.currentRank_pos
  apply mem_landingBad.mpr
  refine ⟨?_, hband.2, hbad⟩
  rw [show q = (q - 1) + 1 by omega, pow_succ] at hband
  omega

/-- A running certified path either terminates below `L` or its source lies
in the exact rankwise shrinking first-bad set. -/
theorem shrinkingRun_terminal_or_firstBad
    (P : ShrinkingBarrierRunData)
    {M S n L elapsed q : ℕ}
    (hn : 0 < n)
    (hnShell : n ∈ dyadicShell M)
    (hL2 : 2 ≤ L)
    (hHiStartup : P.pHi.M0 + 1 ≤ L)
    (hLoStartup : P.pLo.M0 + 1 ≤ L)
    (hqM : q ≤ M - 1)
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    HasShrinkingTerminalLanding P M S n L ∨
      ∃ q' : ℕ, L ≤ q' ∧ q' ≤ q ∧
        n ∈ shrinkingFirstBadSourcesAtRank P M S q' := by
  induction q using Nat.strong_induction_on generalizing elapsed with
  | h q ih =>
      by_cases hqL : q < L
      · exact Or.inl ⟨elapsed, q, hqL, hrun⟩
      · have hLq : L ≤ q := by omega
        let x := orbit elapsed n
        let m := Nat.log 2 x
        have hx : 0 < x := orbit_pos hn elapsed
        have hxshell : x ∈ dyadicShell m := by
          rw [mem_dyadicShell]
          exact ⟨Nat.pow_log_le_self 2 hx.ne',
            Nat.lt_pow_succ_log_self (by norm_num) x⟩
        have hmHiStartup : P.pHi.M0 ≤ m := by
          have hranks := firstPassage_landing_shell_rank hrun.elapsed_pos
            hrun.directFirstPassage hxshell
          omega
        have hmLoStartup : P.pLo.M0 ≤ m := by
          have hranks := firstPassage_landing_shell_rank hrun.elapsed_pos
            hrun.directFirstPassage hxshell
          omega
        let t := shrinkingTargetTolerance P M S q
        by_cases hxGood : x ∈ initialWindowGood t
        · have hmEq : m = q - 1 :=
            hrun.certified_endpoint_shell_eq
              (by
                dsimp [t]
                unfold shrinkingTargetTolerance
                split_ifs
                · exact shrinkingHighTolerance_lt_a0 P M (q - 1)
                · exact P.etaLo_lt_a0)
              hxGood hxshell
          have hmpos : 0 < m := by omega
          by_cases hmHigh : S ≤ m
          · have htEq : t = shrinkingHighTolerance P M m := by
              dsimp [t]
              rw [shrinkingTargetTolerance_eq_high P (by omega), hmEq]
            have hxGoodHi : x ∈ initialWindowGood
                (shrinkingHighTolerance P M m) := by simpa [htEq] using hxGood
            have hrHi0 : (0 : ℚ) ≤ P.rHi := by
              exact_mod_cast P.pHi.r_pos.le
            have hrHi1 : P.rHi < 1 := by exact_mod_cast P.pHi.r_lt_one
            have hgap : rationalTargetRank P.rHi m < q := by
              exact (rationalTargetRank_lt_parent hrHi0 hrHi1 hmpos).trans
                (by omega)
            let nextRun : ShrinkingRecertificationRun P M S n
                (elapsed + stageLength (shrinkingHighSetup P M m) x)
                (rationalTargetRank P.rHi m) :=
              ShrinkingRecertificationRun.nextHi hrun hmHigh hmHiStartup
                hxshell hxGoodHi hgap
            rcases ih (rationalTargetRank P.rHi m) hgap
              (hgap.le.trans hqM) nextRun with hterm | hfail
            · exact Or.inl hterm
            · rcases hfail with ⟨q', hq'L, hq'next, hq'bad⟩
              exact Or.inr ⟨q', hq'L, hq'next.trans hgap.le, hq'bad⟩
          · have hmLow : m < S := Nat.lt_of_not_ge hmHigh
            have htEq : t = P.etaLo := by
              dsimp [t]
              exact shrinkingTargetTolerance_eq_low P hrun.currentRank_pos
                (by omega)
            have hxGoodLo : x ∈ initialWindowGood P.etaLo := by
              simpa [htEq] using hxGood
            have hrLo0 : (0 : ℚ) ≤ P.rLo := by
              exact_mod_cast P.pLo.r_pos.le
            have hrLo1 : P.rLo < 1 := by exact_mod_cast P.pLo.r_lt_one
            have hgap : rationalTargetRank P.rLo m < q := by
              exact (rationalTargetRank_lt_parent hrLo0 hrLo1 hmpos).trans
                (by omega)
            let nextRun : ShrinkingRecertificationRun P M S n
                (elapsed + stageLength P.pLo x)
                (rationalTargetRank P.rLo m) :=
              ShrinkingRecertificationRun.nextLo hrun hmLow hmLoStartup
                hxshell hxGoodLo hgap
            rcases ih (rationalTargetRank P.rLo m) hgap
              (hgap.le.trans hqM) nextRun with hterm | hfail
            · exact Or.inl hterm
            · rcases hfail with ⟨q', hq'L, hq'next, hq'bad⟩
              exact Or.inr ⟨q', hq'L, hq'next.trans hgap.le, hq'bad⟩
        · exact Or.inr ⟨q, hLq, le_rfl,
            mem_shrinkingFirstBadSourcesAtRank.mpr
              ⟨hnShell,
                elapsed, hrun, hrun.endpoint_mem_landingBad hxGood⟩⟩

/-- Every outer-shell source either reaches terminal rank or lies in the
separated shrinking failure envelope. -/
theorem shrinkingSource_terminal_or_failure
    (P : ShrinkingBarrierRunData)
    {M S n L : ℕ}
    (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
    (hL2 : 2 ≤ L)
    (hHiStartup : P.pHi.M0 + 1 ≤ L)
    (hLoStartup : P.pLo.M0 + 1 ≤ L)
    (hq0M : rationalTargetRank P.rHi M ≤ M - 1)
    (hnShell : n ∈ dyadicShell M) :
    HasShrinkingTerminalLanding P M S n L ∨
      n ∈ shrinkingSeparatedFailureEnvelope P M L S := by
  classical
  have hn : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact hp.trans_le (mem_dyadicShell.mp hnShell).1
  by_cases hnGood : n ∈ initialWindowGood (shrinkingHighTolerance P M M)
  · let firstRun : ShrinkingRecertificationRun P M S n
        (stageLength (shrinkingHighSetup P M M) n)
        (rationalTargetRank P.rHi M) :=
      ShrinkingRecertificationRun.first hSM hM0 hnShell hnGood
    rcases shrinkingRun_terminal_or_firstBad P hn hnShell hL2
      hHiStartup hLoStartup hq0M firstRun with hterm | hfail
    · exact Or.inl hterm
    · rcases hfail with ⟨q, hqL, hqInitial, hfail⟩
      have hqUpper : q ≤ M - 1 := hqInitial.trans hq0M
      have hqS : q ≤ S ∨ S + 1 ≤ q := by omega
      exact Or.inr (by
        unfold shrinkingSeparatedFailureEnvelope
        rcases hqS with hlow | hhigh
        · apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          exact ⟨q,
            Finset.mem_Icc.mpr ⟨hqL, hlow⟩, hfail⟩
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          exact ⟨q, Finset.mem_Icc.mpr ⟨hhigh, hqUpper⟩, hfail⟩)
  · exact Or.inr (by
      unfold shrinkingSeparatedFailureEnvelope
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [← shellBad_initialWindowGood]
      exact Finset.mem_filter.mpr ⟨hnShell, hnGood⟩)

/-- Outside the counted failure envelope there is a literal shortcut iterate
below `2^L`, within the retained two-regime clock. -/
theorem shrinkingSource_lands_below_horizon
    (P : ShrinkingBarrierRunData)
    {M S n L : ℕ}
    (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
    (hL2 : 2 ≤ L)
    (hHiStartup : P.pHi.M0 + 1 ≤ L)
    (hLoStartup : P.pLo.M0 + 1 ≤ L)
    (hq0M : rationalTargetRank P.rHi M ≤ M - 1)
    (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∉ shrinkingSeparatedFailureEnvelope P M L S) :
    ∃ elapsed : ℕ,
      elapsed ≤ twoRegimeHorizon P.rHi P.rLo S M ∧
        orbit elapsed n < 2 ^ L := by
  rcases shrinkingSource_terminal_or_failure P hSM hM0 hL2 hHiStartup
    hLoStartup hq0M hnShell with hterm | hfail
  · rcases hterm with ⟨elapsed, q, hqL, hrun⟩
    exact ⟨elapsed, hrun.elapsed_le_horizon,
      hrun.directFirstPassage.1.trans_lt
        (Nat.pow_lt_pow_right (by omega) hqL)⟩
  · exact False.elim (hnGood hfail)

end

end FirstPassageLinearTransport
