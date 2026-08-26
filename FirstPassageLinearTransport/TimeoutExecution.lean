/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutEnvelope

/-!
# Literal execution of the timeout re-certification chain

Every outer-shell source is totalized into one of four cases: an initial
high failure, a first failed high certification, a first low timeout, or a
genuine orbit witness below the terminal threshold.  A dyadic upper endpoint
in the low phase is completed by exact halving; it is not inserted into the
timeout target as an artificial boundary atom.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- A timeout run has produced a terminal witness.  The first alternative is
an ordinary reached threshold.  The second records the exceptional dyadic
upper endpoint, whose remaining orbit is exact halving. -/
def HasTimeoutTerminalLanding
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S n : ℕ) : Prop :=
  (∃ elapsed q : ℕ,
      q ≤ L ∧ TimeoutRecertificationRun P K₀ L M S n elapsed q) ∨
  (∃ elapsed q : ℕ,
      L < q ∧ q ≤ S ∧
        TimeoutRecertificationRun P K₀ L M S n elapsed q ∧
        orbit elapsed n = 2 ^ q)


/-- A failed high certification at a reached threshold is literal membership
in the corresponding high landing target. -/
theorem TimeoutRecertificationRun.endpoint_mem_timeoutHighLandingBad
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hbad : orbit elapsed n ∉
      initialWindowGood (timeoutHighTargetTolerance P M q)) :
    orbit elapsed n ∈
      landingBad q (timeoutHighTargetTolerance P M q) := by
  have hband := hrun.landingBand
  have hq := hrun.currentRank_pos
  apply mem_landingBad.mpr
  refine ⟨?_, hband.2, hbad⟩
  have hmul : 2 ^ (q - 1) * 2 < orbit elapsed n * 2 := by
    calc
      2 ^ (q - 1) * 2 = 2 ^ ((q - 1) + 1) := by rw [pow_succ]
      _ = 2 ^ q := by rw [Nat.sub_add_cancel hq]
      _ < 2 * orbit elapsed n := hband.1
      _ = orbit elapsed n * 2 := by omega
  exact lt_of_mul_lt_mul_right hmul (by norm_num)

/-- A started timeout run either produces a terminal iterate or places its
original source in the separated failure envelope.  The induction is on the
strictly decreasing reached threshold rank. -/
theorem timeoutRun_terminal_or_failure
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {L M S n elapsed q : ℕ}
    (hL2 : 2 ≤ L) (_hLS : L ≤ S)
    (hHiStartup : P.pHi.M0 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p - 1)
    (hqM : q ≤ M - 1)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    HasTimeoutTerminalLanding P K₀ L M S n ∨
      n ∈ timeoutSeparatedFailureEnvelope P K₀ M L S := by
  classical
  induction q using Nat.strong_induction_on generalizing elapsed with
  | h q ih =>
      by_cases hqL : q ≤ L
      · exact Or.inl (Or.inl ⟨elapsed, q, hqL, hrun⟩)
      · have hLq : L < q := Nat.lt_of_not_ge hqL
        let x := orbit elapsed n
        by_cases hqHigh : S < q
        · let t := timeoutHighTargetTolerance P M q
          by_cases hxGood : x ∈ initialWindowGood t
          · have hq1 : 1 ≤ q := by omega
            have hband := hrun.landingBand
            have hcert : x ∈ dyadicShell (q - 1) := by
              apply certified_landing_mem_lower_shell hq1
                (timeoutHighTolerance_lt_a0 P M (q - 1))
              · exact ⟨by
                  have hmul : 2 ^ (q - 1) * 2 < x * 2 := by
                    calc
                      2 ^ (q - 1) * 2 = 2 ^ q := by
                        calc
                          _ = 2 ^ ((q - 1) + 1) := (pow_succ _ _).symm
                          _ = 2 ^ q := by rw [Nat.sub_add_cancel hq1]
                      _ < 2 * x := hband.1
                      _ = x * 2 := by omega
                  exact lt_of_mul_lt_mul_right hmul (by norm_num), hband.2⟩
              · simpa [t, timeoutHighTargetTolerance] using hxGood
            have hmStartup : P.pHi.M0 ≤ q - 1 := by omega
            have hgap : rationalTargetRank P.rHi (q - 1) < q := by
              exact (rationalTargetRank_lt_parent
                (by exact_mod_cast P.pHi.r_pos.le)
                (by exact_mod_cast P.pHi.r_lt_one)
                (by omega)).trans (by omega)
            let nextRun : TimeoutRecertificationRun P K₀ L M S n
                (elapsed + stageLength (timeoutHighSetup P M (q - 1)) x)
                (rationalTargetRank P.rHi (q - 1)) :=
              TimeoutRecertificationRun.nextHi hrun (by omega) hmStartup
                (by omega) hcert (by
                  simpa [t, timeoutHighTargetTolerance] using hxGood) hgap
            exact ih _ hgap (hgap.le.trans hqM) nextRun
          · exact Or.inr (by
              unfold timeoutSeparatedFailureEnvelope
              apply Finset.mem_union_left
              apply Finset.mem_union_right
              apply Finset.mem_biUnion.mpr
              refine ⟨q, Finset.mem_Icc.mpr ⟨by omega, hqM⟩, ?_⟩
              exact mem_timeoutHighFirstBadSourcesAtRank.mpr
                ⟨hrun.source_mem_dyadicShell, elapsed, hrun,
                  hrun.endpoint_mem_timeoutHighLandingBad hxGood⟩)
        · have hqLow : q ≤ S := by omega
          by_cases hupper : x = 2 ^ q
          · exact Or.inl (Or.inr ⟨elapsed, q, hLq, hqLow, hrun, hupper⟩)
          · have hq1 : 1 ≤ q := by omega
            have hband := hrun.landingBand
            have hsourceShell : x ∈ dyadicShell (q - 1) := by
              rw [mem_dyadicShell]
              refine ⟨?_, ?_⟩
              · have hmul : 2 ^ (q - 1) * 2 < x * 2 := by
                  calc
                    2 ^ (q - 1) * 2 = 2 ^ q := by
                      calc
                        _ = 2 ^ ((q - 1) + 1) := (pow_succ _ _).symm
                        _ = 2 ^ q := by rw [Nat.sub_add_cancel hq1]
                    _ < 2 * x := hband.1
                    _ = x * 2 := by omega
                exact (lt_of_mul_lt_mul_right hmul (by norm_num)).le
              · have hxlt : x < 2 ^ q := lt_of_le_of_ne hband.2 hupper
                simpa [Nat.sub_add_cancel hq1] using hxlt
            have hpI : q ∈ Finset.Icc (L + 1) S :=
              Finset.mem_Icc.mpr ⟨by omega, hqLow⟩
            let m := q - 1
            by_cases htimeout : LowStageTimeout K₀ L m x
            · exact Or.inr (by
                unfold timeoutSeparatedFailureEnvelope
                apply Finset.mem_union_right
                apply Finset.mem_biUnion.mpr
                exact ⟨q, hpI,
                  mem_timeoutFirstBadSourcesAtRank.mpr
                    ⟨hrun.source_mem_dyadicShell, elapsed, hrun, by
                      simpa [m] using htimeout⟩⟩)
            · let hpass : LowTimeoutPassage K₀ L m x :=
                Classical.choice (exists_lowTimeoutPassage_of_not_timeout htimeout)
              have hqpos : 0 < timeoutTargetRank K₀ L m := by
                simpa [m] using hnextPos q hpI
              have hqparent : timeoutTargetRank K₀ L m < m := by
                simpa [m] using hnextParent q hpI
              have hgap : timeoutTargetRank K₀ L m < q :=
                hqparent.trans_le (by dsimp [m]; omega)
              have hmS : m < S := by dsimp [m]; omega
              have hLm : L ≤ m := by dsimp [m]; omega
              have hmPrevLo : m ≤ q := by dsimp [m]; omega
              have hmPrevHi : q ≤ m + 1 := by dsimp [m]; omega
              let nextRun : TimeoutRecertificationRun P K₀ L M S n
                  (elapsed + hpass.duration) (timeoutTargetRank K₀ L m) :=
                TimeoutRecertificationRun.nextLo hrun hmS hLm hmPrevLo
                  hmPrevHi hsourceShell hpass hqpos hqparent hgap
              exact ih _ hgap (hgap.le.trans hqM) nextRun

/-- Every source in the outer shell either reaches the timeout terminal target
or belongs to the literal separated failure envelope. -/
theorem timeoutSource_terminal_or_failure
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {M L S n : ℕ}
    (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
    (hL2 : 2 ≤ L) (hLS : L ≤ S)
    (hHiStartup : P.pHi.M0 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p - 1)
    (hq0M : rationalTargetRank P.rHi M ≤ M - 1)
    (hnShell : n ∈ dyadicShell M) :
    HasTimeoutTerminalLanding P K₀ L M S n ∨
      n ∈ timeoutSeparatedFailureEnvelope P K₀ M L S := by
  classical
  by_cases hnGood : n ∈ initialWindowGood (timeoutHighTolerance P M M)
  · let firstRun : TimeoutRecertificationRun P K₀ L M S n
        (stageLength (timeoutHighSetup P M M) n)
        (rationalTargetRank P.rHi M) :=
      TimeoutRecertificationRun.first hSM hM0 hnShell hnGood
    exact timeoutRun_terminal_or_failure P K₀ hL2 hLS hHiStartup
      hnextPos hnextParent hq0M firstRun
  · exact Or.inr (by
      unfold timeoutSeparatedFailureEnvelope
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      have hnBad : n ∈ shellBad
          (initialWindowGood (timeoutHighTolerance P M M)) M :=
        Finset.mem_filter.mpr ⟨hnShell, hnGood⟩
      rw [shellBad_initialWindowGood] at hnBad
      exact hnBad)

end

end FirstPassageLinearTransport
