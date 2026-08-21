/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingExecution
import FirstPassageLinearTransport.OrbitCeiling

/-!
# Intermediate-orbit ceiling for shrinking-barrier runs
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

theorem ShrinkingRecertificationRun.currentRank_lt_startShell
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) : q < M := by
  induction hrun with
  | first hSM hM0 hnShell' hnGood =>
      have hMpos : 0 < M := by
        have ht := P.pHi.target_one_lt M hM0
        by_contra hM
        have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
        rw [hMzero] at ht
        norm_num [targetScale] at ht
      have hr0 : (0 : ℚ) ≤ P.rHi := by exact_mod_cast P.pHi.r_pos.le
      have hr1 : P.rHi < 1 := by exact_mod_cast P.pHi.r_lt_one
      exact rationalTargetRank_lt_parent hr0 hr1 hMpos
  | nextHi hrun hSm hm0 hsourceShell hsourceGood hgap ih => exact hgap.trans ih
  | nextLo hrun hmS hm0 hsourceShell hsourceGood hgap ih => exact hgap.trans ih

theorem ShrinkingRecertificationRun.endpoint_lt_start
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q)
    (hnShell : n ∈ dyadicShell M) : orbit elapsed n < n := by
  have hqM := hrun.currentRank_lt_startShell
  exact hrun.directFirstPassage.1.trans_lt
    ((Nat.pow_lt_pow_right (by omega) hqM).trans_le
      (mem_dyadicShell.mp hnShell).1)

/-- All prefixes of a literal shrinking run obey the outer power ceiling. -/
theorem ShrinkingRecertificationRun.orbit_le_start_power
    {P : ShrinkingBarrierRunData} {beta : ℝ}
    {M S n elapsed q : ℕ}
    (hbeta : 0 < beta) (htau : P.tau < beta)
    (hLowMargin : (S : ℝ) * (1 + P.etaLo) ≤ beta * (M : ℝ))
    (hrun : ShrinkingRecertificationRun P M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    {j : ℕ} (hj : j ≤ elapsed) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  have hn : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact hp.trans_le (mem_dyadicShell.mp hnShell).1
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  induction hrun with
  | first hSM hM0 hnShell' hnGood =>
      let p := shrinkingHighSetup P M M
      have hnW : n ∈ extendedWindow p :=
        initialWindowGood_subset_extendedWindow p hnGood
      have hlocal := orbit_le_one_add_eta_of_le_stageLength p hn hnW hj
      have heta : shrinkingHighTolerance P M M < beta :=
        (shrinkingHighTolerance_le_tau P M M).trans_lt htau
      exact hlocal.trans
        (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith))
  | @nextHi elapsed qPrev m hrun hSm hm0 hsourceShell hsourceGood hgap ih =>
      by_cases hjPrev : j ≤ elapsed
      · exact ih hjPrev
      · let v := j - elapsed
        have hjForm : j = elapsed + v := by dsimp [v]; omega
        have hv : v ≤ stageLength (shrinkingHighSetup P M m)
            (orbit elapsed n) := by dsimp [v]; omega
        have hx : 0 < orbit elapsed n := orbit_pos hn elapsed
        have hxW : orbit elapsed n ∈ extendedWindow (shrinkingHighSetup P M m) :=
          initialWindowGood_subset_extendedWindow _ hsourceGood
        have hlocal := orbit_le_one_add_eta_of_le_stageLength
          (shrinkingHighSetup P M m) hx hxW hv
        have hxle : (orbit elapsed n : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (hrun.endpoint_lt_start hnShell).le
        have heta : shrinkingHighTolerance P M m < beta :=
          (shrinkingHighTolerance_le_tau P M m).trans_lt htau
        have hbase : (orbit elapsed n : ℝ) ^
            (1 + shrinkingHighTolerance P M m) ≤
              (n : ℝ) ^ (1 + shrinkingHighTolerance P M m) :=
          Real.rpow_le_rpow (by positivity) hxle
            (by linarith [shrinkingHighTolerance_pos P M m])
        rw [hjForm, add_comm, orbit_add]
        exact hlocal.trans (hbase.trans
          (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)))
  | @nextLo elapsed qPrev m hrun hmS hm0 hsourceShell hsourceGood hgap ih =>
      by_cases hjPrev : j ≤ elapsed
      · exact ih hjPrev
      · let v := j - elapsed
        have hjForm : j = elapsed + v := by dsimp [v]; omega
        have hv : v ≤ stageLength P.pLo (orbit elapsed n) := by
          dsimp [v]
          omega
        have hx : 0 < orbit elapsed n := orbit_pos hn elapsed
        have hxW : orbit elapsed n ∈ extendedWindow P.pLo :=
          initialWindowGood_subset_extendedWindow P.pLo hsourceGood
        have hlocal := orbit_le_one_add_eta_of_le_stageLength P.pLo hx hxW hv
        have hmSle : m + 1 ≤ S := by omega
        have hxUpperNat : orbit elapsed n ≤ 2 ^ S :=
          (mem_dyadicShell.mp hsourceShell).2.le.trans
            (Nat.pow_le_pow_right (by omega) hmSle)
        have hxUpper : (orbit elapsed n : ℝ) ≤ (2 : ℝ) ^ S := by
          norm_num at hxUpperNat ⊢
          exact_mod_cast hxUpperNat
        have hlocalScale :
            (orbit elapsed n : ℝ) ^ (1 + P.etaLo) ≤
              ((2 : ℝ) ^ S) ^ (1 + P.etaLo) :=
          Real.rpow_le_rpow (by positivity) hxUpper
            (by linarith [P.pLo.eta_pos])
        have hExp : (S : ℝ) * (1 + P.etaLo) ≤
            (M : ℝ) * (1 + beta) := by
          calc
            _ ≤ beta * (M : ℝ) := hLowMargin
            _ ≤ (M : ℝ) * (1 + beta) := by
              nlinarith [show (0 : ℝ) ≤ M from Nat.cast_nonneg M]
        have htwo : ((2 : ℝ) ^ S) ^ (1 + P.etaLo) ≤
            ((2 : ℝ) ^ M) ^ (1 + beta) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
        have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
          exact_mod_cast (mem_dyadicShell.mp hnShell).1
        have houter : ((2 : ℝ) ^ M) ^ (1 + beta) ≤
            (n : ℝ) ^ (1 + beta) :=
          Real.rpow_le_rpow (by positivity) hnLower (by linarith)
        rw [hjForm, add_comm, orbit_add]
        exact hlocal.trans (hlocalScale.trans (htwo.trans houter))

/-- Canonical shrinking shell-good witnesses satisfy landing, clock, and
the complete intermediate-orbit ceiling. -/
theorem eventually_shrinkingPolylogGood_has_shellLanding_with_orbitCeiling
    {A c beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta)
    (P : ShrinkingPolylogParameterPackage A c beta) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      n ∈ dyadicShell M →
      n ∈ shrinkingPolylogGood P.run A P.Cswitch M →
      ∃ k : ℕ,
        (k : ℝ) < c * (M : ℝ) * Real.log 2 ∧
        (orbit k n : ℝ) < 2 * (((M : ℝ) + 2) ^ A) ∧
        ∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  have hSwitch := eventually_shrinkingSwitchRank_lt_source P.Cswitch_pos.le
  have hTerminalT := tendsto_polylogTerminalRank_atTop hA
  have hL2 : ∀ᶠ M : ℕ in atTop, 2 ≤ polylogTerminalRank A M :=
    hTerminalT.eventually (eventually_ge_atTop 2)
  have hHiStartup : ∀ᶠ M : ℕ in atTop,
      P.run.pHi.M0 + 1 ≤ polylogTerminalRank A M :=
    hTerminalT.eventually (eventually_ge_atTop (P.run.pHi.M0 + 1))
  have hLoStartup : ∀ᶠ M : ℕ in atTop,
      P.run.pLo.M0 + 1 ≤ polylogTerminalRank A M :=
    hTerminalT.eventually (eventually_ge_atTop (P.run.pLo.M0 + 1))
  have hrHi1 : P.run.rHi < 1 := by exact_mod_cast P.run.pHi.r_lt_one
  have hrLo1 : P.run.rLo < 1 := by exact_mod_cast P.run.pLo.r_lt_one
  have hClock := eventually_shrinkingHorizon_lt_shellClock
    hrHi1 hrLo1 P.Cswitch_pos.le P.clock_pressure
  have hMargin := eventually_shrinkingSwitchRank_envelope_le_shellMargin
    P.Cswitch_pos.le P.run.pLo.eta_pos.le hbeta
  filter_upwards [hSwitch, hL2, hHiStartup, hLoStartup, hClock, hMargin,
      eventually_ge_atTop P.run.pHi.M0, eventually_ge_atTop (1 : ℕ)]
    with M hSwitch hL2 hHiStartup hLoStartup hClock hMargin hM0 hM1
  intro n hnShell hnGood
  have hq0M : rationalTargetRank P.run.rHi M ≤ M - 1 := by
    have hlt := rationalTargetRank_lt_parent
      (by exact_mod_cast P.run.pHi.r_pos.le)
      (by exact_mod_cast P.run.pHi.r_lt_one) (by omega : 0 < M)
    omega
  have hnNotFailure : n ∉ shrinkingSeparatedFailureEnvelope P.run M
      (polylogTerminalRank A M) (shrinkingSwitchRank P.Cswitch M) := by
    simpa [shrinkingPolylogGood] using hnGood
  rcases shrinkingSource_terminal_or_failure P.run hSwitch.le hM0 hL2
    hHiStartup hLoStartup hq0M hnShell with hterm | hfail
  · rcases hterm with ⟨k, q, hqL, hrun⟩
    have hkH := hrun.elapsed_le_horizon
    have hkReal : (k : ℝ) ≤ twoRegimeHorizon P.run.rHi P.run.rLo
        (shrinkingSwitchRank P.Cswitch M) M := by exact_mod_cast hkH
    have hlanding : orbit k n < 2 ^ polylogTerminalRank A M :=
      hrun.directFirstPassage.1.trans_lt
        (Nat.pow_lt_pow_right (by omega) hqL)
    have hlandingReal : (orbit k n : ℝ) <
        ((2 ^ polylogTerminalRank A M : ℕ) : ℝ) := by exact_mod_cast hlanding
    refine ⟨k, hkReal.trans_lt hClock,
      hlandingReal.trans (two_pow_polylogTerminalRank_lt hA.le M), ?_⟩
    intro j hj
    exact hrun.orbit_le_start_power hbeta P.tau_lt_beta hMargin hnShell hj
  · exact False.elim (hnNotFailure hfail)

end

end FirstPassageLinearTransport
