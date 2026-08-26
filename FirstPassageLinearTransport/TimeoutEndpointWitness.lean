/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutOrbitCeiling
import FirstPassageLinearTransport.PolylogTarget

/-!
# Same-witness execution for the timeout endpoint

The literal source outside the timeout envelope reaches the moving terminal
rank.  The same iterate supplies the logarithmic clock and orbit ceiling.  If
the low landing is a dyadic upper endpoint, its exact halving tail is included
in that same witness.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

private theorem timeout_fixedPolylogTargetConstant_mono
    {a b : ℝ} (hab : a ≤ b) :
    fixedPolylogTargetConstant a ≤ fixedPolylogTargetConstant b := by
  unfold fixedPolylogTargetConstant
  have hbase : 1 ≤ 1 / Real.log 2 + 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hinv : 0 < 1 / Real.log 2 := by positivity
    linarith
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hbase hab) (by norm_num)

/-- Canonical timeout-good shell sources have one witness satisfying landing,
clock, and ceiling simultaneously. -/
theorem eventually_timeoutEndpointGood_has_shellWitness
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      n ∈ dyadicShell M →
      n ∈ timeoutEndpointGood P A M →
      ∃ k : ℕ,
        (k : ℝ) < c * (M : ℝ) * Real.log 2 ∧
        (orbit k n : ℝ) <
          fixedPolylogTargetConstant Amax * (Real.log n) ^ (A M) ∧
        ∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  have hTerminalT := tendsto_movingTerminalRank_atTop hbuffer
  have hL2 := (tendsto_atTop.1 hTerminalT) 2
  have hHiStartup := (tendsto_atTop.1 hTerminalT) P.run.pHi.M0
  have hLS := eventually_movingTerminalRank_lt_shrinkingSwitchRank
    P.Amax_pos.le P.terminal_below_switch hUpper
  have hSwitch := eventually_shrinkingSwitchRank_lt_source P.Cswitch_pos.le
  have hClock := eventually_timeoutRun_elapsed_add_switch_lt_shellClock P
  have hbeta : 0 < beta := P.run.pHi.eta_pos.trans P.tau_lt_beta
  have hMargin := eventually_shrinkingSwitchRank_envelope_le_shellMargin
    P.Cswitch_pos.le (show (0 : ℝ) ≤ 1 by norm_num) hbeta
  have hA0 := eventually_movingExponent_pos hbuffer
  have hTimeoutAdmBase := eventually_timeoutTargetRank_admissible
    (show 0 < P.K₀ by linarith [P.K₀_gt_six])
  have hTimeoutAdm := hTerminalT.eventually hTimeoutAdmBase
  filter_upwards [hL2, hHiStartup, hLS, hSwitch, hClock, hMargin,
      hA0, hUpper, hTimeoutAdm, eventually_ge_atTop P.run.pHi.M0,
      eventually_ge_atTop (3 : ℕ)]
    with M hL2 hHiStartup hLS hSwitch hClock hMargin hA0 hUpper
      hTimeoutAdm hM0 hM3
  intro n hnShell hnGood
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  have hSM : S ≤ M := by dsimp [S]; exact hSwitch.le
  have hL2' : 2 ≤ L := by simpa [L] using hL2
  have hLS' : L ≤ S := by dsimp [L, S]; exact hLS.le
  have hHiStartup' : P.run.pHi.M0 ≤ L := by simpa [L] using hHiStartup
  have hq0M : rationalTargetRank P.run.rHi M ≤ M - 1 := by
    have hlt := rationalTargetRank_lt_parent
      (by exact_mod_cast P.run.pHi.r_pos.le)
      (by exact_mod_cast P.run.pHi.r_lt_one) (by omega : 0 < M)
    omega
  have hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank P.K₀ L (p - 1) := by
    intro p hp
    exact (hTimeoutAdm (p - 1) (by
      have hpI := Finset.mem_Icc.mp hp
      omega)).1
  have hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank P.K₀ L (p - 1) < p - 1 := by
    intro p hp
    exact (hTimeoutAdm (p - 1) (by
      have hpI := Finset.mem_Icc.mp hp
      omega)).2
  have hnNotFailure : n ∉
      timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M L S := by
    simpa [timeoutEndpointGood, L, S] using hnGood
  rcases timeoutSource_terminal_or_failure P.run.toTimeoutHigh P.K₀
    hSM hM0 hL2' hLS' hHiStartup' hnextPos hnextParent hq0M hnShell with
      hterm | hfail
  · have hn8 : 8 ≤ n := by
      have hpow : 2 ^ 3 ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hM3
      exact hpow.trans (mem_dyadicShell.mp hnShell).1
    have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
        (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
      norm_num only [Nat.cast_ofNat]
      nlinarith
    have hn8Real : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    have hlogn : 1 ≤ Real.log n :=
      hlog8.trans (Real.log_le_log (by norm_num) hn8Real)
    have htarget := shellPolylogTarget_le_natLog hA0.le hnShell hlogn
    have hconst := timeout_fixedPolylogTargetConstant_mono hUpper
    have hlogPow0 : 0 ≤ (Real.log n) ^ (A M) :=
      Real.rpow_nonneg (zero_le_one.trans hlogn) _
    have hLowMargin : 2 * (S : ℝ) ≤ beta * (M : ℝ) := by
      have hMargin' : (S : ℝ) * 2 ≤ beta * (M : ℝ) := by
        norm_num at hMargin ⊢
        exact hMargin
      nlinarith
    rcases hterm with hrunTerm | hdyadic
    · rcases hrunTerm with ⟨elapsed, q, hqL, hrun⟩
      have hlandingNat : orbit elapsed n ≤ 2 ^ L :=
        hrun.directFirstPassage.1.trans
          (Nat.pow_le_pow_right (by omega) hqL)
      have hlandingReal : (orbit elapsed n : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
        exact_mod_cast hlandingNat
      have hterminal : ((2 ^ L : ℕ) : ℝ) <
          2 * (((M : ℝ) + 2) ^ (A M)) := by
        simpa [L] using two_pow_movingTerminalRank_lt hA0.le
      have hclockRun := hClock hrun
      have hclock : (elapsed : ℝ) < c * (M : ℝ) * Real.log 2 := by
        have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
        push_cast at hclockRun
        linarith
      refine ⟨elapsed, hclock,
        hlandingReal.trans_lt (hterminal.trans_le (htarget.trans
          (mul_le_mul_of_nonneg_right hconst hlogPow0))), ?_⟩
      intro j hj
      exact hrun.orbit_le_start_power hbeta P.tau_lt_beta
        hLowMargin hnShell hj
    · rcases hdyadic with ⟨elapsed, q, hLq, hqS, hrun, heq⟩
      let v := q - L
      let k := elapsed + v
      have hvq : v ≤ q := Nat.sub_le _ _
      have horbitV : orbit v (2 ^ q) = 2 ^ L := by
        rw [timeout_orbit_two_pow hvq]
        congr
        omega
      have hlandingNat : orbit k n = 2 ^ L := by
        dsimp [k]
        rw [add_comm, orbit_add, heq, horbitV]
      have hlandingReal : (orbit k n : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
        exact_mod_cast hlandingNat.le
      have hterminal : ((2 ^ L : ℕ) : ℝ) <
          2 * (((M : ℝ) + 2) ^ (A M)) := by
        simpa [L] using two_pow_movingTerminalRank_lt hA0.le
      have hclockRun := hClock hrun
      have hvS : v ≤ S := (Nat.sub_le q L).trans hqS
      have hkBound : k ≤ elapsed + S := Nat.add_le_add_left hvS elapsed
      have hclock : (k : ℝ) < c * (M : ℝ) * Real.log 2 := by
        have hkR : (k : ℝ) ≤ ((elapsed + S : ℕ) : ℝ) := by exact_mod_cast hkBound
        exact hkR.trans_lt hclockRun
      refine ⟨k, hclock,
        hlandingReal.trans_lt (hterminal.trans_le (htarget.trans
          (mul_le_mul_of_nonneg_right hconst hlogPow0))), ?_⟩
      intro j hj
      by_cases hjElapsed : j ≤ elapsed
      · exact hrun.orbit_le_start_power hbeta P.tau_lt_beta
          hLowMargin hnShell hjElapsed
      · let u := j - elapsed
        have hjForm : j = u + elapsed := by dsimp [u]; omega
        have huV : u ≤ v := by dsimp [u, k] at hj ⊢; omega
        have huq : u ≤ q := huV.trans hvq
        have huOrbit : orbit u (2 ^ q) = 2 ^ (q - u) :=
          timeout_orbit_two_pow huq
        have htailNat : orbit j n ≤ orbit elapsed n := by
          rw [hjForm, orbit_add, heq, huOrbit]
          exact Nat.pow_le_pow_right (by omega) (Nat.sub_le q u)
        have htail : (orbit j n : ℝ) ≤ (n : ℝ) := by
          have hEndpoint : orbit elapsed n ≤ n :=
            (hrun.endpoint_lt_start hnShell).le
          have htailNat' : orbit j n ≤ n := htailNat.trans hEndpoint
          exact_mod_cast htailNat'
        exact htail.trans (by
          calc
            (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ ≤ (n : ℝ) ^ (1 + beta) :=
              Real.rpow_le_rpow_of_exponent_le
                (by exact_mod_cast (show 1 ≤ n by omega)) (by linarith))
  · exact False.elim (hnNotFailure hfail)

end

end FirstPassageLinearTransport
