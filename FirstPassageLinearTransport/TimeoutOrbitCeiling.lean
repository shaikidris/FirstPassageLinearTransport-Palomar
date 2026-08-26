/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutEndpointAsymptotics
import FirstPassageLinearTransport.AsymptoticBounds
import FirstPassageLinearTransport.OrbitCeiling

/-!
# Clock and orbit ceiling for timeout runs

The high blocks retain the certified power envelope.  Inside a low timeout
block we use only the elementary deterministic inequality
`shortcut x ≤ 2*x`; since both its duration and source rank are below the
logarithmic switch, this crude loss is absorbed by the outer power margin.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

theorem shortcut_le_two_mul (n : ℕ) : shortcut n ≤ 2 * n := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · rw [shortcut_of_even heven]
    omega
  · rw [shortcut_of_odd hodd]
    have hn : 1 ≤ n := by omega
    omega

theorem orbit_le_two_pow_mul (j n : ℕ) : orbit j n ≤ 2 ^ j * n := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [orbit_succ]
      calc
        shortcut (orbit j n) ≤ 2 * orbit j n := shortcut_le_two_mul _
        _ ≤ 2 * (2 ^ j * n) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (j + 1) * n := by rw [pow_succ]; ring

theorem TimeoutRecertificationRun.currentRank_lt_startShell
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) : q < M := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      have hMpos : 0 < M := by
        have ht := P.pHi.target_one_lt M hM0
        by_contra hM
        have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
        rw [hMzero] at ht
        norm_num [targetScale] at ht
      exact rationalTargetRank_lt_parent
        (by exact_mod_cast P.pHi.r_pos.le)
        (by exact_mod_cast P.pHi.r_lt_one) hMpos
  | nextHi hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      exact hgap.trans ih
  | nextLo hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass hqpos
      hqparent hgap ih =>
      exact hgap.trans ih

theorem TimeoutRecertificationRun.endpoint_lt_start
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M) : orbit elapsed n < n := by
  have hqM := hrun.currentRank_lt_startShell
  exact hrun.directFirstPassage.1.trans_lt
    ((Nat.pow_lt_pow_right (by omega) hqM).trans_le
      (mem_dyadicShell.mp hnShell).1)

/-- Every prefix of a timeout run obeys the same outer power ceiling. -/
theorem TimeoutRecertificationRun.orbit_le_start_power
    {P : TimeoutHighRunData} {K₀ beta : ℝ}
    {L M S n elapsed q : ℕ}
    (hbeta : 0 < beta) (htau : P.tau < beta)
    (hLowMargin : 2 * (S : ℝ) ≤ beta * (M : ℝ))
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q)
    (hnShell : n ∈ dyadicShell M)
    {j : ℕ} (hj : j ≤ elapsed) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  have hn : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact hp.trans_le (mem_dyadicShell.mp hnShell).1
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  induction hrun with
  | first hSM hM0 hnShell' hnGood =>
      let p := timeoutHighSetup P M M
      have hnW : n ∈ extendedWindow p :=
        initialWindowGood_subset_extendedWindow p hnGood
      have hlocal := orbit_le_one_add_eta_of_le_stageLength p hn hnW hj
      have heta : timeoutHighTolerance P M M < beta :=
        (timeoutHighTolerance_le_tau P M M).trans_lt htau
      exact hlocal.trans
        (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith))
  | @nextHi elapsed qPrev m hrun hSm hm0 hmPrev hsourceShell hsourceGood
      hgap ih =>
      by_cases hjPrev : j ≤ elapsed
      · exact ih hjPrev
      · let v := j - elapsed
        have hjForm : j = elapsed + v := by dsimp [v]; omega
        have hv : v ≤ stageLength (timeoutHighSetup P M m)
            (orbit elapsed n) := by dsimp [v]; omega
        have hx : 0 < orbit elapsed n := orbit_pos hn elapsed
        have hxW : orbit elapsed n ∈ extendedWindow (timeoutHighSetup P M m) :=
          initialWindowGood_subset_extendedWindow _ hsourceGood
        have hlocal := orbit_le_one_add_eta_of_le_stageLength
          (timeoutHighSetup P M m) hx hxW hv
        have hxle : (orbit elapsed n : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (hrun.endpoint_lt_start hnShell).le
        have heta : timeoutHighTolerance P M m < beta :=
          (timeoutHighTolerance_le_tau P M m).trans_lt htau
        have hbase : (orbit elapsed n : ℝ) ^
            (1 + timeoutHighTolerance P M m) ≤
              (n : ℝ) ^ (1 + timeoutHighTolerance P M m) :=
          Real.rpow_le_rpow (by positivity) hxle
            (by linarith [timeoutHighTolerance_pos P M m])
        rw [hjForm, add_comm, orbit_add]
        exact hlocal.trans (hbase.trans
          (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)))
  | @nextLo elapsed qPrev m hrun hmS hLm hmPrevLo hmPrevHi hsourceShell
      hpass hqpos hqparent hgap ih =>
      by_cases hjPrev : j ≤ elapsed
      · exact ih hjPrev
      · let v := j - elapsed
        have hjForm : j = elapsed + v := by dsimp [v]; omega
        have hv : v ≤ hpass.duration := by dsimp [v]; omega
        have hvm : v ≤ m := hv.trans hpass.duration_le
        have hmSle : m + 1 ≤ S := by omega
        have hpowv : 2 ^ v ≤ 2 ^ S :=
          Nat.pow_le_pow_right (by omega) (hvm.trans (by omega))
        have hxS : orbit elapsed n ≤ 2 ^ S :=
          (mem_dyadicShell.mp hsourceShell).2.le.trans
            (Nat.pow_le_pow_right (by omega) hmSle)
        have hlocalNat : orbit v (orbit elapsed n) ≤ (2 ^ S) ^ 2 := by
          calc
            orbit v (orbit elapsed n) ≤ 2 ^ v * orbit elapsed n :=
              orbit_le_two_pow_mul _ _
            _ ≤ 2 ^ S * 2 ^ S := Nat.mul_le_mul hpowv hxS
            _ = (2 ^ S) ^ 2 := by ring
        have hlocal : (orbit v (orbit elapsed n) : ℝ) ≤
            (((2 : ℝ) ^ S) ^ (2 : ℕ)) := by
          exact_mod_cast hlocalNat
        have hExp : (S : ℝ) * 2 ≤ (M : ℝ) * beta := by
          nlinarith
        have htwo : (((2 : ℝ) ^ S) ^ (2 : ℝ)) ≤
            (((2 : ℝ) ^ M) ^ beta) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
        have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
          exact_mod_cast (mem_dyadicShell.mp hnShell).1
        have houter : ((2 : ℝ) ^ M) ^ beta ≤ (n : ℝ) ^ beta :=
          Real.rpow_le_rpow (by positivity) hnLower hbeta.le
        have hfinal : (n : ℝ) ^ beta ≤ (n : ℝ) ^ (1 + beta) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
        have htwo' : (((2 : ℝ) ^ S) ^ (2 : ℕ)) ≤
            (((2 : ℝ) ^ M) ^ beta) := by
          simpa [Real.rpow_two] using htwo
        rw [hjForm, add_comm, orbit_add]
        exact hlocal.trans (htwo'.trans (houter.trans hfinal))

/-- The timeout clock leaves enough of the strict clock margin to pay every
possible exact-halving completion below the logarithmic switch. -/
theorem eventually_timeoutRun_elapsed_add_switch_lt_shellClock
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀ L M
        (shrinkingSwitchRank P.Cswitch M) n elapsed q →
      ((elapsed + shrinkingSwitchRank P.Cswitch M : ℕ) : ℝ) <
        c * (M : ℝ) * Real.log 2 := by
  let T := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch
  let margin := c * Real.log 2 - 1 / driftGap
  have hmargin : 0 < margin := sub_pos.mpr P.clock_pressure
  have hT0 : 0 ≤ T := by
    have hrHi0 : 0 < (P.run.toTimeoutHigh.rHi : ℝ) :=
      P.run.toTimeoutHigh.pHi.r_pos
    have hsqrt1 : Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ) < 1 := by
      nlinarith [Real.sq_sqrt hrHi0.le,
        Real.sqrt_nonneg (P.run.toTimeoutHigh.rHi : ℝ),
        P.run.toTimeoutHigh.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ) :=
      sub_pos.mpr hsqrt1
    have hnum : 0 ≤
        P.run.toTimeoutHigh.D + P.run.toTimeoutHigh.tau + 3 := by
      linarith [P.run.toTimeoutHigh.D_pos,
        P.run.toTimeoutHigh.pHi.eta_pos]
    have hinner : 0 ≤
        (P.run.toTimeoutHigh.D + P.run.toTimeoutHigh.tau + 3) /
            (1 - Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    dsimp [T, timeoutTimeSupportConstant]
    nlinarith [mul_nonneg hratio hinner]
  let delta := margin / (8 * (T + 1))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hSqrt := eventually_sqrt_mul_log_le_linear hdelta
  have hPotential := eventually_timeoutTimePotential_source_le_sqrt
    P.run.toTimeoutHigh P.Cswitch_pos.le
  have hLarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop (4 / (driftGap * margin)))
  have hSwitchMargin := eventually_shrinkingSwitchRank_envelope_le_shellMargin
    P.Cswitch_pos.le (show (0 : ℝ) ≤ 0 by norm_num) (by
      exact half_pos hmargin)
  filter_upwards [hSqrt, hPotential, hLarge, hSwitchMargin,
      eventually_ge_atTop (2 : ℕ)]
    with M hSqrt hPotential hLarge hSwitchMargin hM2
  intro L n elapsed q hrun
  have hM1 : 1 ≤ M := by omega
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hpot0 := timeoutTimePotential_nonneg P.run.toTimeoutHigh M
    (shrinkingSwitchRank P.Cswitch M) (M + 1)
  have hdev := hrun.deviation_add_potential_le hM1
  have hpotq0 := timeoutTimePotential_nonneg P.run.toTimeoutHigh M
    (shrinkingSwitchRank P.Cswitch M) q
  have habs :
      |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
        timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) := by
    linarith
  have hupper := (abs_le.mp habs).2
  have hpotRatio :
      timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap ≤
        T * root := by
    have hratio0 : 0 ≤
        timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap :=
      div_nonneg hpot0 driftGap_pos.le
    calc
      _ ≤ 1 + 2 * (timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap) := by
        linarith
      _ ≤ T * root := by
        simpa [T, root, div_eq_mul_inv, mul_assoc] using hPotential
  have hraw : driftGap * (elapsed : ℝ) ≤
      (M : ℝ) + 1 + timeoutTimePotential P.run.toTimeoutHigh M
        (shrinkingSwitchRank P.Cswitch M) (M + 1) := by
    push_cast at hupper
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have htime : (elapsed : ℝ) ≤ (M : ℝ) / driftGap +
      (1 / driftGap + T * root) := by
    have hdiv : (elapsed : ℝ) ≤ ((M : ℝ) + 1 +
        timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1)) / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      simpa [mul_comm] using hraw
    calc
      _ ≤ _ := hdiv
      _ = (M : ℝ) / driftGap + (1 / driftGap +
          timeoutTimePotential P.run.toTimeoutHigh M
            (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap) := by ring
      _ ≤ (M : ℝ) / driftGap + (1 / driftGap + T * root) := by gcongr
  have hTdelta : T * delta ≤ margin / 8 := by
    have hratioT : T / (T + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith)
    calc
      T * delta = (margin / 8) * (T / (T + 1)) := by
        dsimp [delta]
        field_simp
      _ ≤ (margin / 8) * 1 :=
        mul_le_mul_of_nonneg_left hratioT (by positivity)
      _ = margin / 8 := by ring
  have hrootBound : T * root ≤ margin / 4 * (M : ℝ) := by
    have hxM : (M : ℝ) + 2 ≤ 2 * (M : ℝ) := by
      have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM2
      linarith
    have hfirst : T * root ≤ T * (delta * ((M : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left (by simpa [root] using hSqrt) hT0
    calc
      T * root ≤ (T * delta) * ((M : ℝ) + 2) := by
        simpa [mul_assoc] using hfirst
      _ ≤ (margin / 8) * ((M : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hTdelta (by positivity)
      _ ≤ (margin / 8) * (2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hxM (by positivity)
      _ = margin / 4 * (M : ℝ) := by ring
  have hconst : 1 / driftGap < margin / 4 * (M : ℝ) := by
    have hprod : 4 / (driftGap * margin) < (M : ℝ) := by simpa using hLarge
    rw [div_lt_iff₀ (mul_pos driftGap_pos hmargin)] at hprod
    rw [div_lt_iff₀ driftGap_pos]
    ring_nf at hprod ⊢
    nlinarith
  have hsublinear : 1 / driftGap + T * root < margin / 2 * (M : ℝ) := by
    linarith
  have hSwitch : (shrinkingSwitchRank P.Cswitch M : ℝ) ≤
      margin / 2 * (M : ℝ) := by
    simpa using hSwitchMargin
  push_cast
  calc
    (elapsed : ℝ) + (shrinkingSwitchRank P.Cswitch M : ℝ) ≤
        ((M : ℝ) / driftGap + (1 / driftGap + T * root)) +
          (shrinkingSwitchRank P.Cswitch M : ℝ) := by gcongr
    _ < (M : ℝ) / driftGap + margin * (M : ℝ) := by linarith
    _ = c * (M : ℝ) * Real.log 2 := by
      dsimp [margin]
      ring

end

end FirstPassageLinearTransport
