/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutRun
import FirstPassageLinearTransport.ShrinkingSchedules

/-!
# Feasible times for the timeout route

The high phase retains the shrinking-barrier corridor.  A low block uses no
all-prefix envelope: its duration is merely at most its parent rank.  Strict
rank descent then pays the whole low phase with the elementary potential
`S * q`, giving a total reserve `S^2`.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Width notation used only by the high certified blocks. -/
def timeoutDurationError (t : ℝ) (m : ℕ) : ℝ :=
  t * (m : ℝ) + t + 3

private theorem timeout_abs_add_sub_one_le (a b : ℝ) :
    |a + b - 1| ≤ |a| + |b| + 1 := by
  calc
    |a + b - 1| ≤ |a + b| + 1 := by
      simpa using (abs_sub_le (a + b) 0 (1 : ℝ))
    _ ≤ |a| + |b| + 1 := by
      linarith [abs_add_le a b]

/-- A certified high block has the usual duration corridor. -/
theorem timeoutCertified_duration_error
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    |driftGap * (h : ℝ) - ((m : ℝ) - (q : ℝ))| ≤
      t * (m : ℝ) + t + 2 :=
  certified_firstPassage_duration_error ht0 ht1 hxShell hxGood hhm hh hfp

/-- The shrinking high corridor for the reduced high-data package. -/
theorem timeoutDurationError_high_le
    (P : TimeoutHighRunData) {M m : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) :
    timeoutDurationError (timeoutHighTolerance P M m) m ≤
      (P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog1 : 1 ≤ Real.log ((M : ℝ) + 2) := by
    have hM3 : Real.exp 1 ≤ (M : ℝ) + 2 := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    simpa using (Real.le_log_iff_exp_le (by positivity)).2 hM3
  have hsqrtLog1 : 1 ≤ Real.sqrt (Real.log ((M : ℝ) + 2)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlog1
  have hsqrtM1 : 1 ≤ Real.sqrt (m : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have htD : timeoutHighTolerance P M m ≤
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) := by
    simp [timeoutHighTolerance, Nat.ne_of_gt hm]
  have hsqrtm0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hmain :
      Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) * (m : ℝ) =
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt (m : ℝ) := by
    have harg : (1 : ℝ) ≤ (M : ℝ) + 2 := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    rw [Real.sqrt_div (Real.log_nonneg harg)]
    field_simp [hsqrtm0.ne']
    nlinarith [Real.sq_sqrt hm0.le]
  have htmain : timeoutHighTolerance P M m * (m : ℝ) ≤
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
    calc
      timeoutHighTolerance P M m * (m : ℝ) ≤
          (P.D * Real.sqrt
            (Real.log ((M : ℝ) + 2) / (m : ℝ))) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right htD hm0.le
      _ = P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
        rw [mul_assoc, hmain]
        ring
  have htcap := timeoutHighTolerance_le_tau P M m
  have hscale1 : 1 ≤
      Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt (m : ℝ) :=
    one_le_mul_of_one_le_of_one_le hsqrtLog1 hsqrtM1
  unfold timeoutDurationError
  calc
    timeoutHighTolerance P M m * (m : ℝ) +
          timeoutHighTolerance P M m + 3 ≤
        P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m +
          P.tau + 3 := by linarith
    _ ≤ (P.D + P.tau + 3) *
          Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
      have hD0 := P.D_pos.le
      have htau0 := P.pHi.eta_pos.le
      nlinarith [mul_nonneg (add_nonneg htau0 (by norm_num : (0 : ℝ) ≤ 3))
        (sub_nonneg.mpr hscale1)]

/-- A timeout block has corridor width at most the switch rank.  This uses
only `duration ≤ m`, `q < m`, and `m < S`. -/
theorem lowTimeout_duration_error_le
    {K₀ : ℝ} {L S m x : ℕ}
    (hmS : m < S) (hpass : LowTimeoutPassage K₀ L m x)
    (hqparent : timeoutTargetRank K₀ L m < m) :
    |driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1 ≤ S := by
  have hgap0 : 0 ≤ driftGap := driftGap_pos.le
  have hgap1 : driftGap ≤ 1 := by
    linarith [driftGap_lt_a0, a0_lt_one]
  have hduration : (hpass.duration : ℝ) ≤ m := by
    exact_mod_cast hpass.duration_le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hq0 : (0 : ℝ) ≤ timeoutTargetRank K₀ L m := Nat.cast_nonneg _
  have hprod0 : 0 ≤ driftGap * (hpass.duration : ℝ) :=
    mul_nonneg hgap0 (Nat.cast_nonneg _)
  have hprodM : driftGap * (hpass.duration : ℝ) ≤ m := by
    nlinarith
  have hdiff0 : 0 ≤ (m : ℝ) - (timeoutTargetRank K₀ L m : ℝ) := by
    have hqm : (timeoutTargetRank K₀ L m : ℝ) ≤ m := by
      exact_mod_cast hqparent.le
    linarith
  have hdiffM : (m : ℝ) - (timeoutTargetRank K₀ L m : ℝ) ≤ m := by
    linarith
  have habs :
      |driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| ≤ m := by
    rw [abs_le]
    constructor <;> linarith
  have hmSreal : (m : ℝ) + 1 ≤ S := by exact_mod_cast hmS
  linarith

/-- Width potential for the timeout route.  Below the switch it is the exact
decreasing potential `S*q`; above the switch it carries an `S^2` reserve. -/
def timeoutTimePotential
    (P : TimeoutHighRunData) (M S q : ℕ) : ℝ :=
  if S < q then
    ((P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt q) /
          (1 - Real.sqrt (P.rHi : ℝ)) + (S : ℝ) ^ 2
  else
    (S : ℝ) * (q : ℝ)

private theorem timeout_sqrt_rat_lt_one
    {r : ℚ} (hr1 : r < 1) :
    Real.sqrt (r : ℝ) < 1 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num
  exact_mod_cast hr1

theorem timeoutTimePotential_nonneg
    (P : TimeoutHighRunData) (M S q : ℕ) :
    0 ≤ timeoutTimePotential P M S q := by
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr
    (timeout_sqrt_rat_lt_one
      (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1))
  have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  unfold timeoutTimePotential
  split_ifs <;> positivity

/-- One high rank drop pays its certified corridor and preserves the complete
future low-phase reserve. -/
theorem timeoutTimePotential_high_step
    (P : TimeoutHighRunData) {M S m q : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hSm : S ≤ m)
    (hq : (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ)) :
    timeoutDurationError (timeoutHighTolerance P M m) m +
        timeoutTimePotential P M S q ≤
      timeoutTimePotential P M S (m + 1) := by
  have hrHi0 : (0 : ℝ) ≤ P.rHi := P.pHi.r_pos.le
  have hsHi1 := timeout_sqrt_rat_lt_one
    (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1)
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr hsHi1
  have hcoefHi : 0 < P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((M : ℝ) + 2)) := Real.sqrt_nonneg _
  have hcost := timeoutDurationError_high_le P hM hm
  have hprevHigh : S < m + 1 := by omega
  by_cases hqHigh : S < q
  · have hsqrtq : Real.sqrt (q : ℝ) ≤
        Real.sqrt (P.rHi : ℝ) * Real.sqrt (m : ℝ) := by
      have hs := Real.sqrt_le_sqrt hq
      rw [Real.sqrt_mul hrHi0] at hs
      exact hs
    have hmSucc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
    have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hmSucc
    simp only [timeoutTimePotential, if_pos hqHigh, if_pos hprevHigh]
    have hscaled :
        (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt (m : ℝ) +
            ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt (q : ℝ)) / (1 - Real.sqrt (P.rHi : ℝ)) ≤
          ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt ((m + 1 : ℕ) : ℝ)) /
              (1 - Real.sqrt (P.rHi : ℝ)) := by
      apply (le_div_iff₀ hdHi).2
      rw [add_mul, div_mul_cancel₀ _ hdHi.ne']
      have hmulq := mul_le_mul_of_nonneg_left hsqrtq
        (mul_nonneg hcoefHi.le hlog0)
      have hmulm := mul_le_mul_of_nonneg_left hsqrtm
        (mul_nonneg hcoefHi.le hlog0)
      nlinarith
    linarith
  · have hqLow : q ≤ S := by omega
    simp only [timeoutTimePotential, if_neg hqHigh, if_pos hprevHigh]
    have hlowReserve : (S : ℝ) * (q : ℝ) ≤ (S : ℝ) ^ 2 := by
      have hqR : (q : ℝ) ≤ S := by exact_mod_cast hqLow
      have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
      nlinarith
    have hmSucc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
    have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hmSucc
    have hhighPay :
        (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt (m : ℝ) ≤
          ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt ((m + 1 : ℕ) : ℝ)) /
              (1 - Real.sqrt (P.rHi : ℝ)) := by
      have hbase := mul_le_mul_of_nonneg_left hsqrtm
        (mul_nonneg hcoefHi.le hlog0)
      have hdiv :
          (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt ((m + 1 : ℕ) : ℝ) ≤
            ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt ((m + 1 : ℕ) : ℝ)) /
                (1 - Real.sqrt (P.rHi : ℝ)) := by
        apply (le_div_iff₀ hdHi).2
        let A := (P.D + P.tau + 3) *
          Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt ((m + 1 : ℕ) : ℝ)
        have hA0 : 0 ≤ A := by
          dsimp [A]
          positivity
        have hdenLe : 1 - Real.sqrt (P.rHi : ℝ) ≤ 1 := by
          linarith [Real.sqrt_nonneg (P.rHi : ℝ)]
        change A * (1 - Real.sqrt (P.rHi : ℝ)) ≤ A
        calc
          A * (1 - Real.sqrt (P.rHi : ℝ)) ≤ A * 1 :=
            mul_le_mul_of_nonneg_left hdenLe hA0
          _ = A := mul_one A
      exact hbase.trans hdiv
    linarith

/-- One timeout block pays its whole crude corridor by strict rank descent. -/
theorem timeoutTimePotential_low_step
    (P : TimeoutHighRunData) {K₀ : ℝ} {L M S qPrev m x : ℕ}
    (hmS : m < S) (hpass : LowTimeoutPassage K₀ L m x)
    (hmPrevLo : m ≤ qPrev) (hmPrevHi : qPrev ≤ m + 1)
    (hqparent : timeoutTargetRank K₀ L m < m) :
    (|driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
        timeoutTimePotential P M S (timeoutTargetRank K₀ L m) ≤
      timeoutTimePotential P M S qPrev := by
  have hlocal := lowTimeout_duration_error_le hmS hpass hqparent
  have hqLow : ¬S < timeoutTargetRank K₀ L m := by omega
  have hprevLow : ¬S < qPrev := by omega
  simp only [timeoutTimePotential, if_neg hqLow, if_neg hprevLow]
  have hqR : (timeoutTargetRank K₀ L m : ℝ) + 1 ≤ m := by
    exact_mod_cast hqparent
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hmul : (S : ℝ) *
      ((timeoutTargetRank K₀ L m : ℝ) + 1) ≤ (S : ℝ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hqR hS0
  have hmPrevR : (m : ℝ) ≤ (qPrev : ℝ) := by exact_mod_cast hmPrevLo
  calc
    (|driftGap * (hpass.duration : ℝ) -
          ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
        (S : ℝ) * (timeoutTargetRank K₀ L m : ℝ) ≤
      (S : ℝ) + (S : ℝ) * (timeoutTargetRank K₀ L m : ℝ) :=
        by gcongr
    _ = (S : ℝ) * ((timeoutTargetRank K₀ L m : ℝ) + 1) := by ring
    _ ≤ (S : ℝ) * (m : ℝ) := hmul
    _ ≤ (S : ℝ) * (qPrev : ℝ) :=
      mul_le_mul_of_nonneg_left hmPrevR hS0

/-- Every timeout run lies in one common interval around the linear-drift
center `(M+1)-q`. -/
theorem TimeoutRecertificationRun.deviation_add_potential_le
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| +
        timeoutTimePotential P M S q ≤
      timeoutTimePotential P M S (M + 1) := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      have hlen := stageLength_le_shell (timeoutHighSetup P M M)
        hM0 hnShell hnGood
      have hpos := stageLength_pos (timeoutHighSetup P M M)
        hM0 hnShell hnGood
      have hfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi M) n
          (stageLength (timeoutHighSetup P M M) n) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (timeoutHighSetup P M M)
            hM0 hnShell hnGood
      have herr := timeoutCertified_duration_error
        (timeoutHighTolerance_pos P M M).le
        ((timeoutHighTolerance_le_tau P M M).trans P.pHi.eta_le_one)
        hnShell hnGood hlen hpos hfp
      have hq : (rationalTargetRank P.rHi M : ℝ) ≤
          (P.rHi : ℝ) * (M : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (M : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg M)
        exact Nat.floor_le hnonneg
      have hstep := timeoutTimePotential_high_step P
        (S := S) (m := M) (q := rationalTargetRank P.rHi M)
        hM hM hSM hq
      have habs :
          |driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi M : ℝ))| ≤
            timeoutDurationError (timeoutHighTolerance P M M) M := by
        have hshift :
            driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                (((M + 1 : ℕ) : ℝ) -
                  (rationalTargetRank P.rHi M : ℝ)) =
              (driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1 := by
          push_cast
          ring
        rw [hshift]
        calc
          |(driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
              ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1| ≤
              |driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))| + 1 := by
            simpa using (abs_sub_le
              (driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) 0 (1 : ℝ))
          _ ≤ timeoutDurationError (timeoutHighTolerance P M M) M := by
            unfold timeoutDurationError
            linarith
      linarith
  | @nextHi elapsed qPrev m hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      have hm1 : 1 ≤ m := P.pHi.M0_pos.trans hm0
      have hlen := stageLength_le_shell (timeoutHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hpos := stageLength_pos (timeoutHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hlocalfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi m)
          (orbit elapsed n)
          (stageLength (timeoutHighSetup P M m) (orbit elapsed n)) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (timeoutHighSetup P M m)
            hm0 hsourceShell hsourceGood
      have herr := timeoutCertified_duration_error
        (timeoutHighTolerance_pos P M m).le
        ((timeoutHighTolerance_le_tau P M m).trans P.pHi.eta_le_one)
        hsourceShell hsourceGood hlen hpos hlocalfp
      have hq : (rationalTargetRank P.rHi m : ℝ) ≤
          (P.rHi : ℝ) * (m : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (m : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg m)
        exact Nat.floor_le hnonneg
      have hstep := timeoutTimePotential_high_step P
        (S := S) (m := m) (q := rationalTargetRank P.rHi m)
        hM hm1 hSm hq
      rw [←hmPrev] at hstep
      have hdecomp :
          driftGap * ((elapsed +
              stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap *
                (stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℝ) -
              ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))) - 1 := by
        rw [hmPrev]
        push_cast
        ring
      rw [hdecomp]
      have habs := timeout_abs_add_sub_one_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap *
            (stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℝ) -
          ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ)))
      have hlocal :
          |driftGap *
              (stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℝ) -
            ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))| + 1 ≤
            timeoutDurationError (timeoutHighTolerance P M m) m := by
        unfold timeoutDurationError
        linarith
      linarith
  | @nextLo elapsed qPrev m hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass
      hqpos hqparent hgap ih =>
      have hstep := timeoutTimePotential_low_step P (M := M) hmS hpass
        hmPrevLo hmPrevHi hqparent
      let e : ℕ := qPrev - m
      have heLe : e ≤ 1 := by
        dsimp [e]
        omega
      have heEq : (e : ℝ) = (qPrev : ℝ) - (m : ℝ) := by
        dsimp [e]
        rw [Nat.cast_sub hmPrevLo]
      have hdecomp :
          driftGap * ((elapsed + hpass.duration : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (timeoutTargetRank K₀ L m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ) := by
        rw [heEq]
        push_cast
        ring
      rw [hdecomp]
      have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      have he1 : (e : ℝ) ≤ 1 := by exact_mod_cast heLe
      have habs0 := abs_sub_le
        ((driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
        (driftGap * (hpass.duration : ℝ) -
          ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))) 0 (e : ℝ)
      have habsAdd := abs_add_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap * (hpass.duration : ℝ) -
          ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))
      have habs :
          |(driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| ≤
            |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            |driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1 := by
        have heabs : |(e : ℝ)| ≤ 1 := by rw [abs_of_nonneg he0]; exact he1
        have habsSub :
            |(driftGap * (elapsed : ℝ) -
                (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
              (driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| ≤
              |(driftGap * (elapsed : ℝ) -
                  (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
                (driftGap * (hpass.duration : ℝ) -
                  ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))| + |(e : ℝ)| := by
          simpa using habs0
        calc
          |(driftGap * (elapsed : ℝ) -
                (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
              (driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| ≤
            |(driftGap * (elapsed : ℝ) -
                  (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
                (driftGap * (hpass.duration : ℝ) -
                  ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))| + |(e : ℝ)| :=
              habsSub
          _ ≤ (|driftGap * (elapsed : ℝ) -
                (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
              |driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))|) +
              |(e : ℝ)| := by gcongr
          _ ≤ _ := by linarith
      calc
        |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)) +
            (driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| +
            timeoutTimePotential P M S (timeoutTargetRank K₀ L m) ≤
          (|driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            |driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
            timeoutTimePotential P M S (timeoutTargetRank K₀ L m) :=
              by gcongr
        _ = |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            ((|driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
              timeoutTimePotential P M S (timeoutTargetRank K₀ L m)) := by ring
        _ ≤ |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            timeoutTimePotential P M S qPrev := by gcongr
        _ ≤ timeoutTimePotential P M S (M + 1) := ih

/-- A finite cutoff containing every realized timeout-run time. -/
def timeoutFeasibleTimeCutoff
    (P : TimeoutHighRunData) (M S : ℕ) : ℕ :=
  ⌈((((M + 1 : ℕ) : ℝ) + timeoutTimePotential P M S (M + 1)) /
      driftGap)⌉₊

/-- All cumulative timeout-run times ending at rank `q`. -/
noncomputable def timeoutFeasibleTimes
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (timeoutFeasibleTimeCutoff P M S + 1)).filter fun h =>
    ∃ n : ℕ, n ∈ dyadicShell M ∧
      TimeoutRecertificationRun P K₀ L M S n h q

theorem TimeoutRecertificationRun.mem_timeoutFeasibleTimes
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hnShell : n ∈ dyadicShell M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    elapsed ∈ timeoutFeasibleTimes P K₀ L M S q := by
  classical
  have hdev := hrun.deviation_add_potential_le hM
  have hpotq0 := timeoutTimePotential_nonneg P M S q
  have habs :
      |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
        timeoutTimePotential P M S (M + 1) := by
    linarith
  have hupper := (abs_le.mp habs).2
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hreal : (elapsed : ℝ) ≤
      (((M + 1 : ℕ) : ℝ) + timeoutTimePotential P M S (M + 1)) /
        driftGap := by
    rw [le_div_iff₀ driftGap_pos]
    linarith
  have hceilReal := Nat.le_ceil
    ((((M + 1 : ℕ) : ℝ) + timeoutTimePotential P M S (M + 1)) / driftGap)
  have hbound : elapsed ≤ timeoutFeasibleTimeCutoff P M S := by
    exact_mod_cast hreal.trans hceilReal
  simp only [timeoutFeasibleTimes, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, n, hnShell, hrun⟩

/-- Exact cardinality bound for the feasible timeout times. -/
theorem timeoutFeasibleTimes_card_le_potential
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {L M S q : ℕ} (hM : 1 ≤ M) :
    (timeoutFeasibleTimes P K₀ L M S q).card ≤
      ⌈(1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap)⌉₊ := by
  classical
  let times := timeoutFeasibleTimes P K₀ L M S q
  by_cases hne : times.Nonempty
  · have hspan := finset_card_le_one_add_span times hne
    have hmaxMem := times.max'_mem hne
    have hminMem := times.min'_mem hne
    have hmaxMem' : times.max' hne ∈ timeoutFeasibleTimes P K₀ L M S q := by
      simpa [times] using hmaxMem
    have hminMem' : times.min' hne ∈ timeoutFeasibleTimes P K₀ L M S q := by
      simpa [times] using hminMem
    rw [timeoutFeasibleTimes, Finset.mem_filter] at hmaxMem' hminMem'
    rcases hmaxMem'.2 with ⟨xmax, hxShell, hxrun⟩
    rcases hminMem'.2 with ⟨xmin, hxminShell, hxminrun⟩
    have hxdev := hxrun.deviation_add_potential_le hM
    have hmindev := hxminrun.deviation_add_potential_le hM
    have hpotq0 := timeoutTimePotential_nonneg P M S q
    have hxabs :
        |driftGap * (times.max' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            timeoutTimePotential P M S (M + 1) := by
      linarith
    have hminabs :
        |driftGap * (times.min' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            timeoutTimePotential P M S (M + 1) := by
      linarith
    have hdiff :
        ((times.max' hne : ℕ) : ℝ) - (times.min' hne : ℝ) ≤
          2 * timeoutTimePotential P M S (M + 1) / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      have hmaxUpper := (abs_le.mp hxabs).2
      have hminLower := (abs_le.mp hminabs).1
      nlinarith
    have hcardR : ((times.card : ℕ) : ℝ) ≤
        1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap := by
      have hspanR : ((times.card : ℕ) : ℝ) ≤
          1 + (times.max' hne : ℝ) - (times.min' hne : ℝ) := by
        exact_mod_cast hspan
      linarith
    have hceil := Nat.le_ceil
      (1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap)
    exact_mod_cast hcardR.trans hceil
  · have hempty : times = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hactual : timeoutFeasibleTimes P K₀ L M S q = ∅ := by
      simpa [times] using hempty
    rw [hactual]
    exact Nat.zero_le _

/-- Explicit constant for the square-root-logarithmic timeout support. -/
def timeoutTimeSupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  2 + 2 / driftGap *
    ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
      (C + 5) ^ 2)

private theorem eventually_timeout_log_sq_le_sqrt_mul :
    ∀ᶠ M : ℕ in atTop,
      (Real.log ((M : ℝ) + 2)) ^ 2 ≤
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hsmallReal :=
    (Real.isLittleO_pow_log_id_atTop (n := 3)).bound
      (by norm_num : (0 : ℝ) < 1)
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with M hsmall hM
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hlog1 : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    dsimp [x]
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog1
  have hlogCube0 : 0 ≤ (Real.log x) ^ 3 := by positivity
  have hsmall' : (Real.log x) ^ 3 ≤ x := by
    simpa [x, id_eq, Real.norm_eq_abs, abs_of_nonneg hlogCube0,
      abs_of_nonneg hlog0, abs_of_nonneg hx0] using hsmall
  have hfourth : (Real.log x) ^ 4 ≤ x * Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall' hlog0]
  have hroot0 := Real.sqrt_nonneg (x * Real.log x)
  have hrootSq := Real.sq_sqrt (mul_nonneg hx0 hlog0)
  dsimp [x] at *
  nlinarith [sq_nonneg ((Real.log ((M : ℝ) + 2)) ^ 2 -
    Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)))]

/-- The high corridor plus the crude `S²` timeout reserve has the same
square-root-logarithmic scale as the frozen feasible-time support. -/
theorem eventually_timeoutTimePotential_source_le_sqrt
    (P : TimeoutHighRunData) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeout_log_sq_le_sqrt_mul,
      eventually_shrinkingSwitchRank_lt_source hC,
      eventually_ge_atTop (1 : ℕ)] with M hlogSq hSwitch hM
  let x : ℝ := (M : ℝ) + 2
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog1 : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp [x]
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt (x * Real.log x) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    nlinarith [show 0 ≤ Real.log x from zero_le_one.trans hlog1]
  have hsqrtM :
      Real.sqrt (Real.log x) * Real.sqrt ((M + 1 : ℕ) : ℝ) ≤
        Real.sqrt (x * Real.log x) := by
    rw [← Real.sqrt_mul (Real.log_nonneg hx1)]
    apply Real.sqrt_le_sqrt
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    dsimp [x]
    push_cast
    nlinarith
  have hS := shrinkingSwitchRank_lt_add_one hC M
  have hSle : (shrinkingSwitchRank C M : ℝ) ≤
      (C + 5) * Real.log x := by
    have hC5 : 0 ≤ C + 5 := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    apply le_of_lt
    calc
      (shrinkingSwitchRank C M : ℝ) < C * Real.log x + 1 := by
        simpa [x] using hS
      _ ≤ (C + 5) * Real.log x := by nlinarith
  have hlow :
      (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
        (C + 5) ^ 2 * Real.sqrt (x * Real.log x) := by
    have hC5 : 0 ≤ C + 5 := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hS0 : 0 ≤ (shrinkingSwitchRank C M : ℝ) := Nat.cast_nonneg _
    have hsquare :
        (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
          ((C + 5) * Real.log x) ^ 2 := by nlinarith
    calc
      (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
          ((C + 5) * Real.log x) ^ 2 := hsquare
      _ = (C + 5) ^ 2 * (Real.log x) ^ 2 := by ring
      _ ≤ (C + 5) ^ 2 * Real.sqrt (x * Real.log x) := by
        exact mul_le_mul_of_nonneg_left (by simpa [x] using hlogSq) (sq_nonneg _)
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr
    (timeout_sqrt_rat_lt_one
      (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1))
  have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hpot :
      timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2) * Real.sqrt (x * Real.log x) := by
    rw [timeoutTimePotential,
      if_pos (by omega : shrinkingSwitchRank C M < M + 1)]
    calc
      ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt (((M + 1 : ℕ) : ℝ))) /
              (1 - Real.sqrt (P.rHi : ℝ)) +
          (shrinkingSwitchRank C M : ℝ) ^ 2 ≤
        ((P.D + P.tau + 3) * Real.sqrt (x * Real.log x)) /
              (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2 * Real.sqrt (x * Real.log x) := by
        apply add_le_add
        · apply (div_le_div_iff_of_pos_right hdHi).2
          simpa [x, mul_assoc] using
            (mul_le_mul_of_nonneg_left hsqrtM hcoefHi)
        · exact hlow
      _ = ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2) * Real.sqrt (x * Real.log x) := by ring
  unfold timeoutTimeSupportConstant
  calc
    1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap ≤
      1 + 2 * (((P.D + P.tau + 3) /
          (1 - Real.sqrt (P.rHi : ℝ)) + (C + 5) ^ 2) *
            Real.sqrt (x * Real.log x)) / driftGap := by
      have hmul := mul_le_mul_of_nonneg_left hpot (by norm_num : (0 : ℝ) ≤ 2)
      have hdiv := div_le_div_of_nonneg_right hmul driftGap_pos.le
      linarith
    _ ≤ (2 + 2 / driftGap *
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (C + 5) ^ 2)) * Real.sqrt (x * Real.log x) := by
      let B := (P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
        (C + 5) ^ 2
      have hid :
          (2 + 2 / driftGap * B) * Real.sqrt (x * Real.log x) -
            (1 + 2 * (B * Real.sqrt (x * Real.log x)) / driftGap) =
              2 * Real.sqrt (x * Real.log x) - 1 := by ring
      dsimp only [B] at hid
      linarith

/-- Eventually every fixed-rank timeout time support has
`O(sqrt(M log M))` cardinality. -/
theorem eventually_timeoutFeasibleTimes_card_lt_sqrt
    (P : TimeoutHighRunData) (K₀ : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      ∀ L q : ℕ,
        ((timeoutFeasibleTimes P K₀ L M (shrinkingSwitchRank C M) q).card : ℝ) <
          (timeoutTimeSupportConstant P C + 1) *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutTimePotential_source_le_sqrt P hC,
      eventually_ge_atTop (1 : ℕ)] with M hpotential hM
  intro L q
  have hcard := timeoutFeasibleTimes_card_le_potential P K₀
    (L := L) (S := shrinkingSwitchRank C M) (q := q) hM
  have hpot0 := timeoutTimePotential_nonneg P M
    (shrinkingSwitchRank C M) (M + 1)
  have hceil :
      (⌈(1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap)⌉₊ : ℝ) <
      (1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap) + 1 := by
    apply Nat.ceil_lt_add_one
    have hquot : 0 ≤
        2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := div_nonneg (mul_nonneg (by norm_num) hpot0) driftGap_pos.le
    linarith
  have hcardR :
      ((timeoutFeasibleTimes P K₀ L M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := by exact_mod_cast hcard
  have hsqrt1 : 1 ≤
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hlog1 : 1 ≤ Real.log ((M : ℝ) + 2) := by
      apply (Real.le_log_iff_exp_le (by positivity)).2
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    nlinarith
  calc
    ((timeoutFeasibleTimes P K₀ L M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := hcardR
    _ < (1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap) + 1 := hceil
    _ ≤ timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) + 1 := by
      linarith
    _ ≤ (timeoutTimeSupportConstant P C + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
      nlinarith

end

end FirstPassageLinearTransport
