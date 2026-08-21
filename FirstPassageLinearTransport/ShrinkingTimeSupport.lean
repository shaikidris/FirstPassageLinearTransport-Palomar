/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingBarrierRun

/-!
# Feasible cumulative times for the shrinking-barrier chain

The successful landing shell is deterministic.  The only remaining freedom
is the duration of each block.  The potential in this file sums the widths of
the one-block duration corridors and gives one explicit finite support for
every cumulative first-bad time.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- Width budget used for one duration corridor.  The extra `1` pays the
one-rank offset between a threshold and the next parent shell. -/
def durationError (t : ℝ) (m : ℕ) : ℝ :=
  t * (m : ℝ) + t + 3

private theorem abs_add_sub_one_le (a b : ℝ) :
    |a + b - 1| ≤ |a| + |b| + 1 := by
  calc
    |a + b - 1| ≤ |a + b| + 1 := by
      simpa using (abs_sub_le (a + b) 0 (1 : ℝ))
    _ ≤ |a| + |b| + 1 := by
      linarith [abs_add_le a b]

/-- A one-block duration lies within `durationError` of its deterministic
linear-drift center. -/
theorem certified_firstPassage_duration_error
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    |driftGap * (h : ℝ) - ((m : ℝ) - (q : ℝ))| ≤
      t * (m : ℝ) + t + 2 := by
  have hc := certified_firstPassage_duration_corridor ht0 ht1 hxShell
    hxGood hhm hh hfp
  rw [abs_le]
  constructor <;> nlinarith

/-- The high-rank width is at most a square-root rank cost. -/
theorem durationError_shrinkingHigh_le
    (P : ShrinkingBarrierRunData) {M m : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) :
    durationError (shrinkingHighTolerance P M m) m ≤
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
  have htD : shrinkingHighTolerance P M m ≤
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) := by
    simp [shrinkingHighTolerance, Nat.ne_of_gt hm]
  have hsqrtm0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hsqrtSq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt hm0.le
  have hmain :
      Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)) * (m : ℝ) =
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt (m : ℝ) := by
    have harg : (1 : ℝ) ≤ (M : ℝ) + 2 := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    rw [Real.sqrt_div (Real.log_nonneg harg)]
    field_simp [hsqrtm0.ne']
    nlinarith
  have htmain : shrinkingHighTolerance P M m * (m : ℝ) ≤
      P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
    calc
      shrinkingHighTolerance P M m * (m : ℝ) ≤
          (P.D * Real.sqrt
            (Real.log ((M : ℝ) + 2) / (m : ℝ))) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right htD hm0.le
      _ = P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
        rw [mul_assoc, hmain]
        ring
  have htcap := shrinkingHighTolerance_le_tau P M m
  have hscale1 : 1 ≤
      Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt (m : ℝ) :=
    one_le_mul_of_one_le_of_one_le hsqrtLog1 hsqrtM1
  unfold durationError
  calc
    shrinkingHighTolerance P M m * (m : ℝ) +
          shrinkingHighTolerance P M m + 3 ≤
        P.D * Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m +
          P.tau + 3 := by linarith
    _ ≤ (P.D + P.tau + 3) *
          Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt m := by
      have hD0 := P.D_pos.le
      have htau0 := P.pHi.eta_pos.le
      nlinarith [mul_nonneg (add_nonneg htau0 (by norm_num : (0 : ℝ) ≤ 3))
        (sub_nonneg.mpr hscale1)]

/-- The fixed low-rank width is at most a linear rank cost. -/
theorem durationError_low_le
    (P : ShrinkingBarrierRunData) {m : ℕ} (hm : 1 ≤ m) :
    durationError P.etaLo m ≤ (2 * P.etaLo + 3) * (m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold durationError
  nlinarith [P.pLo.eta_pos.le]

/-- Remaining width potential at threshold rank `q`.  The strict test
`S < q` matches exactly the deterministic relation `qPrev=m+1`. -/
def shrinkingTimePotential
    (P : ShrinkingBarrierRunData) (M S q : ℕ) : ℝ :=
  if S < q then
    ((P.D + P.tau + 3) *
        Real.sqrt (Real.log ((M : ℝ) + 2)) * Real.sqrt q) /
          (1 - Real.sqrt (P.rHi : ℝ)) +
      ((2 * P.etaLo + 3) * (S : ℝ)) / (1 - (P.rLo : ℝ))
  else
    ((2 * P.etaLo + 3) * (q : ℝ)) / (1 - (P.rLo : ℝ))

private theorem sqrt_rat_lt_one
    {r : ℚ} (hr1 : r < 1) :
    Real.sqrt (r : ℝ) < 1 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num
  exact_mod_cast hr1

private theorem floor_rank_real_le
    {r : ℚ} (hr0 : 0 ≤ r) (m : ℕ) :
    (rationalTargetRank r m : ℝ) ≤ (r : ℝ) * (m : ℝ) := by
  exact Nat.floor_le (mul_nonneg (by exact_mod_cast hr0) (Nat.cast_nonneg m))

/-- One deterministic rank step pays its complete corridor-width budget. -/
theorem shrinkingTimePotential_step
    (P : ShrinkingBarrierRunData) {M S qPrev m q : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hmPrev : qPrev = m + 1)
    (hq : if S ≤ m then
        (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ)
      else (q : ℝ) ≤ (P.rLo : ℝ) * (m : ℝ)) :
    (if S ≤ m then durationError (shrinkingHighTolerance P M m) m
      else durationError P.etaLo m) + shrinkingTimePotential P M S q ≤
        shrinkingTimePotential P M S qPrev := by
  subst qPrev
  have hrHi0 : (0 : ℝ) ≤ P.rHi := P.pHi.r_pos.le
  have hrLo0 : (0 : ℝ) ≤ P.rLo := P.pLo.r_pos.le
  have hsHi1 := sqrt_rat_lt_one
    (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1)
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr hsHi1
  have hdLo : 0 < 1 - (P.rLo : ℝ) := sub_pos.mpr P.pLo.r_lt_one
  have hcoefHi : 0 < P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hcoefLo : 0 < 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((M : ℝ) + 2)) := Real.sqrt_nonneg _
  by_cases hmHigh : S ≤ m
  · have hqBound : (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ) := by
      simpa [hmHigh] using hq
    have hprevHigh : S < m + 1 := by omega
    have hcost := durationError_shrinkingHigh_le P hM hm
    by_cases hqHigh : S < q
    · have hsqrtq : Real.sqrt (q : ℝ) ≤
          Real.sqrt (P.rHi : ℝ) * Real.sqrt (m : ℝ) := by
        have hs := Real.sqrt_le_sqrt hqBound
        rw [Real.sqrt_mul hrHi0] at hs
        exact hs
      have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by norm_num)
      rw [if_pos hmHigh]
      simp only [shrinkingTimePotential, if_pos hqHigh, if_pos hprevHigh]
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
      rw [if_pos hmHigh]
      simp only [shrinkingTimePotential, if_neg hqHigh, if_pos hprevHigh]
      have hlowReserve :
          ((2 * P.etaLo + 3) * (q : ℝ)) / (1 - (P.rLo : ℝ)) ≤
            ((2 * P.etaLo + 3) * (S : ℝ)) / (1 - (P.rLo : ℝ)) := by
        apply (div_le_div_iff_of_pos_right hdLo).2
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqLow) hcoefLo.le
      have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by norm_num)
      have hhighPay :
          (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt (m : ℝ) ≤
            ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt ((m + 1 : ℕ) : ℝ)) /
              (1 - Real.sqrt (P.rHi : ℝ)) := by
        have hbase := mul_le_mul_of_nonneg_left hsqrtm
          (mul_nonneg hcoefHi.le hlog0)
        have hdenLe : 1 - Real.sqrt (P.rHi : ℝ) ≤ 1 := by
          linarith [Real.sqrt_nonneg (P.rHi : ℝ)]
        have hdiv :
            (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
                Real.sqrt ((m + 1 : ℕ) : ℝ) ≤
              ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
                Real.sqrt ((m + 1 : ℕ) : ℝ)) /
                (1 - Real.sqrt (P.rHi : ℝ)) := by
          apply (le_div_iff₀ hdHi).2
          nlinarith [mul_nonneg (mul_nonneg hcoefHi.le hlog0)
            (Real.sqrt_nonneg ((m + 1 : ℕ) : ℝ))]
        exact hbase.trans hdiv
      linarith
  · have hmLow : m < S := Nat.lt_of_not_ge hmHigh
    have hprevLow : ¬ S < m + 1 := by omega
    have hqBound : (q : ℝ) ≤ (P.rLo : ℝ) * (m : ℝ) := by
      simpa [hmHigh] using hq
    have hqLow : ¬ S < q := by
      have hm0R : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hrmul : (P.rLo : ℝ) * (m : ℝ) ≤ (m : ℝ) := by
        nlinarith [P.pLo.r_lt_one]
      have hqm : q ≤ m := by exact_mod_cast hqBound.trans hrmul
      omega
    have hcost := durationError_low_le P hm
    rw [if_neg hmHigh]
    simp only [shrinkingTimePotential, if_neg hqLow, if_neg hprevLow]
    apply (le_div_iff₀ hdLo).2
    rw [add_mul, div_mul_cancel₀ _ hdLo.ne']
    have hcostMul := mul_le_mul_of_nonneg_right hcost hdLo.le
    have hqMul := mul_le_mul_of_nonneg_left hqBound hcoefLo.le
    push_cast
    nlinarith

/-- Every literal run stays in one deterministic interval around the linear
drift time. -/
theorem ShrinkingRecertificationRun.deviation_add_potential_le
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hM : 1 ≤ M)
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| +
        shrinkingTimePotential P M S q ≤
      shrinkingTimePotential P M S (M + 1) := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      have hlen := stageLength_le_shell (shrinkingHighSetup P M M)
        hM0 hnShell hnGood
      have hpos := stageLength_pos (shrinkingHighSetup P M M)
        hM0 hnShell hnGood
      have hfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi M) n
          (stageLength (shrinkingHighSetup P M M) n) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (shrinkingHighSetup P M M)
            hM0 hnShell hnGood
      have herr := certified_firstPassage_duration_error
        (shrinkingHighTolerance_pos P M M).le
        (shrinkingHighTolerance_le_tau P M M |>.trans P.pHi.eta_le_one)
        hnShell hnGood hlen hpos hfp
      have hq := floor_rank_real_le
        (by exact_mod_cast P.pHi.r_pos.le : (0 : ℚ) ≤ P.rHi) M
      have hstep := shrinkingTimePotential_step P
        (S := S) (qPrev := M + 1) (m := M)
        (q := rationalTargetRank P.rHi M) hM hM rfl (by
        simpa [hSM] using hq)
      rw [if_pos hSM] at hstep
      have habs :
          |driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi M : ℝ))| ≤
            durationError (shrinkingHighTolerance P M M) M := by
        have hshift :
            driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                (((M + 1 : ℕ) : ℝ) -
                  (rationalTargetRank P.rHi M : ℝ)) =
              (driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1 := by
          push_cast
          ring
        rw [hshift]
        calc
          |(driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
              ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1| ≤
              |driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))| + 1 :=
            by
              simpa using (abs_sub_le
                (driftGap *
                  (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                    ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ)))
                0 (1 : ℝ))
          _ ≤ durationError (shrinkingHighTolerance P M M) M := by
            unfold durationError
            linarith
      linarith
  | @nextHi elapsed qPrev m hrun hSm hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq
        (shrinkingHighTolerance_lt_a0 P M m) hsourceGood hsourceShell
      have hm1 : 1 ≤ m := P.pHi.M0_pos.trans hm0
      have hlen := stageLength_le_shell (shrinkingHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hpos := stageLength_pos (shrinkingHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hlocalfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi m)
          (orbit elapsed n)
          (stageLength (shrinkingHighSetup P M m) (orbit elapsed n)) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (shrinkingHighSetup P M m)
            hm0 hsourceShell hsourceGood
      have herr := certified_firstPassage_duration_error
        (shrinkingHighTolerance_pos P M m).le
        (shrinkingHighTolerance_le_tau P M m |>.trans P.pHi.eta_le_one)
        hsourceShell hsourceGood hlen hpos hlocalfp
      have hq := floor_rank_real_le
        (by exact_mod_cast P.pHi.r_pos.le : (0 : ℚ) ≤ P.rHi) m
      have hprevpos := hrun.currentRank_pos
      have hmPrevEq : qPrev = m + 1 := by omega
      have hstep := shrinkingTimePotential_step P
        (S := S) (qPrev := qPrev) (m := m)
        (q := rationalTargetRank P.rHi m) hM hm1 hmPrevEq (by
        simpa [hSm] using hq)
      rw [if_pos hSm] at hstep
      have hdecomp :
          driftGap * ((elapsed +
              stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap *
                (stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℝ) -
              ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))) - 1 := by
        rw [hmPrevEq]
        push_cast
        ring
      rw [hdecomp]
      have habs := abs_add_sub_one_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap *
            (stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℝ) -
          ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ)))
      have hlocal :
          |driftGap *
              (stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℝ) -
            ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))| + 1 ≤
            durationError (shrinkingHighTolerance P M m) m := by
        unfold durationError
        linarith
      linarith
  | @nextLo elapsed qPrev m hrun hmS hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq P.etaLo_lt_a0
        hsourceGood hsourceShell
      have hm1 : 1 ≤ m := P.pLo.M0_pos.trans hm0
      have hlen := stageLength_le_shell P.pLo hm0 hsourceShell hsourceGood
      have hpos := stageLength_pos P.pLo hm0 hsourceShell hsourceGood
      have hlocalfp : IsFirstPassage (2 ^ rationalTargetRank P.rLo m)
          (orbit elapsed n) (stageLength P.pLo (orbit elapsed n)) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage P.pLo hm0 hsourceShell hsourceGood
      have herr := certified_firstPassage_duration_error P.pLo.eta_pos.le
        P.pLo.eta_le_one hsourceShell hsourceGood hlen hpos hlocalfp
      have hq := floor_rank_real_le
        (by exact_mod_cast P.pLo.r_pos.le : (0 : ℚ) ≤ P.rLo) m
      have hprevpos := hrun.currentRank_pos
      have hmPrevEq : qPrev = m + 1 := by omega
      have hstep := shrinkingTimePotential_step P
        (S := S) (qPrev := qPrev) (m := m)
        (q := rationalTargetRank P.rLo m) hM hm1 hmPrevEq (by
        simpa [show ¬ S ≤ m by omega] using hq)
      rw [if_neg (show ¬ S ≤ m by omega)] at hstep
      have hdecomp :
          driftGap * ((elapsed + stageLength P.pLo (orbit elapsed n) : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rLo m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap * (stageLength P.pLo (orbit elapsed n) : ℝ) -
              ((m : ℝ) - (rationalTargetRank P.rLo m : ℝ))) - 1 := by
        rw [hmPrevEq]
        push_cast
        ring
      rw [hdecomp]
      have habs := abs_add_sub_one_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap * (stageLength P.pLo (orbit elapsed n) : ℝ) -
          ((m : ℝ) - (rationalTargetRank P.rLo m : ℝ)))
      have hlocal :
          |driftGap * (stageLength P.pLo (orbit elapsed n) : ℝ) -
            ((m : ℝ) - (rationalTargetRank P.rLo m : ℝ))| + 1 ≤
            durationError P.etaLo m := by
        unfold durationError
        linarith
      linarith

/-- All cumulative times of literal runs ending at rank `q`. -/
noncomputable def shrinkingFeasibleTimes
    (P : ShrinkingBarrierRunData) (M S q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (twoRegimeHorizon P.rHi P.rLo S M + 1)).filter fun h =>
    ∃ n : ℕ, n ∈ dyadicShell M ∧
      ShrinkingRecertificationRun P M S n h q

@[simp] theorem mem_shrinkingFeasibleTimes
    {P : ShrinkingBarrierRunData} {M S q h : ℕ} :
    h ∈ shrinkingFeasibleTimes P M S q ↔
      h ≤ twoRegimeHorizon P.rHi P.rLo S M ∧
        ∃ n : ℕ, n ∈ dyadicShell M ∧
          ShrinkingRecertificationRun P M S n h q := by
  classical
  simp only [shrinkingFeasibleTimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hh, n, hnShell, hrun⟩
    exact ⟨by omega, n, hnShell, hrun⟩
  · rintro ⟨hh, n, hnShell, hrun⟩
    exact ⟨by omega, n, hnShell, hrun⟩

/-- Exact support-cardinality bound before asymptotic simplification. -/
theorem shrinkingFeasibleTimes_card_le_potential
    (P : ShrinkingBarrierRunData) {M S q : ℕ} (hM : 1 ≤ M) :
    (shrinkingFeasibleTimes P M S q).card ≤
      ⌈(1 + 2 * shrinkingTimePotential P M S (M + 1) / driftGap)⌉₊ := by
  classical
  let times := shrinkingFeasibleTimes P M S q
  by_cases hne : times.Nonempty
  · have hspan := finset_card_le_one_add_span times hne
    have hmaxMem := times.max'_mem hne
    have hminMem := times.min'_mem hne
    rcases mem_shrinkingFeasibleTimes.mp hmaxMem with ⟨_hmaxH, xmax, hxShell, hxrun⟩
    rcases mem_shrinkingFeasibleTimes.mp hminMem with ⟨_hminH, xmin, hxminShell, hxminrun⟩
    have hxdev := (hxrun.deviation_add_potential_le hM)
    have hmindev := (hxminrun.deviation_add_potential_le hM)
    have hpot0 : 0 ≤ shrinkingTimePotential P M S q := by
      have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr
        (sqrt_rat_lt_one
          (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1))
      have hdLo : 0 < 1 - (P.rLo : ℝ) := sub_pos.mpr P.pLo.r_lt_one
      have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
        nlinarith [P.D_pos, P.pHi.eta_pos]
      have hcoefLo : 0 ≤ 2 * P.etaLo + 3 := by
        nlinarith [P.pLo.eta_pos]
      unfold shrinkingTimePotential
      split_ifs <;> positivity
    have hxabs :
        |driftGap * (times.max' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            shrinkingTimePotential P M S (M + 1) := by
      linarith
    have hminabs :
        |driftGap * (times.min' hne : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
            shrinkingTimePotential P M S (M + 1) := by
      linarith
    have hdiff :
        ((times.max' hne : ℕ) : ℝ) - (times.min' hne : ℝ) ≤
          2 * shrinkingTimePotential P M S (M + 1) / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      have hmaxUpper := (abs_le.mp hxabs).2
      have hminLower := (abs_le.mp hminabs).1
      nlinarith
    have hcardR : ((times.card : ℕ) : ℝ) ≤
        1 + 2 * shrinkingTimePotential P M S (M + 1) / driftGap := by
      have hspanR : ((times.card : ℕ) : ℝ) ≤
          1 + (times.max' hne : ℝ) - (times.min' hne : ℝ) := by
        exact_mod_cast hspan
      linarith
    have hceil := Nat.le_ceil
      (1 + 2 * shrinkingTimePotential P M S (M + 1) / driftGap)
    exact_mod_cast hcardR.trans hceil
  · have hempty : times = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hactual : shrinkingFeasibleTimes P M S q = ∅ := by
      simpa [times] using hempty
    rw [hactual]
    exact Nat.zero_le _

end

end FirstPassageLinearTransport
