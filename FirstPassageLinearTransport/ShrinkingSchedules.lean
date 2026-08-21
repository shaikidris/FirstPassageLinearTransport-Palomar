/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingTimeSupport
import FirstPassageLinearTransport.PolylogTerminalSchedule
import FirstPassageLinearTransport.TwoRegimeClock

/-!
# Scalar schedules for shrinking-barrier transport

The switch is linear in `log (M+2)`, while the terminal rank is linear in
`logb 2 (M+2)`.  This file proves the exact finite inequalities behind the
paper's `O(sqrt (M log M))` feasible-time support.  No density estimate is
used here.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Linear-logarithmic high/low switch used by the shrinking barrier. -/
def shrinkingSwitchRank (C : ℝ) (M : ℕ) : ℕ :=
  ⌈C * Real.log ((M : ℝ) + 2)⌉₊

theorem shrinkingSwitchRank_lower (C : ℝ) (M : ℕ) :
    C * Real.log ((M : ℝ) + 2) ≤ (shrinkingSwitchRank C M : ℝ) :=
  Nat.le_ceil _

theorem shrinkingSwitchRank_lt_add_one
    {C : ℝ} (hC : 0 ≤ C) (M : ℕ) :
    (shrinkingSwitchRank C M : ℝ) <
      C * Real.log ((M : ℝ) + 2) + 1 := by
  apply Nat.ceil_lt_add_one
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    linarith
  exact mul_nonneg hC (Real.log_nonneg hx)

theorem shrinkingSwitchRank_pos
    {C : ℝ} (hC : 0 < C) (M : ℕ) :
    0 < shrinkingSwitchRank C M := by
  apply Nat.ceil_pos.mpr
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx : (1 : ℝ) < (M : ℝ) + 2 := by
    linarith
  exact mul_pos hC (Real.log_pos hx)


/-- A linear-log switch is eventually below the source shell. -/
theorem eventually_shrinkingSwitchRank_lt_source
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, shrinkingSwitchRank C M < M := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmallReal := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / (2 * (C + 1)) by
      have : 0 < C + 1 := by linarith
      positivity)
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (5 : ℕ)] with M hsmall hM
  have hx0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx1 : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0] at hsmall
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at hsmall
  have hswitch := shrinkingSwitchRank_lt_add_one hC M
  have hreal : (shrinkingSwitchRank C M : ℝ) < (M : ℝ) := by
    calc
      (shrinkingSwitchRank C M : ℝ) <
          C * Real.log ((M : ℝ) + 2) + 1 := hswitch
      _ ≤ C * ((M : ℝ) + 2) / (2 * (C + 1)) + 1 := by
        have hmul := mul_le_mul_of_nonneg_left hsmall hC
        calc
          C * Real.log ((M : ℝ) + 2) + 1 ≤
              C * (1 / (2 * (C + 1)) * ((M : ℝ) + 2)) + 1 := by
            simpa [add_comm] using add_le_add_right hmul 1
          _ = C * ((M : ℝ) + 2) / (2 * (C + 1)) + 1 := by
            field_simp [ne_of_gt (by positivity : (0 : ℝ) < 2 * (C + 1))]
      _ < (M : ℝ) := by
        have hMR : (5 : ℝ) ≤ M := by exact_mod_cast hM
        have hC1 : 0 < C + 1 := by linarith
        have hfrac : C / (2 * (C + 1)) ≤ (1 / 2 : ℝ) := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))).2
          nlinarith
        calc
          C * ((M : ℝ) + 2) / (2 * (C + 1)) + 1 =
              (C / (2 * (C + 1))) * ((M : ℝ) + 2) + 1 := by ring
          _ ≤ (1 / 2 : ℝ) * ((M : ℝ) + 2) + 1 := by gcongr
          _ < (M : ℝ) := by linarith
  exact_mod_cast hreal

/-- The terminal schedule lies below the linear-log switch exactly when the
switch coefficient strictly exceeds `A / log 2`. -/
theorem eventually_polylogTerminalRank_lt_shrinkingSwitchRank
    {A C : ℝ} (hA : 0 ≤ A)
    (hAC : A / Real.log 2 < C) :
    ∀ᶠ M : ℕ in atTop,
      polylogTerminalRank A M < shrinkingSwitchRank C M := by
  let g := C - A / Real.log 2
  have hg : 0 < g := by dsimp [g]; linarith
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 2))
      atTop atTop := Real.tendsto_log_atTop.comp hxT
  have hlarge : ∀ᶠ M : ℕ in atTop,
      1 < g * Real.log ((M : ℝ) + 2) := by
    have hmul := hlogT.const_mul_atTop hg
    filter_upwards [(tendsto_atTop.1 hmul) 2] with M hM
    linarith
  filter_upwards [hlarge] with M hlarge
  have hterminal := polylogTerminalRank_lt_add_one hA M
  have hswitch := shrinkingSwitchRank_lower C M
  have hrewrite :
      A * Real.logb 2 ((M : ℝ) + 2) =
        (A / Real.log 2) * Real.log ((M : ℝ) + 2) := by
    simp [Real.logb]
    ring
  have hreal :
      (polylogTerminalRank A M : ℝ) <
        (shrinkingSwitchRank C M : ℝ) := by
    calc
      (polylogTerminalRank A M : ℝ) <
          A * Real.logb 2 ((M : ℝ) + 2) + 1 := hterminal
      _ = (A / Real.log 2) * Real.log ((M : ℝ) + 2) + 1 := by
        rw [hrewrite]
      _ < C * Real.log ((M : ℝ) + 2) := by
        dsimp [g] at hlarge
        nlinarith
      _ ≤ (shrinkingSwitchRank C M : ℝ) := hswitch
  exact_mod_cast hreal

/-- Explicit constant in the square-root feasible-time support. -/
def shrinkingTimeSupportConstant
    (P : ShrinkingBarrierRunData) (C : ℝ) : ℝ :=
  2 + 2 / driftGap *
    ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
      (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)))

theorem shrinkingTimeSupportConstant_pos
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C) :
    0 < shrinkingTimeSupportConstant P C := by
  have hsqrt : Real.sqrt (P.rHi : ℝ) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    norm_num
    exact_mod_cast P.pHi.r_lt_one
  have hrLo : (P.rLo : ℝ) < 1 := by exact_mod_cast P.pLo.r_lt_one
  unfold shrinkingTimeSupportConstant
  have hD : 0 < P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hLo : 0 < 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
  have hinner : 0 <
      (P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
        (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)) := by
    apply add_pos
    · exact div_pos hD (sub_pos.mpr hsqrt)
    · exact div_pos (mul_pos hLo (by linarith)) (sub_pos.mpr hrLo)
  have hscale : 0 < 2 / driftGap := div_pos (by norm_num) driftGap_pos
  nlinarith [mul_pos hscale hinner]

private theorem log_le_sqrt_mul
    {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt (x * Real.log x) := by
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hx)).trans (by linarith)
  have hsqrt0 := Real.sqrt_nonneg (x * Real.log x)
  have hsqrtSq := Real.sq_sqrt (mul_nonneg (zero_le_one.trans hx) hlog0)
  have hsq : Real.log x * Real.log x ≤ x * Real.log x :=
    mul_le_mul_of_nonneg_right hlogx hlog0
  nlinarith

/-- Exact potential estimate for the canonical linear-log switch. -/
theorem shrinkingTimePotential_source_le_sqrt
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C)
    {M : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M < M + 1) :
    1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap ≤
      shrinkingTimeSupportConstant P C *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  let x : ℝ := (M : ℝ) + 2
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx1 : 1 ≤ x := by
    dsimp [x]
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
    nlinarith [show 0 ≤ Real.log x from hlog1.trans' zero_le_one]
  have hlogSqrt := log_le_sqrt_mul hx1
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
  have hSbound : (shrinkingSwitchRank C M : ℝ) ≤
      (C + 1) * Real.sqrt (x * Real.log x) := by
    calc
      (shrinkingSwitchRank C M : ℝ) ≤
          C * Real.log x + 1 := hS.le
      _ ≤ C * Real.sqrt (x * Real.log x) +
          Real.sqrt (x * Real.log x) := by gcongr
      _ = (C + 1) * Real.sqrt (x * Real.log x) := by ring
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := by
    apply sub_pos.mpr
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    norm_num
    exact_mod_cast P.pHi.r_lt_one
  have hdLo : 0 < 1 - (P.rLo : ℝ) := sub_pos.mpr P.pLo.r_lt_one
  have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hcoefLo : 0 ≤ 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
  have hpot :
      shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
            Real.sqrt (x * Real.log x) := by
    rw [shrinkingTimePotential, if_pos hSwitch]
    calc
      ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt (((M + 1 : ℕ) : ℝ))) / (1 - Real.sqrt (P.rHi : ℝ)) +
          ((2 * P.etaLo + 3) * (shrinkingSwitchRank C M : ℝ)) /
            (1 - (P.rLo : ℝ)) ≤
        ((P.D + P.tau + 3) * Real.sqrt (x * Real.log x)) /
            (1 - Real.sqrt (P.rHi : ℝ)) +
          ((2 * P.etaLo + 3) * ((C + 1) *
            Real.sqrt (x * Real.log x))) / (1 - (P.rLo : ℝ)) := by
          apply add_le_add
          · apply (div_le_div_iff_of_pos_right hdHi).2
            simpa [x, mul_assoc] using
              (mul_le_mul_of_nonneg_left hsqrtM hcoefHi)
          · apply (div_le_div_iff_of_pos_right hdLo).2
            exact mul_le_mul_of_nonneg_left hSbound hcoefLo
      _ = ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
            Real.sqrt (x * Real.log x) := by ring
  unfold shrinkingTimeSupportConstant
  have hscale0 : 0 ≤ Real.sqrt (x * Real.log x) := Real.sqrt_nonneg _
  calc
    1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap ≤
      1 + 2 * (((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
            Real.sqrt (x * Real.log x)) / driftGap := by
      have hmul := mul_le_mul_of_nonneg_left hpot (by norm_num : (0 : ℝ) ≤ 2)
      have hdiv := div_le_div_of_nonneg_right hmul driftGap_pos.le
      linarith
    _ ≤ (2 + 2 / driftGap *
        ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
          (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)))) *
            Real.sqrt (x * Real.log x) := by
      have hid :
          (2 + 2 / driftGap *
              ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
                (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)))) *
                Real.sqrt (x * Real.log x) -
            (1 + 2 * (((P.D + P.tau + 3) /
                (1 - Real.sqrt (P.rHi : ℝ)) +
                (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ))) *
                  Real.sqrt (x * Real.log x)) / driftGap) =
              2 * Real.sqrt (x * Real.log x) - 1 := by ring
      linarith

/-- Canonical feasible-time sets have square-root-logarithmic cardinality. -/
theorem shrinkingFeasibleTimes_card_lt_sqrt
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C)
    {M q : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M < M + 1) :
    ((shrinkingFeasibleTimes P M (shrinkingSwitchRank C M) q).card : ℝ) <
      (shrinkingTimeSupportConstant P C + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hcard := shrinkingFeasibleTimes_card_le_potential P
    (S := shrinkingSwitchRank C M) (q := q) hM
  have hceil :
      (⌈(1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap)⌉₊ : ℝ) <
      (1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap) + 1 := by
    apply Nat.ceil_lt_add_one
    have hpot0 : 0 ≤ shrinkingTimePotential P M
        (shrinkingSwitchRank C M) (M + 1) := by
      have hsqrt : Real.sqrt (P.rHi : ℝ) < 1 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
        norm_num
        exact_mod_cast P.pHi.r_lt_one
      have hrLo : (P.rLo : ℝ) < 1 := by exact_mod_cast P.pLo.r_lt_one
      have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
        nlinarith [P.D_pos, P.pHi.eta_pos]
      have hcoefLo : 0 ≤ 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
      have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) :=
        Real.log_nonneg (by
          have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith)
      rw [shrinkingTimePotential, if_pos hSwitch]
      apply add_nonneg
      · exact div_nonneg
          (mul_nonneg (mul_nonneg hcoefHi (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)) (sub_pos.mpr hsqrt).le
      · exact div_nonneg
          (mul_nonneg hcoefLo (Nat.cast_nonneg _)) (sub_pos.mpr hrLo).le
    have hquot : 0 ≤
        2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := div_nonneg (mul_nonneg (by norm_num) hpot0) driftGap_pos.le
    linarith
  have hbound := shrinkingTimePotential_source_le_sqrt P hC hM hSwitch
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
  have hcardR :
      ((shrinkingFeasibleTimes P M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := by exact_mod_cast hcard
  calc
    ((shrinkingFeasibleTimes P M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := hcardR
    _ < (1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap) + 1 := hceil
    _ ≤ shrinkingTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) + 1 := by
      linarith
    _ ≤ (shrinkingTimeSupportConstant P C + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
      nlinarith

/-- The linear-log switch contributes only a lower-order term to the
two-regime clock. -/
theorem eventually_shrinkingHorizon_lt_shellClock
    {rHi rLo : ℚ} {C c : ℝ}
    (hrHi1 : rHi < 1) (hrLo1 : rLo < 1)
    (hC : 0 ≤ C)
    (hlead : 1 / (1 - (rHi : ℝ)) < c * Real.log 2) :
    ∀ᶠ M : ℕ in atTop,
      (twoRegimeHorizon rHi rLo (shrinkingSwitchRank C M) M : ℝ) <
        c * (M : ℝ) * Real.log 2 := by
  let dHi : ℝ := 1 - (rHi : ℝ)
  let dLo : ℝ := 1 - (rLo : ℝ)
  have hdHi : 0 < dHi := by
    dsimp [dHi]
    have h : (rHi : ℝ) < 1 := by exact_mod_cast hrHi1
    linarith
  have hdLo : 0 < dLo := by
    dsimp [dLo]
    have h : (rLo : ℝ) < 1 := by exact_mod_cast hrLo1
    linarith
  let g : ℝ := c * Real.log 2 - 1 / dHi
  have hg : 0 < g := by dsimp [g, dHi]; linarith
  let q : ℝ := g * dLo / (4 * (C + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually (Real.isLittleO_log_id_atTop.bound hq)
  have hlinT : Tendsto (fun M : ℕ => (3 * g / 4) * (M : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hlarge : ∀ᶠ M : ℕ in atTop,
      g / 2 + 1 / dLo + 1 < (3 * g / 4) * (M : ℝ) := by
    filter_upwards [(tendsto_atTop.1 hlinT) (g / 2 + 1 / dLo + 2)]
      with M hM
    linarith
  filter_upwards [hsmall, hlarge] with M hsmall hlarge
  have hx0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hx1 : 1 ≤ (M : ℝ) + 2 := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0] at hsmall
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at hsmall
  have hSdiv :
      (shrinkingSwitchRank C M : ℝ) / dLo <
        g / 4 * ((M : ℝ) + 2) + 1 / dLo := by
    have hS := shrinkingSwitchRank_lt_add_one hC M
    have hCd : C / (C + 1) ≤ 1 := by
      apply (div_le_one (by linarith)).2
      linarith
    have hmain : C * Real.log ((M : ℝ) + 2) ≤
        g * dLo / 4 * ((M : ℝ) + 2) := by
      have hmul := mul_le_mul_of_nonneg_left hsmall hC
      calc
        C * Real.log ((M : ℝ) + 2) ≤ C * (q * ((M : ℝ) + 2)) := hmul
        _ = (g * dLo / 4) * (C / (C + 1)) * ((M : ℝ) + 2) := by
          dsimp [q]
          field_simp [ne_of_gt (by linarith : (0 : ℝ) < C + 1)]
        _ ≤ (g * dLo / 4) * 1 * ((M : ℝ) + 2) := by gcongr
        _ = g * dLo / 4 * ((M : ℝ) + 2) := by ring
    calc
      (shrinkingSwitchRank C M : ℝ) / dLo <
          (C * Real.log ((M : ℝ) + 2) + 1) / dLo :=
        (div_lt_div_iff_of_pos_right hdLo).2 hS
      _ ≤ (g * dLo / 4 * ((M : ℝ) + 2) + 1) / dLo := by gcongr
      _ = g / 4 * ((M : ℝ) + 2) + 1 / dLo := by
        field_simp [ne_of_gt hdLo]
  have hbudget0 : 0 ≤ (M : ℝ) / dHi +
      (shrinkingSwitchRank C M : ℝ) / dLo := by positivity
  have hceil :
      (twoRegimeHorizon rHi rLo (shrinkingSwitchRank C M) M : ℝ) <
        (M : ℝ) / dHi + (shrinkingSwitchRank C M : ℝ) / dLo + 1 := by
    simpa [twoRegimeHorizon, dHi, dLo] using Nat.ceil_lt_add_one hbudget0
  have hid : 1 / dHi + g = c * Real.log 2 := by dsimp [g]; ring
  calc
    _ < (M : ℝ) / dHi + (shrinkingSwitchRank C M : ℝ) / dLo + 1 := hceil
    _ < (M : ℝ) / dHi +
        (g / 4 * ((M : ℝ) + 2) + 1 / dLo) + 1 := by linarith
    _ < (1 / dHi + g) * (M : ℝ) := by
      calc
        (M : ℝ) / dHi +
            (g / 4 * ((M : ℝ) + 2) + 1 / dLo) + 1 =
          (1 / dHi) * (M : ℝ) +
            (g / 4 * ((M : ℝ) + 2) + 1 / dLo) + 1 := by ring
        _ < (1 / dHi + g) * (M : ℝ) := by nlinarith
    _ = c * (M : ℝ) * Real.log 2 := by rw [hid]; ring

/-- The complete low-rank local envelope is absorbed by any fixed outer
power margin because the switch has only logarithmic rank. -/
theorem eventually_shrinkingSwitchRank_envelope_le_shellMargin
    {C eta beta : ℝ} (hC : 0 ≤ C) (heta : 0 ≤ eta)
    (hbeta : 0 < beta) :
    ∀ᶠ M : ℕ in atTop,
      (shrinkingSwitchRank C M : ℝ) * (1 + eta) ≤ beta * (M : ℝ) := by
  let q := beta / (2 * (C + 1) * (1 + eta))
  have hq : 0 < q := by dsimp [q]; positivity
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually (Real.isLittleO_log_id_atTop.bound hq)
  have hlarge : ∀ᶠ M : ℕ in atTop,
      2 * (1 + eta) + 2 * beta ≤ beta * (M : ℝ) := by
    have ht : Tendsto (fun M : ℕ => beta * (M : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hbeta
    exact (tendsto_atTop.1 ht) _
  filter_upwards [hsmall, hlarge] with M hsmall hlarge
  have hx0 : 0 ≤ (M : ℝ) + 2 := by positivity
  have hx1 : 1 ≤ (M : ℝ) + 2 := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0] at hsmall
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at hsmall
  have hS := shrinkingSwitchRank_lt_add_one hC M
  have hCfrac : C / (C + 1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have hlogTerm : C * Real.log ((M : ℝ) + 2) * (1 + eta) ≤
      beta / 2 * ((M : ℝ) + 2) := by
    have hmul := mul_le_mul_of_nonneg_left hsmall hC
    calc
      C * Real.log ((M : ℝ) + 2) * (1 + eta) ≤
          C * (q * ((M : ℝ) + 2)) * (1 + eta) := by gcongr
      _ = beta / 2 * (C / (C + 1)) * ((M : ℝ) + 2) := by
        dsimp [q]
        field_simp [ne_of_gt (by linarith : (0 : ℝ) < C + 1),
          ne_of_gt (by linarith : (0 : ℝ) < 1 + eta)]
      _ ≤ beta / 2 * 1 * ((M : ℝ) + 2) := by gcongr
      _ = beta / 2 * ((M : ℝ) + 2) := by ring
  calc
    (shrinkingSwitchRank C M : ℝ) * (1 + eta) ≤
        (C * Real.log ((M : ℝ) + 2) + 1) * (1 + eta) := by gcongr
    _ ≤ beta / 2 * ((M : ℝ) + 2) + (1 + eta) := by
      nlinarith
    _ ≤ beta * (M : ℝ) := by nlinarith

end

end FirstPassageLinearTransport
