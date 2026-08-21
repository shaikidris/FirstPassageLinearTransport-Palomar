/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingHighDensity
import FirstPassageLinearTransport.FixedPolylogParameters

/-!
# Endpoint parameters for time-support compression

The square-root time support spends only one half power of the outer shell.
Accordingly the entropy endpoint is exactly half the older fixed-tolerance
critical exponent.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Critical exponent in the shrinking-time-support theorem. -/
def timeSupportCriticalExponent : ℝ :=
  fixedPolylogCriticalExponent / 2

/-- Exact paper form `1 / (2 (1 - H₂(log₃ 2)))`. -/
theorem timeSupportCriticalExponent_eq_entropy :
    timeSupportCriticalExponent =
      1 / (2 * (1 - binaryEntropyBaseTwo logThreeTwo)) := by
  rw [timeSupportCriticalExponent, fixedPolylogCriticalExponent_eq_entropy]
  have hden : 1 - binaryEntropyBaseTwo logThreeTwo ≠ 0 := by
    intro hz
    have hEq := fixedPolylogCriticalExponent_eq_entropy
    rw [hz] at hEq
    norm_num at hEq
    linarith [fixedPolylogCriticalExponent_gt_one]
  field_simp [hden]

theorem timeSupportCriticalExponent_gt_half :
    1 / 2 < timeSupportCriticalExponent := by
  unfold timeSupportCriticalExponent
  linarith [fixedPolylogCriticalExponent_gt_one]

theorem timeSupportCriticalExponent_pos :
    0 < timeSupportCriticalExponent :=
  lt_trans (by norm_num : (0 : ℝ) < 1 / 2)
    timeSupportCriticalExponent_gt_half

/-- Every exponent above the time-support endpoint admits a low barrier whose
entropy rate beats `log 2 / (2A)`. -/
theorem exists_lowBarrier_of_timeSupportCritical_lt
    {A : ℝ} (hA : timeSupportCriticalExponent < A) :
    ∃ lambda t : ℝ,
      0 ≤ lambda ∧ lambda < 1 ∧
      0 < t ∧ t < driftGap ∧ t < a0 ∧
      Real.log 2 / (2 * A) < adjustableEntropyRate lambda t := by
  have hAhalf : (1 / 2 : ℝ) < A :=
    timeSupportCriticalExponent_gt_half.trans hA
  have hA0 : 0 < A := by linarith
  have hthreshold : Real.log 2 / (2 * A) < firstPassageEndpointRate := by
    have hraw := mul_lt_mul_of_pos_right hA firstPassageEndpointRate_pos
    have hidentity :
        timeSupportCriticalExponent * firstPassageEndpointRate =
          Real.log 2 / 2 := by
      unfold timeSupportCriticalExponent fixedPolylogCriticalExponent
      field_simp [ne_of_gt firstPassageEndpointRate_pos]
    rw [hidentity] at hraw
    apply (div_lt_iff₀ (mul_pos (by norm_num) hA0)).2
    nlinarith
  have hEventually : ∀ᶠ n : ℕ in atTop,
      Real.log 2 / (2 * A) <
        adjustableEntropyRate (endpointLambda n) (endpointTolerance n) :=
    tendsto_endpointEntropyRate.eventually (Ioi_mem_nhds hthreshold)
  obtain ⟨n, hn⟩ := hEventually.exists
  refine ⟨endpointLambda n, endpointTolerance n,
    (endpointLambda_pos n).le, endpointLambda_lt_one n,
    endpointTolerance_pos n, endpointTolerance_lt_driftGap n,
    (endpointTolerance_lt_driftGap n).trans driftGap_lt_a0, hn⟩

/-- Strict retained low rate and positive shell exceptional exponent. -/
theorem exists_lowBarrier_rate_margin_of_timeSupportCritical_lt
    {A : ℝ} (hA : timeSupportCriticalExponent < A) :
    ∃ lambda t b kappa : ℝ,
      0 ≤ lambda ∧ lambda < 1 ∧
      0 < t ∧ t < driftGap ∧ t < a0 ∧
      0 < b ∧ b < adjustableEntropyRate lambda t ∧
      b < Real.log 2 ∧
      0 < kappa ∧ kappa < A * b / Real.log 2 - 1 / 2 := by
  obtain ⟨lambda, t, hlambda0, hlambda1, ht0, htGap, htA, hrate⟩ :=
    exists_lowBarrier_of_timeSupportCritical_lt hA
  have hAhalf : (1 / 2 : ℝ) < A :=
    timeSupportCriticalExponent_gt_half.trans hA
  have hA0 : 0 < A := by linarith
  let threshold := Real.log 2 / (2 * A)
  let upper := min (adjustableEntropyRate lambda t) (Real.log 2)
  have hthreshold0 : 0 < threshold := by
    dsimp [threshold]
    exact div_pos (Real.log_pos (by norm_num)) (mul_pos (by norm_num) hA0)
  have hthresholdUpper : threshold < upper := by
    rw [lt_min_iff]
    refine ⟨by simpa [threshold] using hrate, ?_⟩
    dsimp [threshold]
    have htwoA : 1 < 2 * A := by linarith
    exact div_lt_self (Real.log_pos (by norm_num)) htwoA
  let b := (threshold + upper) / 2
  have hbLower : threshold < b := by dsimp [b]; linarith
  have hbUpper : b < upper := by dsimp [b]; linarith
  have hb0 : 0 < b := hthreshold0.trans hbLower
  have hbRate : b < adjustableEntropyRate lambda t :=
    hbUpper.trans_le (min_le_left _ _)
  have hbLog : b < Real.log 2 := hbUpper.trans_le (min_le_right _ _)
  have hmargin : 0 < A * b / Real.log 2 - 1 / 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hAb : Real.log 2 / 2 < A * b := by
      have hmul := mul_lt_mul_of_pos_left hbLower hA0
      dsimp [threshold] at hmul
      have htwoA : (2 * A : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num) hA0)
      have hid : A * (Real.log 2 / (2 * A)) = Real.log 2 / 2 := by
        field_simp [htwoA]
      rw [hid] at hmul
      exact hmul
    rw [sub_pos]
    apply (lt_div_iff₀ hlog2).2
    nlinarith
  let kappa := (A * b / Real.log 2 - 1 / 2) / 2
  have hkappa0 : 0 < kappa := by dsimp [kappa]; linarith
  have hkappa : kappa < A * b / Real.log 2 - 1 / 2 := by
    dsimp [kappa]
    linarith
  exact ⟨lambda, t, b, kappa,
    hlambda0, hlambda1, ht0, htGap, htA, hb0, hbRate, hbLog,
    hkappa0, hkappa⟩

/-- Complete parameter package for the shrinking-time-support theorem. -/
structure ShrinkingPolylogParameterPackage (A c beta : ℝ) where
  run : ShrinkingBarrierRunData
  lambdaLo : ℝ
  bLo : ℝ
  cDyadic : ℝ
  Cswitch : ℝ
  kappa : ℝ
  lambdaLo_nonneg : 0 ≤ lambdaLo
  lambdaLo_lt_one : lambdaLo < 1
  bLo_pos : 0 < bLo
  bLo_lt_rate : bLo < adjustableEntropyRate lambdaLo run.etaLo
  cDyadic_pos : 0 < cDyadic
  cDyadic_lt_logTwo : cDyadic < Real.log 2
  Cswitch_pos : 0 < Cswitch
  terminal_below_switch : A / Real.log 2 < Cswitch
  high_cap : run.D / Real.sqrt Cswitch ≤ run.tau
  high_rate_margin : kappa <
    min (Cswitch * Real.log 2) (maximalBarrierC0 * run.D ^ 2) - 5 / 2
  low_rate_margin : kappa <
    A * min bLo cDyadic / Real.log 2 - 1 / 2
  clock_pressure : 1 / (1 - (run.rHi : ℝ)) < c * Real.log 2
  tau_lt_beta : run.tau < beta
  kappa_pos : 0 < kappa

/-- Every exponent above the half-loss endpoint admits one complete
shrinking-barrier parameter package. -/
theorem exists_shrinkingPolylogParameterPackage
    {A c beta : ℝ}
    (hA : timeSupportCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta) :
    Nonempty (ShrinkingPolylogParameterPackage A c beta) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := fixedPolylogClockCritical_pos.trans hc
  have hcLog : 0 < c * Real.log 2 := mul_pos hc0 hlog2
  have hgapLog : 0 < driftGap * Real.log 2 :=
    mul_pos driftGap_pos hlog2
  have hclockCross : 1 < c * (driftGap * Real.log 2) := by
    have := (div_lt_iff₀ hgapLog).1 hc
    simpa [fixedPolylogClockCritical] using this
  have hInvGap : 1 / (c * Real.log 2) < driftGap := by
    rw [div_lt_iff₀ hcLog]
    nlinarith [hclockCross]
  have hHiInterval : a0 < 1 - 1 / (c * Real.log 2) := by
    unfold driftGap at hInvGap
    linarith
  obtain ⟨rHi, hrHiLower, hrHiUpper⟩ := exists_rat_btwn hHiInterval
  have hrHiOne : (rHi : ℝ) < 1 := by
    have hinv0 : 0 < 1 / (c * Real.log 2) := by positivity
    linarith
  have hrHiPos : (0 : ℝ) < rHi := a0_pos.trans hrHiLower
  have hclock : 1 / (1 - (rHi : ℝ)) < c * Real.log 2 := by
    have hgap : 1 / (c * Real.log 2) < 1 - (rHi : ℝ) := by linarith
    have hden : 0 < 1 - (rHi : ℝ) := sub_pos.mpr hrHiOne
    rw [div_lt_iff₀ hden]
    have hmul := (div_lt_iff₀ hcLog).1 hgap
    nlinarith
  let dHi : ℝ := min ((rHi : ℝ) - a0) (min beta a0)
  have hdHi : 0 < dHi := by
    rw [lt_min_iff, lt_min_iff]
    exact ⟨sub_pos.mpr hrHiLower, hbeta, a0_pos⟩
  let tau := dHi / 2
  have htau0 : 0 < tau := by dsimp [tau]; positivity
  have htauD : tau < dHi := by dsimp [tau]; linarith
  have htauGap : tau < (rHi : ℝ) - a0 :=
    htauD.trans_le (min_le_left _ _)
  have htauBeta : tau < beta :=
    htauD.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htauA : tau < a0 :=
    htauD.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let pHi := Classical.choice
    (exists_stageSetup hrHiLower hrHiOne htau0 htauGap)
  obtain ⟨lambdaLo, etaLo, bLo, kappa,
      hlambdaLo0, hlambdaLo1, hetaLo0, hetaLoGap, hetaLoA,
      hbLo0, hbLoRate, hbLoLog, hkappa0, hkappa⟩ :=
    exists_lowBarrier_rate_margin_of_timeSupportCritical_lt hA
  have hLoInterval : a0 + etaLo < 1 := by
    unfold driftGap at hetaLoGap
    linarith
  obtain ⟨rLo, hrLoLower, hrLoUpper⟩ := exists_rat_btwn hLoInterval
  have hrLoA : a0 < (rLo : ℝ) := by linarith [hetaLo0]
  have hetaLoRankGap : etaLo < (rLo : ℝ) - a0 := by linarith
  have hrLoPos : (0 : ℝ) < rLo := a0_pos.trans hrLoA
  let pLo := Classical.choice
    (exists_stageSetup hrLoA hrLoUpper hetaLo0 hetaLoRankGap)
  let rStar : ℚ := min rHi rLo
  have hrStar0 : (0 : ℚ) < rStar := by
    dsimp [rStar]
    rw [lt_min_iff]
    exact ⟨by exact_mod_cast hrHiPos, by exact_mod_cast hrLoPos⟩
  let target : ℝ := |kappa| + 4
  have htarget0 : 0 < target := by dsimp [target]; positivity
  have htargetK : kappa + 5 / 2 < target := by
    dsimp [target]
    linarith [le_abs_self kappa]
  have hc00 : 0 < maximalBarrierC0 := maximalBarrierC0_pos
  let D := target / maximalBarrierC0 + 1
  have hD1 : 1 < D := by
    dsimp [D]
    linarith [div_pos htarget0 hc00]
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hDRate : target < maximalBarrierC0 * D ^ 2 := by
    have hDsq : D < D ^ 2 := by nlinarith
    have hmul : maximalBarrierC0 * D < maximalBarrierC0 * D ^ 2 :=
      mul_lt_mul_of_pos_left hDsq hc00
    have heq : maximalBarrierC0 * D = target + maximalBarrierC0 := by
      dsimp [D]
      field_simp [ne_of_gt hc00]
    rw [heq] at hmul
    linarith
  let Cswitch := (D / tau) ^ 2 + target / Real.log 2 +
    A / Real.log 2 + 3
  have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA
  have hC0 : 0 < Cswitch := by
    dsimp [Cswitch]
    have h1 : 0 ≤ (D / tau) ^ 2 := sq_nonneg _
    have h2 : 0 < target / Real.log 2 := div_pos htarget0 hlog2
    have h3 : 0 < A / Real.log 2 := div_pos hA0 hlog2
    positivity
  have hAC : A / Real.log 2 < Cswitch := by
    dsimp [Cswitch]
    have h1 : 0 ≤ (D / tau) ^ 2 := sq_nonneg _
    have h2 : 0 < target / Real.log 2 := div_pos htarget0 hlog2
    linarith
  have hCRate : target < Cswitch * Real.log 2 := by
    have hCpart : target / Real.log 2 < Cswitch := by
      dsimp [Cswitch]
      have h1 : 0 ≤ (D / tau) ^ 2 := sq_nonneg _
      have h3 : 0 < A / Real.log 2 := div_pos hA0 hlog2
      linarith
    exact (div_lt_iff₀ hlog2).1 hCpart
  have hcap : D / Real.sqrt Cswitch ≤ tau := by
    have hsqrtC : 0 < Real.sqrt Cswitch := Real.sqrt_pos.2 hC0
    have hsq : (D / tau) ^ 2 < Cswitch := by
      dsimp [Cswitch]
      have h2 : 0 < target / Real.log 2 := div_pos htarget0 hlog2
      have h3 : 0 < A / Real.log 2 := div_pos hA0 hlog2
      linarith
    have hroot : D / tau < Real.sqrt Cswitch := by
      have hleft : 0 ≤ D / tau := (div_pos hD0 htau0).le
      exact (Real.lt_sqrt hleft).2 hsq
    apply (div_le_iff₀ hsqrtC).2
    have hmul := mul_lt_mul_of_pos_left hroot htau0
    have heq : tau * (D / tau) = D := by
      field_simp [ne_of_gt htau0]
    rw [heq] at hmul
    exact hmul.le
  let run : ShrinkingBarrierRunData := {
    rHi := rHi
    rLo := rLo
    rStar := rStar
    tau := tau
    etaLo := etaLo
    D := D
    pHi := pHi
    pLo := pLo
    D_pos := hD0
    tau_lt_a0 := htauA
    etaLo_lt_a0 := hetaLoA
    rStar_eq := rfl
    rStar_pos := hrStar0 }
  have hHigh : kappa <
      min (Cswitch * Real.log 2) (maximalBarrierC0 * D ^ 2) - 5 / 2 := by
    rw [lt_sub_iff_add_lt, lt_min_iff]
    exact ⟨htargetK.trans hCRate, htargetK.trans hDRate⟩
  exact ⟨{
    run := run
    lambdaLo := lambdaLo
    bLo := bLo
    cDyadic := bLo
    Cswitch := Cswitch
    kappa := kappa
    lambdaLo_nonneg := hlambdaLo0
    lambdaLo_lt_one := hlambdaLo1
    bLo_pos := hbLo0
    bLo_lt_rate := by simpa [run] using hbLoRate
    cDyadic_pos := hbLo0
    cDyadic_lt_logTwo := hbLoLog
    Cswitch_pos := hC0
    terminal_below_switch := hAC
    high_cap := by simpa [run] using hcap
    high_rate_margin := by simpa [run] using hHigh
    low_rate_margin := by simpa using hkappa
    clock_pressure := by simpa [run] using hclock
    tau_lt_beta := by simpa [run] using htauBeta
    kappa_pos := hkappa0 }⟩

end

end FirstPassageLinearTransport
