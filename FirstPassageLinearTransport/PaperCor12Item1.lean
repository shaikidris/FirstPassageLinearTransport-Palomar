/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingNaturalDensityDescent
import FirstPassageLinearTransport.FiniteStartup

/-!
# Paper Corollary 1.2(1) packaging

Isolated submission module, **not** imported by `Main.lean`. It packages the
already-proved shrinking-time-support theorem at the exact strength of
preprint Corollary 1.2, item 1:

* separate landing constant `C_tar` and exceptional constant `C_exc`;
* every exceptional exponent `0 < γ < κ_*(A - A_FP)`.

It does not add the moving schedule, the critical log-log scales, or the
stretched-logarithmic companion.
-/

namespace FirstPassageLinearTransport

open Filter Asymptotics
open scoped Real Topology

noncomputable section

/-- Paper `κ_* = 1 - H₂(log₃ 2)`. -/
def paperKappaStar : ℝ :=
  1 - binaryEntropyBaseTwo logThreeTwo

/-- Paper exceptional-rate ceiling `κ_*(A - A_FP)` for a fixed exponent `A`. -/
def paperExceptionalExponentCeiling (A : ℝ) : ℝ :=
  paperKappaStar * (A - timeSupportCriticalExponent)

theorem paperKappaStar_eq_endpointRate :
    paperKappaStar = firstPassageEndpointRate / Real.log 2 := by
  unfold paperKappaStar firstPassageEndpointRate binaryBarrierRate
    binaryEntropyBaseTwo
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [endpoint_probability_eq_logThreeTwo]
  field_simp [hlog2]

theorem paperKappaStar_pos : 0 < paperKappaStar := by
  rw [paperKappaStar_eq_endpointRate]
  exact div_pos firstPassageEndpointRate_pos (Real.log_pos (by norm_num))

theorem paperExceptionalExponentCeiling_eq_entropy (A : ℝ) :
    paperExceptionalExponentCeiling A =
      A * firstPassageEndpointRate / Real.log 2 - 1 / 2 := by
  unfold paperExceptionalExponentCeiling
  have hstar : paperKappaStar * timeSupportCriticalExponent = 1 / 2 := by
    rw [paperKappaStar_eq_endpointRate, timeSupportCriticalExponent,
      fixedPolylogCriticalExponent]
    have hrate : firstPassageEndpointRate ≠ 0 :=
      ne_of_gt firstPassageEndpointRate_pos
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hrate, hlog2]
  rw [mul_sub, hstar, paperKappaStar_eq_endpointRate]
  ring

/-- Any exceptional exponent strictly below the paper entropy margin is
realized as a shrinking low-barrier rate. -/
theorem exists_lowBarrier_rate_margin_gt
    {A gamma : ℝ}
    (hA : timeSupportCriticalExponent < A)
    (hgamma0 : 0 < gamma)
    (hgamma : gamma <
        A * firstPassageEndpointRate / Real.log 2 - 1 / 2) :
    ∃ lambda t b kappa : ℝ,
      0 ≤ lambda ∧ lambda < 1 ∧
      0 < t ∧ t < driftGap ∧ t < a0 ∧
      0 < b ∧ b < adjustableEntropyRate lambda t ∧
      b < Real.log 2 ∧
      0 < kappa ∧ gamma < kappa ∧
      kappa < A * b / Real.log 2 - 1 / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA
  let bLower := (gamma + 1 / 2) * Real.log 2 / A
  have hbLower0 : 0 < bLower := by
    dsimp [bLower]
    have hhalf : 0 < gamma + 1 / 2 := by linarith
    exact div_pos (mul_pos hhalf hlog2) hA0
  have hbLower_lt_rate : bLower < firstPassageEndpointRate := by
    dsimp [bLower]
    have hsum : gamma + 1 / 2 <
        A * firstPassageEndpointRate / Real.log 2 := by linarith
    have hmul : (gamma + 1 / 2) * Real.log 2 <
        A * firstPassageEndpointRate := (lt_div_iff₀ hlog2).1 hsum
    exact (div_lt_iff₀ hA0).2 (by simpa [mul_comm] using hmul)
  have hbLower_lt_log : bLower < Real.log 2 := by
    dsimp [bLower]
    have hrate_lt := firstPassageEndpointRate_lt_logTwo
    have hquot : firstPassageEndpointRate / Real.log 2 < 1 :=
      (div_lt_one hlog2).2 hrate_lt
    have hA_rate : A * firstPassageEndpointRate / Real.log 2 < A := by
      calc
        A * firstPassageEndpointRate / Real.log 2
            = A * (firstPassageEndpointRate / Real.log 2) := by ring
        _ < A * 1 := mul_lt_mul_of_pos_left hquot hA0
        _ = A := by ring
    have hsum : gamma + 1 / 2 < A :=
      lt_trans (by linarith : gamma + 1 / 2 <
          A * firstPassageEndpointRate / Real.log 2) hA_rate
    have hmul : (gamma + 1 / 2) * Real.log 2 < A * Real.log 2 :=
      mul_lt_mul_of_pos_right hsum hlog2
    exact (div_lt_iff₀ hA0).2 (by simpa [mul_comm] using hmul)
  have hEventually : ∀ᶠ n : ℕ in atTop,
      bLower < adjustableEntropyRate (endpointLambda n) (endpointTolerance n) :=
    tendsto_endpointEntropyRate.eventually (Ioi_mem_nhds hbLower_lt_rate)
  obtain ⟨n, hn⟩ := hEventually.exists
  let lambda := endpointLambda n
  let t := endpointTolerance n
  let rate := adjustableEntropyRate lambda t
  let upper := min rate (Real.log 2)
  have hthresholdUpper : bLower < upper := by
    rw [lt_min_iff]
    exact ⟨hn, hbLower_lt_log⟩
  let b := (bLower + upper) / 2
  have hbLower_lt_b : bLower < b := by dsimp [b]; linarith
  have hb_lt_upper : b < upper := by dsimp [b]; linarith
  have hb0 : 0 < b := hbLower0.trans hbLower_lt_b
  have hbRate : b < rate := hb_lt_upper.trans_le (min_le_left _ _)
  have hbLog : b < Real.log 2 := hb_lt_upper.trans_le (min_le_right _ _)
  have hmargin : gamma < A * b / Real.log 2 - 1 / 2 := by
    have hb : bLower < b := hbLower_lt_b
    have hAb : (gamma + 1 / 2) * Real.log 2 < A * b := by
      have hmul := mul_lt_mul_of_pos_left hb hA0
      dsimp [bLower] at hmul
      have hid : A * ((gamma + 1 / 2) * Real.log 2 / A) =
          (gamma + 1 / 2) * Real.log 2 := by
        field_simp [ne_of_gt hA0]
      rw [hid] at hmul
      exact hmul
    have hdiv : gamma + 1 / 2 < A * b / Real.log 2 :=
      (lt_div_iff₀ hlog2).2 hAb
    linarith
  let kappa := (gamma + (A * b / Real.log 2 - 1 / 2)) / 2
  have hkappa0 : 0 < kappa := by
    dsimp [kappa]
    linarith
  have hkappa_gt : gamma < kappa := by
    dsimp [kappa]
    linarith
  have hkappa : kappa < A * b / Real.log 2 - 1 / 2 := by
    dsimp [kappa]
    linarith
  exact ⟨lambda, t, b, kappa,
    (endpointLambda_pos n).le, endpointLambda_lt_one n,
    endpointTolerance_pos n, endpointTolerance_lt_driftGap n,
    (endpointTolerance_lt_driftGap n).trans driftGap_lt_a0,
    hb0, hbRate, hbLog, hkappa0, hkappa_gt, hkappa⟩

/-- The shrinking-barrier package can be chosen so that its exceptional
exponent strictly exceeds any `gamma` below the paper entropy margin. -/
theorem exists_shrinkingPolylogParameterPackage_gt
    {A c beta gamma : ℝ}
    (hA : timeSupportCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hgamma0 : 0 < gamma)
    (hgamma : gamma <
        A * firstPassageEndpointRate / Real.log 2 - 1 / 2) :
    ∃ P : ShrinkingPolylogParameterPackage A c beta, gamma < P.kappa := by
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
      hbLo0, hbLoRate, hbLoLog, hkappa0, hkappa_gt, hkappa⟩ :=
    exists_lowBarrier_rate_margin_gt hA hgamma0 hgamma
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
  refine ⟨{
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
    kappa_pos := hkappa0 }, ?_⟩
  simpa using hkappa_gt

/-- `(log X)^γ / X → 0` for every real `γ`. -/
theorem tendsto_log_rpow_div_nat (gamma : ℝ) :
    Tendsto (fun X : ℕ => (Real.log X) ^ gamma / (X : ℝ)) atTop (nhds 0) := by
  have h : (fun x : ℝ => Real.log x ^ gamma) =o[atTop] fun x => x := by
    simpa using (isLittleO_log_rpow_rpow_atTop (s := 1) gamma (by norm_num))
  exact h.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- A stronger polylogarithmic profile plus a finite additive error implies
every weaker positive exponent, without reducing the exponent to `min κ 1`. -/
theorem eventually_badCount_add_le_weaker_polylog
    {S : Set ℕ} {C kappa gamma : ℝ} {K : ℕ}
    (hC : 0 ≤ C) (hlt : gamma < kappa)
    (hcount : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) ≤ C * X * (Real.log X) ^ (-kappa)) :
    ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) + K ≤
        (C + K + 1) * X * (Real.log X) ^ (-gamma) := by
  have hpos : 0 < kappa - gamma := sub_pos.mpr hlt
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hCterm : Tendsto
      (fun X : ℕ => C * (Real.log X) ^ (gamma - kappa)) atTop (nhds 0) := by
    have hneg : gamma - kappa = -(kappa - gamma) := by ring
    rw [hneg]
    have hconst : Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    simpa only [Function.comp_apply, mul_zero] using
      hconst.mul ((tendsto_rpow_neg_atTop hpos).comp hlog)
  have hKterm : Tendsto
      (fun X : ℕ => (K : ℝ) * ((Real.log X) ^ gamma / (X : ℝ)))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (K : ℝ)) atTop (nhds (K : ℝ)) :=
      tendsto_const_nhds
    simpa only [mul_div_assoc, mul_zero] using
      hconst.mul (tendsto_log_rpow_div_nat gamma)
  have hCsmall : ∀ᶠ X : ℕ in atTop,
      C * (Real.log X) ^ (gamma - kappa) ≤ 1 / 2 := by
    have ht := hCterm.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [ht] with X hX
    exact hX.le
  have hKsmall : ∀ᶠ X : ℕ in atTop,
      (K : ℝ) ≤ (1 / 2) * X * (Real.log X) ^ (-gamma) := by
    have ht : Tendsto
        (fun X : ℕ => (K : ℝ) * (Real.log X) ^ gamma / (X : ℝ))
      atTop (nhds 0) := by
        simpa only [mul_div_assoc] using hKterm
    have hhalf : ∀ᶠ X : ℕ in atTop,
        (K : ℝ) * (Real.log X) ^ gamma / (X : ℝ) < 1 / 2 :=
      ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hhalf, eventually_ge_atTop (8 : ℕ)] with X hhalf hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
        (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
      norm_num only [Nat.cast_ofNat]
      nlinarith
    have hXreal : (8 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hlog0 : 0 ≤ Real.log X :=
      zero_le_one.trans (hlog8.trans (Real.log_le_log (by norm_num) hXreal))
    have hpowpos : 0 < (Real.log X) ^ gamma :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one
        (hlog8.trans (Real.log_le_log (by norm_num) hXreal))) _
    have hmul := (div_lt_iff₀ hXpos).1 hhalf
    have : (K : ℝ) * (Real.log X) ^ gamma < (1 / 2) * X := hmul
    have hinv : (K : ℝ) < (1 / 2) * X / (Real.log X) ^ gamma :=
      (lt_div_iff₀ hpowpos).2 (by linarith)
    have heq : (1 / 2) * X / (Real.log X) ^ gamma =
        (1 / 2) * X * (Real.log X) ^ (-gamma) := by
      rw [Real.rpow_neg hlog0, div_eq_mul_inv]
    exact hinv.le.trans_eq heq
  filter_upwards [hcount, hCsmall, hKsmall, eventually_ge_atTop (8 : ℕ)]
      with X hcount hCsmall hKsmall hX
  have hXreal : (8 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hlog1 : 1 ≤ Real.log X :=
    hlog8.trans (Real.log_le_log (by norm_num) hXreal)
  have hprofile : C * X * (Real.log X) ^ (-kappa) ≤
      (1 / 2) * X * (Real.log X) ^ (-gamma) := by
    have hpow : (Real.log X) ^ (-kappa) =
        (Real.log X) ^ (gamma - kappa) * (Real.log X) ^ (-gamma) := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hlog1)]
      ring_nf
    rw [hpow, mul_left_comm, mul_assoc, mul_assoc]
    have hnn : 0 ≤ (X : ℝ) * (Real.log X) ^ (-gamma) := by positivity
    have : C * (Real.log X) ^ (gamma - kappa) *
        (X * (Real.log X) ^ (-gamma)) ≤
        (1 / 2) * (X * (Real.log X) ^ (-gamma)) :=
      mul_le_mul_of_nonneg_right hCsmall hnn
    linarith
  have hsum : (badCount S X : ℝ) + K ≤
      C * X * (Real.log X) ^ (-kappa) + (K : ℝ) :=
    add_le_add hcount (le_refl (K : ℝ))
  have hbound : C * X * (Real.log X) ^ (-kappa) + (K : ℝ) ≤
      X * (Real.log X) ^ (-gamma) := by
    linarith [hprofile, hKsmall]
  have hcoef : (X : ℝ) * (Real.log X) ^ (-gamma) ≤
      (C + K + 1) * X * (Real.log X) ^ (-gamma) := by
    have hnn : 0 ≤ (X : ℝ) * (Real.log X) ^ (-gamma) := by positivity
    have h1 : (1 : ℝ) ≤ C + K + 1 := by
      have : (0 : ℝ) ≤ C := hC
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      linarith
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right h1 hnn
  linarith

/-- Paper Corollary 1.2(1): fixed exponent above `A_FP`, every clock above
`c_*`, every height `β > 0`, and every exceptional exponent strictly below
the entropy margin `κ_*(A - A_FP)`, with separate landing and exceptional
constants. -/
theorem paper_cor12_item1_fixed_polylog
    {A c beta gamma : ℝ}
    (hA : 1 / (2 * (1 - binaryEntropyBaseTwo logThreeTwo)) < A)
    (hc : 2 / Real.log (4 / 3) < c)
    (hbeta : 0 < beta)
    (hgamma : 0 < gamma)
    (hgamma_lt : gamma < paperExceptionalExponentCeiling A) :
    ∃ Ctar Cexc : ℝ,
      0 < Ctar ∧ 0 < Cexc ∧
      NaturalDensityOne
        {n : ℕ | ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) ≤ Ctar * (Real.log n) ^ A ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)} ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount
          {n : ℕ | ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) ≤ Ctar * (Real.log n) ^ A ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)} X : ℝ) ≤
          Cexc * X * (Real.log X) ^ (-gamma)) := by
  have hA' : timeSupportCriticalExponent < A := by
    simpa [timeSupportCriticalExponent_eq_entropy] using hA
  have hc' : fixedPolylogClockCritical < c := by
    simpa [fixedPolylogClockCritical_eq_paper] using hc
  have hceil : gamma <
      A * firstPassageEndpointRate / Real.log 2 - 1 / 2 := by
    simpa [paperExceptionalExponentCeiling_eq_entropy A] using hgamma_lt
  obtain ⟨P, hPgamma⟩ :=
    exists_shrinkingPolylogParameterPackage_gt hA' hc' hbeta hgamma hceil
  let Ctar := fixedPolylogTargetConstant A
  have hCtar : 0 < Ctar := by
    dsimp [Ctar, fixedPolylogTargetConstant]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA'
    positivity
  let S := assembleDyadic (shrinkingPolylogGood P.run A P.Cswitch)
  have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA'
  have hc0 : 0 < c := fixedPolylogClockCritical_pos.trans hc'
  have hCountS := P.eventually_badCount hA0
  have hLanding :=
    eventually_assembleDyadic_shrinkingPolylogGood_has_landing
      hA0 hc0 hbeta P
  let W : Set ℕ :=
    {n : ℕ | ∃ k : ℕ,
      (k : ℝ) < c * Real.log n ∧
      (orbit k n : ℝ) ≤ Ctar * (Real.log n) ^ A ∧
      ∀ j : ℕ, j ≤ k →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)}
  have hSW : ∀ᶠ n : ℕ in atTop, n ∈ S → n ∈ W := by
    filter_upwards [hLanding] with n hLanding hnS
    obtain ⟨k, hk, htarget, hceiling⟩ := hLanding hnS
    exact ⟨k, hk, by simpa [Ctar] using htarget.le, hceiling⟩
  rcases (eventually_atTop.1 hSW) with ⟨N, hN⟩
  let C0 := shrinkingExceptionalConstant P
  have hC0 : 0 < C0 := shrinkingExceptionalConstant_pos P
  have hCountT :
      ∀ᶠ X : ℕ in atTop,
        (badCount W X : ℝ) + 0 ≤
          (C0 + N + 1) * X * (Real.log X) ^ (-gamma) := by
    have hraw : ∀ᶠ X : ℕ in atTop,
        (badCount W X : ℝ) ≤ (badCount S X : ℝ) + N := by
      filter_upwards with X
      exact_mod_cast
        (badCount_le_add_of_tail_subset S W N X fun n hn hnS => hN n hn hnS)
    have habs := eventually_badCount_add_le_weaker_polylog
      (K := N) hC0.le hPgamma hCountS
    filter_upwards [hraw, habs] with X hraw habs
    linarith
  let Cexc := C0 + N + 1
  have hCexc : 0 < Cexc := by
    dsimp [Cexc]
    positivity
  have hWcount : ∀ᶠ X : ℕ in atTop,
      (badCount W X : ℝ) ≤ Cexc * X * (Real.log X) ^ (-gamma) := by
    filter_upwards [hCountT] with X hCountT
    simpa [Cexc] using hCountT
  have hWdense : NaturalDensityOne W :=
    naturalDensityOne_of_eventually_badCount_le_polylog
      hCexc.le hgamma hWcount
  refine ⟨Ctar, Cexc, hCtar, hCexc, ?_, ?_⟩
  · simpa [W, Ctar] using hWdense
  · simpa [W, Ctar, Cexc] using hWcount

end

end FirstPassageLinearTransport
