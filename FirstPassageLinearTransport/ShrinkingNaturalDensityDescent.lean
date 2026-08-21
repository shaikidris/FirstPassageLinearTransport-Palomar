/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingOrbitCeiling
import FirstPassageLinearTransport.FiniteStartup
import FirstPassageLinearTransport.PolylogTarget

/-!
# Fixed-polylogarithmic natural-density descent with compressed time support
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

def shrinkingExceptionalConstant
    {A c beta : ℝ} (P : ShrinkingPolylogParameterPackage A c beta) : ℝ :=
  let C := shrinkingPolylogProfileConstant P.run P.Cswitch
    (adjustableEntropyRate P.lambdaLo P.run.etaLo) P.bLo P.cDyadic
  (1 + 2 * max C 0) * (2 * Real.log 2) ^ P.kappa

theorem shrinkingExceptionalConstant_pos
    {A c beta : ℝ} (P : ShrinkingPolylogParameterPackage A c beta) :
    0 < shrinkingExceptionalConstant P := by
  unfold shrinkingExceptionalConstant
  have hbase : 0 < 2 * Real.log 2 := by positivity
  positivity

theorem ShrinkingPolylogParameterPackage.eventually_shellDensity
    {A c beta : ℝ} (P : ShrinkingPolylogParameterPackage A c beta)
    (hA : 0 < A) :
    ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio
          (shrinkingPolylogGood P.run A P.Cswitch M) M ≤
        shrinkingPolylogProfileConstant P.run P.Cswitch
            (adjustableEntropyRate P.lambdaLo P.run.etaLo)
            P.bLo P.cDyadic *
          (((M : ℝ) + 2) ^ (-P.kappa)) := by
  have hraw := eventually_shrinkingFailureEnvelope_density_polylog_le
    P.run hA P.Cswitch_pos P.terminal_below_switch P.high_cap
    P.lambdaLo_nonneg P.lambdaLo_lt_one P.bLo_pos P.bLo_lt_rate
    P.cDyadic_pos P.cDyadic_lt_logTwo
    P.high_rate_margin P.low_rate_margin
  filter_upwards [hraw] with M hraw
  rw [shellExceptionalRatio, shellBad_shrinkingPolylogGood]
  exact hraw

theorem ShrinkingPolylogParameterPackage.eventually_badCount
    {A c beta : ℝ} (P : ShrinkingPolylogParameterPackage A c beta)
    (hA : 0 < A) :
    ∀ᶠ X : ℕ in atTop,
      (badCount
        (assembleDyadic (shrinkingPolylogGood P.run A P.Cswitch)) X : ℝ) ≤
        shrinkingExceptionalConstant P * X *
          (Real.log X) ^ (-P.kappa) := by
  let C := shrinkingPolylogProfileConstant P.run P.Cswitch
    (adjustableEntropyRate P.lambdaLo P.run.etaLo) P.bLo P.cDyadic
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hShell := P.eventually_shellDensity hA
  have hShellB : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (shrinkingPolylogGood P.run A P.Cswitch M) M ≤
        B * (((M : ℝ) + 2) ^ (-P.kappa)) := by
    filter_upwards [hShell] with M hShell
    exact hShell.trans (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (by positivity) _))
  rw [eventually_atTop] at hShellB
  obtain ⟨M₀, hM₀⟩ := hShellB
  have hPrefix := eventually_badCount_assembleDyadic_le_polylog_profile
    (shrinkingPolylogGood P.run A P.Cswitch) M₀ B P.kappa
    hB P.kappa_pos.le hM₀
  have hScale := eventually_halfNatLog_profile_le_natLog P.kappa_pos.le
  filter_upwards [hPrefix, hScale] with X hPrefix hScale
  have hCoeff : 0 ≤ (1 + 2 * B) * (X : ℝ) := by positivity
  calc
    _ ≤ (1 + 2 * B) * X *
        ((((Nat.log 2 X) / 2 : ℕ) : ℝ) + 2) ^ (-P.kappa) := hPrefix
    _ ≤ (1 + 2 * B) * X *
        ((2 * Real.log 2) ^ P.kappa * (Real.log X) ^ (-P.kappa)) :=
      mul_le_mul_of_nonneg_left hScale hCoeff
    _ = shrinkingExceptionalConstant P * X *
        (Real.log X) ^ (-P.kappa) := by
      unfold shrinkingExceptionalConstant
      dsimp [B, C]
      ring

theorem ShrinkingPolylogParameterPackage.naturalDensityOne_good
    {A c beta : ℝ} (P : ShrinkingPolylogParameterPackage A c beta)
    (hA : 0 < A) :
    NaturalDensityOne
      (assembleDyadic (shrinkingPolylogGood P.run A P.Cswitch)) :=
  naturalDensityOne_of_eventually_badCount_le_polylog
    (shrinkingExceptionalConstant_pos P).le P.kappa_pos
    (P.eventually_badCount hA)

/-- Natural-logarithm form of the shellwise landing, clock, and ceiling. -/
theorem eventually_assembleDyadic_shrinkingPolylogGood_has_landing
    {A c beta : ℝ} (hA : 0 < A) (hc : 0 < c) (hbeta : 0 < beta)
    (P : ShrinkingPolylogParameterPackage A c beta) :
    ∀ᶠ n : ℕ in atTop,
      n ∈ assembleDyadic (shrinkingPolylogGood P.run A P.Cswitch) →
      ∃ k : ℕ,
        (k : ℝ) < c * Real.log n ∧
        (orbit k n : ℝ) <
          fixedPolylogTargetConstant A * (Real.log n) ^ A ∧
        ∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  have hShell :=
    eventually_shrinkingPolylogGood_has_shellLanding_with_orbitCeiling
      hA hbeta P
  have hAtLog := tendsto_natLogTwo_atTop.eventually hShell
  filter_upwards [hAtLog, eventually_ge_atTop (8 : ℕ)]
    with n hAtLog hn8
  intro hnSet
  have hn : 0 < n := by omega
  let M := Nat.log 2 n
  have hnShell : n ∈ dyadicShell M := mem_dyadicShell_log hn
  have hnGood : n ∈ shrinkingPolylogGood P.run A P.Cswitch M := by
    simpa [assembleDyadic, M] using hnSet
  obtain ⟨k, hk, hlanding, hceiling⟩ := hAtLog n hnShell hnGood
  have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hn8Real : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
  have hlogMono : Real.log (8 : ℝ) ≤ Real.log n :=
    Real.log_le_log (by norm_num) hn8Real
  have hlogn : 1 ≤ Real.log n := hlog8.trans hlogMono
  exact ⟨k, hk.trans_le (shellClock_le_natLog hc.le hnShell),
    hlanding.trans_le (shellPolylogTarget_le_natLog hA.le hnShell hlogn),
    hceiling⟩

/-- Fully assembled strongest paper theorem. -/
theorem shrinkingFixedPolylogNaturalDensityDescent
    {A c beta : ℝ}
    (hA : timeSupportCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta) :
    ∃ S : Set ℕ, ∃ C kappa : ℝ,
      0 < C ∧ 0 < kappa ∧ NaturalDensityOne S ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤ C * X * (Real.log X) ^ (-kappa)) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) <
            fixedPolylogTargetConstant A * (Real.log n) ^ A ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) := by
  let P : ShrinkingPolylogParameterPackage A c beta :=
    Classical.choice (exists_shrinkingPolylogParameterPackage hA hc hbeta)
  let S := assembleDyadic (shrinkingPolylogGood P.run A P.Cswitch)
  have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA
  have hc0 : 0 < c := fixedPolylogClockCritical_pos.trans hc
  exact ⟨S, shrinkingExceptionalConstant P, P.kappa,
    shrinkingExceptionalConstant_pos P, P.kappa_pos,
    P.naturalDensityOne_good hA0, P.eventually_badCount hA0,
    eventually_assembleDyadic_shrinkingPolylogGood_has_landing
      hA0 hc0 hbeta P⟩

end

end FirstPassageLinearTransport
