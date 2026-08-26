/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.StretchedLogLanding
import FirstPassageLinearTransport.StretchedExceptionalCount

/-!
# Quantitative natural-density descent

This module combines the stretched shell ratio with the generic dyadic
summation theorem.  The target is inserted before summation, so arbitrary
finite startup shells are paid by the existing leading `1` in the exact
prefactor `1 + 2 * A`; no separate finite-error absorption is needed.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- On shell `M`, retain only bootstrap sources certified to satisfy the
requested target predicate. -/
def targetCertifiedShell {r eta : ℝ} (p : StageSetup r eta)
    (omega : ℝ) (Good : ℕ → Prop) (M : ℕ) : Set ℕ :=
  shellBootstrap p omega M ∩ {n | Good n}

/-- Assemble the target-certified shell family. -/
def targetCertifiedSet {r eta : ℝ} (p : StageSetup r eta)
    (omega : ℝ) (Good : ℕ → Prop) : Set ℕ :=
  assembleDyadic (targetCertifiedShell p omega Good)

theorem targetCertifiedSet_subset {r eta : ℝ} (p : StageSetup r eta)
    (omega : ℝ) (Good : ℕ → Prop) :
    targetCertifiedSet p omega Good ⊆ {n | Good n} := by
  intro n hn
  exact hn.2

/-- If every bootstrap source in one shell satisfies `Good`, certification
does not change that shell's exceptional ratio. -/
theorem shellExceptionalRatio_targetCertifiedShell_eq
    {r eta omega : ℝ} (p : StageSetup r eta) (Good : ℕ → Prop) (M : ℕ)
    (hgood : ∀ n : ℕ, 0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) → Good n) :
    shellExceptionalRatio (targetCertifiedShell p omega Good M) M =
      shellExceptionalRatio (shellBootstrap p omega M) M := by
  have hbad :
      shellBad (targetCertifiedShell p omega Good M) M =
        shellBad (shellBootstrap p omega M) M := by
    classical
    ext n
    simp only [shellBad, Finset.mem_filter]
    constructor
    · rintro ⟨hnshell, hncert⟩
      refine ⟨hnshell, ?_⟩
      intro hnboot
      apply hncert
      refine ⟨hnboot, hgood n ?_ hnshell hnboot⟩
      have hnlow := (mem_dyadicShell.mp hnshell).1
      have hp : 0 < 2 ^ M := by positivity
      omega
    · rintro ⟨hnshell, hnboot⟩
      refine ⟨hnshell, ?_⟩
      intro hncert
      exact hnboot hncert.1
  unfold shellExceptionalRatio
  rw [hbad]

/-- A target predicate holding on all sufficiently large retained shells has
the same quantitative exceptional count as the bootstrap set itself. -/
theorem targetExceptionalCountEventually
    {r eta chi Dc omega sigma : ℝ} (p : StageSetup r eta)
    (Good : ℕ → Prop)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - densityGamma omega chi)
    (hgood : ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) → Good n) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount {n | Good n} X : ℝ) ≤
        5 * X * Real.exp (-c * (Real.log X) ^ sigma) := by
  obtain ⟨c0, hc0, hratio⟩ :=
    eventuallyShellBootstrapRatioLeStretched p
      hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega0
      hsigma0 hsigma
  have hcert : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (targetCertifiedShell p omega Good M) M ≤
        2 * Real.exp (-c0 * ((M : ℝ) + 4) ^ sigma) := by
    filter_upwards [hratio, hgood] with M hratioM hgoodM
    rw [shellExceptionalRatio_targetCertifiedShell_eq p Good M hgoodM]
    exact hratioM
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hcert
  let c := QuantitativeDensity.stretchedDyadicRate c0 / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (QuantitativeDensity.stretchedDyadicRate_pos hc0) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ (2 * M0 + 2))] with X hX
  have hX0 : 0 < X := by
    have hp : 0 < 2 ^ (2 * M0 + 2) := by positivity
    omega
  have hlogLower : 2 * M0 + 2 ≤ Nat.log 2 X :=
    Nat.le_log_of_pow_le (by norm_num) hX
  have hL2 : 2 ≤ Nat.log 2 X := by omega
  have hMhalf : M0 ≤ (Nat.log 2 X) / 2 := by omega
  have hloginv0 : 0 ≤ Real.log (1 / chi) := by
    apply Real.log_nonneg
    rw [one_le_div hchi0]
    exact hchi1
  have hgamma0 : 0 ≤ densityGamma omega chi := by
    unfold densityGamma
    positivity
  have hsigma1 : sigma ≤ 1 := by linarith
  have hbound :=
    QuantitativeDensity.badCount_assembleDyadic_le_stretched_log
      (targetCertifiedShell p omega Good) M0 X 2 c0 sigma
      (by norm_num) hc0 hsigma0 hsigma1
      (by
        intro M hM
        simpa [QuantitativeDensity.stretchedShellScale] using hM0 M hM)
      hX0 hL2 hMhalf
  have hmono :
      badCount {n | Good n} X ≤
        badCount (targetCertifiedSet p omega Good) X := by
    unfold badCount
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hncert => hn.2
      (targetCertifiedSet_subset p omega Good hncert)⟩
  have hmonoR :
      (badCount {n | Good n} X : ℝ) ≤
        (badCount (targetCertifiedSet p omega Good) X : ℝ) := by
    exact_mod_cast hmono
  norm_num at hbound
  exact hmonoR.trans (by
    simpa [targetCertifiedSet, c] using hbound)

/-- Quantitative stretched-logarithmic exceptional count for any compatible
parameter package with an explicit density margin. -/
theorem stretchedLogExceptionalCountEventually
    {r eta chi Dc omega delta sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hdelta1 : delta < 1)
    (hdescent : delta < descentAlpha omega r)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount {n | HasStretchedLogDescent delta n} X : ℝ) ≤
        5 * X * Real.exp (-c * (Real.log X) ^ sigma) := by
  have hlanding := eventuallyShellLanding p homega0 hdelta1 hdescent
  apply targetExceptionalCountEventually p
    (fun n => HasStretchedLogDescent delta n)
    hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega0
    hsigma0 hsigma
  filter_upwards [hlanding] with M hlandingM
  intro n hn hnshell hnboot
  refine ⟨stageClock p (stageCount omega M) n, ?_⟩
  rw [← stageOrbit_eq_orbit_stageClock]
  exact hlandingM n hn hnshell hnboot

/-- Literal quantitative form of Theorem 1.3. -/
theorem firstPassageLinearTransportQuantitativeStretched
    {delta sigma : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 - delta) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount {n | HasStretchedLogDescent delta n} X : ℝ) ≤
        5 * X * Real.exp (-c * (Real.log X) ^ sigma) := by
  let h : QuantitativeHeadlineScalars delta sigma :=
    Classical.choice
      (exists_quantitativeHeadlineScalars hdelta0 hsigma0 hsigma)
  let p : StageSetup h.r h.eta :=
    Classical.choice (exists_stageSetup h.a0_lt_r h.r_lt_one
      h.eta_pos h.eta_gap)
  let Dc := quadraticWindowDensityRate h.eta
  have hDc0 : 0 < Dc := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_pos
  have hDc1 : Dc ≤ 1 := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_le_one
  have hchiDc : h.chi * Dc < 1 := by
    have hprod : h.chi * Dc ≤ h.chi * 1 :=
      mul_le_mul_of_nonneg_left hDc1 h.chi_pos.le
    nlinarith [h.chi_lt_r.trans h.r_lt_one]
  have hdescent : delta < descentAlpha h.omega h.r := by
    simpa [descentAlpha, one_div] using h.descent_compat
  have hdensityMargin : sigma < 1 - densityGamma h.omega h.chi := by
    simpa [densityGamma, one_div, add_comm] using h.density_margin
  exact stretchedLogExceptionalCountEventually p
    h.chi_pos h.chi_lt_r h.chi_le_one hDc0 hDc1 le_rfl hchiDc
    h.omega_pos hdelta1 hdescent hsigma0 hdensityMargin

/-- Every fixed stretched-log target with positive `delta` is eventually
below every fixed positive power. -/
theorem eventuallyStretchedLePower {delta alpha : ℝ}
    (hdelta0 : 0 < delta) (halpha : 0 < alpha) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((Real.log n) ^ (1 - delta)) ≤ (n : ℝ) ^ alpha := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hneg : Tendsto
      (fun n : ℕ => (Real.log n) ^ (-delta)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hdelta0).comp hlog
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (Real.log n) ^ (-delta) < alpha :=
    (tendsto_order.1 hneg).2 alpha halpha
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℕ)] with n hnsmall hn
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast hn)
  have hpow : (Real.log n) ^ (1 - delta) < alpha * Real.log n := by
    calc
      (Real.log n) ^ (1 - delta) =
          (Real.log n) ^ ((1 : ℝ) + (-delta)) := by ring_nf
      _ = (Real.log n) ^ (1 : ℝ) *
          (Real.log n) ^ (-delta) :=
        Real.rpow_add hlogpos _ _
      _ = (Real.log n) * (Real.log n) ^ (-delta) := by
        rw [Real.rpow_one]
      _ < (Real.log n) * alpha :=
        mul_lt_mul_of_pos_left hnsmall hlogpos
      _ = alpha * Real.log n := by ring
  rw [Real.rpow_def_of_pos hnReal]
  exact Real.exp_le_exp.2 (by simpa [mul_comm] using hpow.le)

/-- A property holding for all sufficiently large integers holds uniformly
on every sufficiently large dyadic shell. -/
theorem eventuallyShellwise_of_eventually (P : ℕ → Prop)
    (hP : ∀ᶠ n : ℕ in atTop, P n) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M → P n := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop N0] with M hM
  intro n _hn hnshell
  have hMpow : M ≤ 2 ^ M := by
    have htwo := Nat.mul_le_pow (a := 2) (by norm_num) M
    omega
  have hnlow := (mem_dyadicShell.mp hnshell).1
  exact hN0 n (hM.trans (hMpow.trans hnlow))

/-- Literal quantitative form of Corollary 1.5. -/
theorem firstPassageLinearTransportQuantitativeFixedPower
    {alpha sigma : ℝ} (halpha : 0 < alpha)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount {n | HasFixedPowerDescent alpha n} X : ℝ) ≤
        5 * X * Real.exp (-c * (Real.log X) ^ sigma) := by
  let delta := (1 - sigma) / 2
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta < 1 := by dsimp [delta]; linarith
  have hsigmaGap : sigma < 1 - delta := by
    dsimp [delta]
    linarith
  let h : QuantitativeHeadlineScalars delta sigma :=
    Classical.choice
      (exists_quantitativeHeadlineScalars hdelta0 hsigma0 hsigmaGap)
  let p : StageSetup h.r h.eta :=
    Classical.choice (exists_stageSetup h.a0_lt_r h.r_lt_one
      h.eta_pos h.eta_gap)
  let Dc := quadraticWindowDensityRate h.eta
  have hDc0 : 0 < Dc := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_pos
  have hDc1 : Dc ≤ 1 := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_le_one
  have hchiDc : h.chi * Dc < 1 := by
    have hprod : h.chi * Dc ≤ h.chi * 1 :=
      mul_le_mul_of_nonneg_left hDc1 h.chi_pos.le
    nlinarith [h.chi_lt_r.trans h.r_lt_one]
  have hdescent : delta < descentAlpha h.omega h.r := by
    simpa [descentAlpha, one_div] using h.descent_compat
  have hdensityMargin : sigma < 1 - densityGamma h.omega h.chi := by
    simpa [densityGamma, one_div, add_comm] using h.density_margin
  have hlanding := eventuallyShellLanding p h.omega_pos hdelta1 hdescent
  have hcompare := eventuallyStretchedLePower hdelta0 halpha
  have hcompareShell := eventuallyShellwise_of_eventually
    (fun n => Real.exp ((Real.log n) ^ (1 - delta)) ≤
      (n : ℝ) ^ alpha) hcompare
  apply targetExceptionalCountEventually p
    (fun n => HasFixedPowerDescent alpha n)
    h.chi_pos h.chi_lt_r h.chi_le_one hDc0 hDc1 le_rfl hchiDc
    h.omega_pos hsigma0 hdensityMargin
  filter_upwards [hlanding, hcompareShell] with M hlandingM hcompareM
  intro n hn hnshell hnboot
  refine ⟨stageClock p (stageCount h.omega M) n, ?_⟩
  rw [← stageOrbit_eq_orbit_stageClock]
  exact (hlandingM n hn hnshell hnboot).trans
    (hcompareM n hn hnshell)

end

end FirstPassageLinearTransport
