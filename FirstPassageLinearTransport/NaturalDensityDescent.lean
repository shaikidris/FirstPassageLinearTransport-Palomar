/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ClockBudget

/-!
# Natural-density descent assembly

Passage from uniform dyadic-shell landing and clock estimates to the
standalone natural-density-one timed descent theorem.
-/

namespace FirstPassageLinearTransport

open scoped Real Topology BigOperators
open Filter

noncomputable section

/-- Any property that holds uniformly on every sufficiently large dyadic
shell holds for all sufficiently large positive integers at their own shell
index. -/
theorem eventuallyOfEventuallyShellwise
    (P : ℕ → ℕ → Prop)
    (hP : ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M → P M n) :
    ∀ᶠ n : ℕ in atTop, 0 < n → P (Nat.log 2 n) n := by
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 ^ M0)] with n hn
  intro hnpos
  have hlog : M0 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hn
  exact hM0 (Nat.log 2 n) hlog n hnpos (mem_dyadicShell_log hnpos)

/-- For any compatible scalar and stage parameters, the assembled set has
the full timed stretched-log conclusion. -/
theorem assembledBootstrapTimedDescentEventually
    {r eta chi Dc omega delta : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hdensity : densityGamma omega chi < 1)
    (hdelta1 : delta < 1)
    (hdescent : delta < descentAlpha omega r)
    (hrclock : r < clockThreshold) :
    NaturalDensityOne (assembledBootstrap p omega) ∧
      ∀ᶠ n : ℕ in atTop,
        n ∈ assembledBootstrap p omega →
          HasTimedStretchedLogDescent delta (6953 / 1000) n := by
  have hdense : NaturalDensityOne (assembledBootstrap p omega) :=
    assembledBootstrap_naturalDensityOne_of_vanish p omega
      (shellBootstrapRatioTendstoZero p hchi0 hchir hchi1
        hDc0 hDc1 hDcRate hchiDc homega0 hdensity)
  have hlandingM := eventuallyShellLanding p homega0 hdelta1 hdescent
  have hclockM := eventuallyShellClockLt6953 p hrclock homega0
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount omega M) →
      (stageOrbit p (stageCount omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount omega M) →
      (stageClock p (stageCount omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  refine ⟨hdense, ?_⟩
  filter_upwards [hlanding, hclock, eventually_gt_atTop (0 : ℕ)] with n
    hnlanding hnclock hnpos hnassembled
  have hnboot := mem_shellBootstrap_of_mem_assembled p hnassembled
  exact assembledBootstrap_timed_descent_of_scalar_bounds p
    (hnlanding hnpos hnboot) (hnclock hnpos hnboot)

/-- Standalone V2 headline theorem: for every fixed `0 < delta < 1`, a
natural-density-one set reaches the stretched-log threshold along a literal
shortcut Collatz iterate before `6.953 log n` steps. -/
theorem firstPassageLinearTransportMain
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            HasTimedStretchedLogDescent delta (6953 / 1000) n := by
  let h : HeadlineScalars delta :=
    Classical.choice (exists_headlineScalars hdelta0 hdelta1)
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
  have hdensity : densityGamma h.omega h.chi < 1 := by
    simpa [densityGamma, one_div] using h.density_compat
  have hdescent : delta < descentAlpha h.omega h.r := by
    simpa [descentAlpha, one_div] using h.descent_compat
  refine ⟨assembledBootstrap p h.omega, ?_⟩
  exact assembledBootstrapTimedDescentEventually p
    h.chi_pos h.chi_lt_r h.chi_le_one hDc0 hDc1 le_rfl hchiDc
    h.omega_pos hdensity hdelta1 hdescent h.r_lt_clock

end

end FirstPassageLinearTransport
