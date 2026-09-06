/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.RawClockBudget
import FirstPassageLinearTransport.NaturalDensityDescent

/-!
# Raw-clock natural-density descent

Parameter selection and global assembly for the literal raw Collatz clock
`261/25 = 10.44`.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section


/-- Starting from the already-selected headline density/descent parameters,
shrink only the envelope width so that the raw leading coefficient has a
strict `10.44` margin. -/
theorem exists_rawClockStage
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ (h : HeadlineScalars delta) (eta : ℝ) (_p : StageSetup h.r eta),
      eta < h.r - a0 ∧ rawClockLeading h.r eta < (261 / 25 : ℝ) := by
  let h : HeadlineScalars delta :=
    Classical.choice (exists_headlineScalars hdelta0 hdelta1)
  let base := (3 / (2 * Real.log 2)) / (1 - h.r)
  let gap := (261 / 25 : ℝ) - base
  have hr1 : h.r < 1 := h.r_lt_one
  have hden : 0 < 1 - h.r := sub_pos.mpr hr1
  have hshortcut := clockLeadingLt6953 h.r_lt_clock
  have hbase : base < (261 / 25 : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_left hshortcut (by norm_num :
      (0 : ℝ) < 3 / 2)
    have hreform :
        base = 3 / 2 * (1 / ((1 - h.r) * Real.log 2)) := by
      dsimp [base]
      field_simp [hden.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    rw [hreform]
    exact hscaled.trans (by norm_num)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let eta := min ((h.r - a0) / 2)
    (gap * (1 - h.r) * Real.log 3 / 2)
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact lt_min (by linarith [h.a0_lt_r]) (by positivity)
  have hetaGap : eta < h.r - a0 := by
    have hle : eta ≤ (h.r - a0) / 2 := by
      dsimp [eta]
      exact min_le_left _ _
    linarith [h.a0_lt_r]
  have hetaBudget :
      eta ≤ gap * (1 - h.r) * Real.log 3 / 2 := by
    dsimp [eta]
    exact min_le_right _ _
  let p : StageSetup h.r eta := Classical.choice
    (exists_stageSetup h.a0_lt_r h.r_lt_one heta0 hetaGap)
  have hextra :
      (eta / Real.log 3) / (1 - h.r) ≤ gap / 2 := by
    apply (div_le_iff₀ hden).2
    apply (div_le_iff₀ hlog3).2
    nlinarith
  refine ⟨h, eta, p, hetaGap, ?_⟩
  unfold rawClockLeading
  have hsplit :
      (3 / (2 * Real.log 2) + eta / Real.log 3) / (1 - h.r) =
        base + (eta / Real.log 3) / (1 - h.r) := by
    dsimp [base]
    ring
  rw [hsplit]
  dsimp [gap] at hextra
  linarith

/-- **Raw timed first-passage natural-density descent.** The literal raw
Collatz orbit reaches the same stretched-logarithmic target before
`10.44 log n` raw steps. -/
theorem firstPassageLinearTransportRawMain
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ j : ℕ,
              (j : ℝ) < (261 / 25 : ℝ) * Real.log n ∧
                (rawOrbit j n : ℝ) ≤
                  Real.exp ((Real.log n) ^ (1 - delta)) := by
  obtain ⟨h, eta, p, hetaGap, hrawLeading⟩ :=
    exists_rawClockStage hdelta0 hdelta1
  let Dc := quadraticWindowDensityRate eta
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
  let S := assembledBootstrap p h.omega
  have hSdense : NaturalDensityOne S :=
    assembledBootstrap_naturalDensityOne_of_vanish p h.omega
      (shellBootstrapRatioTendstoZero p h.chi_pos h.chi_lt_r
        h.chi_le_one hDc0 hDc1 le_rfl hchiDc h.omega_pos hdensity)
  have hlandingM := eventuallyShellLanding p h.omega_pos hdelta1 hdescent
  have hrawM := eventuallyShellRawClockLt p h.omega_pos hrawLeading
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageOrbit p (stageCount h.omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hraw := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (rawTime n (stageClock p (stageCount h.omega M) n) : ℝ) <
        (261 / 25 : ℝ) * Real.log n) hrawM
  refine ⟨S, hSdense, ?_⟩
  filter_upwards [hlanding, hraw, eventually_gt_atTop (0 : ℕ)] with n
    hnlanding hnraw hnpos hnS
  have hnboot : n ∈ bootstrapSet p
      (stageCount h.omega (Nat.log 2 n)) := by
    exact hnS
  let k := stageClock p (stageCount h.omega (Nat.log 2 n)) n
  refine ⟨rawTime n k, hnraw hnpos hnboot, ?_⟩
  rw [rawOrbit_rawTime_eq_orbit]
  rw [← stageOrbit_eq_orbit_stageClock]
  exact hnlanding hnpos hnboot

end

end FirstPassageLinearTransport
