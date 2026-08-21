/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.NaturalDensityDescent

/-!
# Intermediate-orbit ceiling

Formalization of the intermediate path bound.  The maximal barrier controls
every shortcut prefix inside one stopped block.  Iterating that estimate
introduces only a power of the fixed startup constant; on the logarithmic
stage schedule this is polynomial in the shell index and is absorbed by the
strict exponent margin `eta < beta`.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Every prefix of one retained stopped block stays below the local
`1 + eta` power envelope. -/
theorem orbit_le_one_add_eta_of_le_stageLength
    {r eta : ℝ} (p : StageSetup r eta) {n j : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p)
    (hj : j ≤ stageLength p n) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + eta) := by
  by_cases hlarge : p.M0 ≤ Nat.log 2 n
  · have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW hlarge
    have hjlog : j ≤ Nat.log 2 n :=
      hj.trans (stageLength_le_log p hn hnW)
    have henv := (hgood j hjlog).2
    have hscale : centralOrbitScale j ≤ 1 := by
      rw [centralOrbitScale_eq_rho_pow]
      exact pow_le_one₀ rho_pos.le rho_lt_one.le
    exact henv.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hscale
          (Real.rpow_nonneg (by positivity) (1 + eta)))
  · have hlen : stageLength p n = 0 := by
      simp [stageLength, hlarge]
    have hj0 : j = 0 := by omega
    subst j
    rw [orbit_zero]
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (1 + eta) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [p.eta_pos])

/-- Raising one stopped endpoint to the local envelope exponent costs at
most two powers of the fixed startup constant. -/
theorem stageMap_rpow_one_add_eta_le
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    (stageMap p n : ℝ) ^ (1 + eta) ≤
      stageK p ^ 2 * (n : ℝ) ^ (1 + eta) := by
  have hstage := stageMap_le_power p hn hnW
  have hexp0 : 0 ≤ 1 + eta := by linarith [p.eta_pos]
  have hraise :
      (stageMap p n : ℝ) ^ (1 + eta) ≤
        (stageK p * (n : ℝ) ^ r) ^ (1 + eta) :=
    Real.rpow_le_rpow (by positivity) hstage hexp0
  have hKexp : stageK p ^ (1 + eta) ≤ stageK p ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (stageK_one_le p)
      (by linarith [p.eta_le_one])
  have hK : stageK p ^ (1 + eta) ≤ stageK p ^ 2 := by
    simpa [Real.rpow_two] using hKexp
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrexp : r * (1 + eta) ≤ 1 + eta := by
    nlinarith [p.r_lt_one.le, p.eta_pos]
  have hnPow : (n : ℝ) ^ (r * (1 + eta)) ≤
      (n : ℝ) ^ (1 + eta) :=
    Real.rpow_le_rpow_of_exponent_le hnOne hrexp
  calc
    (stageMap p n : ℝ) ^ (1 + eta) ≤
        (stageK p * (n : ℝ) ^ r) ^ (1 + eta) := hraise
    _ = stageK p ^ (1 + eta) *
        ((n : ℝ) ^ r) ^ (1 + eta) := by
      rw [Real.mul_rpow (stageK_pos p).le (by positivity)]
    _ = stageK p ^ (1 + eta) *
        (n : ℝ) ^ (r * (1 + eta)) := by
      rw [← Real.rpow_mul (by positivity)]
    _ ≤ stageK p ^ 2 * (n : ℝ) ^ (1 + eta) :=
      mul_le_mul hK hnPow (by positivity) (by positivity)

/-- Coarse all-prefix bootstrap envelope.  It deliberately keeps the
startup loss as `stageK^(2R)`; this becomes only polynomial on the scheduled
depth and is absorbed below. -/
theorem orbit_le_stageClock_ceiling
    {r eta : ℝ} (p : StageSetup r eta) {R n j : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R)
    (hj : j ≤ stageClock p R n) :
    (orbit j n : ℝ) ≤
      stageK p ^ (2 * R) * (n : ℝ) ^ (1 + eta) := by
  induction R generalizing n j with
  | zero =>
      have hj0 : j = 0 := by simpa using hj
      subst j
      rw [orbit_zero]
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc
        (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ (n : ℝ) ^ (1 + eta) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [p.eta_pos])
        _ = stageK p ^ (2 * 0) * (n : ℝ) ^ (1 + eta) := by simp
  | succ R ih =>
      rw [bootstrapSet_succ] at hnSet
      have hnW : n ∈ extendedWindow p := hnSet.1
      have hmapSet : stageMap p n ∈ bootstrapSet p R := hnSet.2
      by_cases hjlen : j ≤ stageLength p n
      · have hblock := orbit_le_one_add_eta_of_le_stageLength p hn hnW hjlen
        have hfactor : (1 : ℝ) ≤ stageK p ^ (2 * (R + 1)) :=
          one_le_pow₀ (stageK_one_le p)
        exact hblock.trans (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hfactor
              (Real.rpow_nonneg (by positivity) (1 + eta)))
      · let q := j - stageLength p n
        have hjform : j = stageLength p n + q := by
          dsimp [q]
          omega
        have hqclock : q ≤ stageClock p R (stageMap p n) := by
          rw [stageClock_succ] at hj
          dsimp [q]
          omega
        have hmapPos : 0 < stageMap p n := by
          rw [stageMap_is_actual]
          exact orbit_pos hn _
        have hIH := ih hmapPos hmapSet hqclock
        have hmapPow := stageMap_rpow_one_add_eta_le p hn hnW
        rw [hjform, add_comm, orbit_add, ← stageMap_is_actual]
        calc
          (orbit q (stageMap p n) : ℝ) ≤
              stageK p ^ (2 * R) *
                (stageMap p n : ℝ) ^ (1 + eta) := hIH
          _ ≤ stageK p ^ (2 * R) *
                (stageK p ^ 2 * (n : ℝ) ^ (1 + eta)) :=
            mul_le_mul_of_nonneg_left hmapPow
              (pow_nonneg (stageK_pos p).le _)
          _ = stageK p ^ (2 * (R + 1)) *
                (n : ℝ) ^ (1 + eta) := by
            rw [show 2 * (R + 1) = 2 * R + 2 by omega, pow_add]
            ring

/-- On the logarithmic stage schedule, the fixed startup factor in the
all-prefix envelope is swallowed by every strict exponent margin
`eta < beta`. -/
theorem eventuallyShellOrbitCeiling
    {r eta omega beta : ℝ} (p : StageSetup r eta)
    (homega : 0 < omega) (hetaBeta : eta < beta) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      ∀ j : ℕ, j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  let A := 2 * omega * Real.log (stageK p)
  let c := (beta - eta) * Real.log 2 / 2
  have hlogK0 : 0 ≤ Real.log (stageK p) :=
    Real.log_nonneg (stageK_one_le p)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos
      (mul_pos (sub_pos.mpr hetaBeta) (Real.log_pos (by norm_num)))
      (by norm_num)
  have hscalarReal := eventuallyLogAddRpowLe
    (A := A) (C := 0) (c := c) (a := (1 / 2 : ℝ)) (delta := 0)
    hA (by norm_num) hc (by norm_num) (by norm_num)
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hscalar := hxT.eventually hscalarReal
  filter_upwards [hscalar, eventually_ge_atTop (4 : ℕ)] with M hsc hM
  intro n hn hnshell hnboot j hj
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 0 < x := by dsimp [x]; positivity
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by dsimp [x]; linarith)
  have hsc' : A * Real.log x ≤ c * x := by
    simpa [x] using hsc
  have hxM : x ≤ 2 * (M : ℝ) := by
    dsimp [x]
    exact_mod_cast (by omega : M + 4 ≤ 2 * M)
  have hlinear : A * Real.log x ≤
      (beta - eta) * (M : ℝ) * Real.log 2 := by
    calc
      A * Real.log x ≤ c * x := hsc'
      _ ≤ c * (2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hxM hc.le
      _ = (beta - eta) * (M : ℝ) * Real.log 2 := by
        dsimp [c]
        ring
  have hR := stageCount_le homega.le M
  have hRlog : (2 * R : ℕ) * Real.log (stageK p) ≤
      A * Real.log x := by
    have htwoLogK : 0 ≤ 2 * Real.log (stageK p) :=
      mul_nonneg (by norm_num) hlogK0
    have hmul := mul_le_mul_of_nonneg_right hR htwoLogK
    dsimp [R, A, x] at hmul ⊢
    push_cast at hmul ⊢
    nlinarith
  have hlowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnshell).1
  have hlowerCast : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast hlowerNat
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
      hlowerCast
    rw [Real.log_pow] at h
    exact h
  have hmargin : 0 ≤ beta - eta := sub_nonneg.mpr hetaBeta.le
  have hexponent : (2 * R : ℕ) * Real.log (stageK p) ≤
      (beta - eta) * Real.log n := by
    calc
      (2 * R : ℕ) * Real.log (stageK p) ≤ A * Real.log x := hRlog
      _ ≤ (beta - eta) * (M : ℝ) * Real.log 2 := hlinear
      _ ≤ (beta - eta) * Real.log n := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hlogLower hmargin)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor : stageK p ^ (2 * R) ≤ (n : ℝ) ^ (beta - eta) := by
    rw [← Real.exp_log (pow_pos (stageK_pos p) (2 * R)), Real.log_pow,
      Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.2
    push_cast
    simpa [mul_comm] using hexponent
  have hpath := orbit_le_stageClock_ceiling p hn hnboot hj
  calc
    (orbit j n : ℝ) ≤
        stageK p ^ (2 * R) * (n : ℝ) ^ (1 + eta) := hpath
    _ ≤ (n : ℝ) ^ (beta - eta) * (n : ℝ) ^ (1 + eta) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (1 + beta) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring

/-- One density-one set and one witness simultaneously satisfy the shortcut
clock, the stretched-log landing, and the intermediate-orbit ceiling through
that witness. -/
theorem firstPassageLinearTransportOrbitCeiling
    {delta beta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hbeta : 0 < beta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ k : ℕ,
              (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
                (orbit k n : ℝ) ≤
                  Real.exp ((Real.log n) ^ (1 - delta)) ∧
                ∀ j : ℕ, j ≤ k →
                  (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  let h : HeadlineScalars delta :=
    Classical.choice (exists_headlineScalars hdelta0 hdelta1)
  let eta := min ((h.r - a0) / 2) (beta / 2)
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact lt_min (by linarith [h.a0_lt_r]) (by linarith)
  have hetaGap : eta < h.r - a0 := by
    have hle : eta ≤ (h.r - a0) / 2 := min_le_left _ _
    dsimp only [eta] at hle ⊢
    linarith [h.a0_lt_r]
  have hetaBeta : eta < beta := by
    have hle : eta ≤ beta / 2 := min_le_right _ _
    dsimp only [eta] at hle ⊢
    linarith
  let p : StageSetup h.r eta :=
    Classical.choice (exists_stageSetup h.a0_lt_r h.r_lt_one
      heta0 hetaGap)
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
  have hclockM := eventuallyShellClockLt6953 p h.r_lt_clock h.omega_pos
  have hceilingM := eventuallyShellOrbitCeiling p h.omega_pos hetaBeta
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageOrbit p (stageCount h.omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageClock p (stageCount h.omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  have hceiling := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      ∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) hceilingM
  refine ⟨S, hSdense, ?_⟩
  filter_upwards [hlanding, hclock, hceiling,
    eventually_gt_atTop (0 : ℕ)] with n hnlanding hnclock hnceiling hnpos hnS
  have hnboot : n ∈ bootstrapSet p
      (stageCount h.omega (Nat.log 2 n)) := by
    exact hnS
  let k := stageClock p (stageCount h.omega (Nat.log 2 n)) n
  refine ⟨k, hnclock hnpos hnboot, ?_, hnceiling hnpos hnboot⟩
  rw [← stageOrbit_eq_orbit_stageClock]
  exact hnlanding hnpos hnboot

end

end FirstPassageLinearTransport
