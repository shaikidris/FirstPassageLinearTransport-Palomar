/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.OrbitCeiling
import FirstPassageLinearTransport.RawNaturalDensityDescent
import FirstPassageLinearTransport.StretchedExceptionalCount

/-!
# Stretched-logarithmic relative-height strengthening

This module transfers the finite multiplicative-maximum argument to the
fixed-barrier bootstrap chain.  It gives a common shortcut/raw landing whose
two preceding trajectories stay below
`n * exp (zeta * (log n)^(1-delta))` on a natural-density-one set.

The module proves both a qualitative theorem and a quantitative form retaining
every strict exceptional exponent `sigma < 1 - delta`.  The manuscript's
endpoint exponent `1 - delta` and arbitrary strict clock coefficients require
the separate Version 4 fixed-barrier interface.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- A stopped block never increases its checkpoint. -/
theorem stageMap_le_self
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    stageMap p n ≤ n := by
  let M := Nat.log 2 n
  have hshell : n ∈ dyadicShell M := mem_dyadicShell_log hn
  by_cases hlarge : p.M0 ≤ M
  · have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW hlarge
    have hfp := stageLength_isFirstPassage p hlarge hshell hgood
    exact hfp.1.trans (p.target_lt_shell M hlarge).le |>.trans
      (mem_dyadicShell.mp hshell).1
  · simp [stageMap, stageLength, M, hlarge]

/-- On the large branch, the first stopped checkpoint pays no startup
constant: it lies below the exact power of its source. -/
theorem stageMap_le_rpow_of_large
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p)
    (hlarge : p.M0 ≤ Nat.log 2 n) :
    (stageMap p n : ℝ) ≤ (n : ℝ) ^ r := by
  let M := Nat.log 2 n
  have hshell : n ∈ dyadicShell M := mem_dyadicShell_log hn
  have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW hlarge
  have hfp := stageLength_isFirstPassage p hlarge hshell hgood
  have hstage : (stageMap p n : ℝ) ≤ targetScale r M := by
    exact_mod_cast hfp.1
  have hrM0 : 0 ≤ r * (M : ℝ) :=
    mul_nonneg p.r_pos.le (Nat.cast_nonneg M)
  have hfloor : (⌊r * (M : ℝ)⌋₊ : ℝ) ≤ r * M :=
    Nat.floor_le hrM0
  have htarget : (targetScale r M : ℝ) ≤ (2 : ℝ) ^ (r * M) := by
    unfold targetScale
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
  have hbase : (2 : ℝ) ^ M ≤ n := by
    exact_mod_cast (mem_dyadicShell.mp hshell).1
  have hpow : (2 : ℝ) ^ (r * M) ≤ (n : ℝ) ^ r := by
    calc
      (2 : ℝ) ^ (r * M) = (2 : ℝ) ^ ((M : ℝ) * r) := by ring_nf
      _ = ((2 : ℝ) ^ M) ^ r := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ (n : ℝ) ^ r :=
        Real.rpow_le_rpow (by positivity) hbase p.r_pos.le
  exact hstage.trans (htarget.trans hpow)

/-- Once a checkpoint lies below `root^r`, every prefix in the remaining
bootstrap chain stays below `root`, provided `r(1+eta) ≤ 1`. -/
theorem orbit_le_root_of_stageClock_of_le_rpow
    {r eta : ℝ} (p : StageSetup r eta)
    (hre : r * (1 + eta) ≤ 1)
    {R m : ℕ} {root : ℝ}
    (hm : 0 < m) (hmSet : m ∈ bootstrapSet p R)
    (hroot : 1 ≤ root) (hmroot : (m : ℝ) ≤ root ^ r) :
    ∀ j : ℕ, j ≤ stageClock p R m → (orbit j m : ℝ) ≤ root := by
  induction R generalizing m with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      rw [orbit_zero]
      calc
        (m : ℝ) ≤ root ^ r := hmroot
        _ ≤ root ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hroot p.r_lt_one.le
        _ = root := Real.rpow_one root
  | succ R ih =>
      rw [bootstrapSet_succ] at hmSet
      have hmW : m ∈ extendedWindow p := hmSet.1
      have hchildSet : stageMap p m ∈ bootstrapSet p R := hmSet.2
      have hchildPos : 0 < stageMap p m := by
        rw [stageMap_is_actual]
        exact orbit_pos hm _
      have hmapLe : (stageMap p m : ℝ) ≤ root ^ r := by
        have hcast : (stageMap p m : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast stageMap_le_self p hm hmW
        exact hcast.trans hmroot
      intro j hj
      by_cases hjlen : j ≤ stageLength p m
      · have hlocal := orbit_le_one_add_eta_of_le_stageLength p hm hmW hjlen
        have hm0 : 0 ≤ (m : ℝ) := by positivity
        have hraise : (m : ℝ) ^ (1 + eta) ≤
            (root ^ r) ^ (1 + eta) :=
          Real.rpow_le_rpow hm0 hmroot (by linarith [p.eta_pos])
        have hroot0 : 0 < root := zero_lt_one.trans_le hroot
        calc
          (orbit j m : ℝ) ≤ (m : ℝ) ^ (1 + eta) := hlocal
          _ ≤ (root ^ r) ^ (1 + eta) := hraise
          _ = root ^ (r * (1 + eta)) := by
            rw [Real.rpow_mul hroot0.le]
          _ ≤ root ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hroot hre
          _ = root := Real.rpow_one root
      · let q := j - stageLength p m
        have hjform : j = stageLength p m + q := by
          dsimp [q]
          omega
        have hqclock : q ≤ stageClock p R (stageMap p m) := by
          rw [stageClock_succ] at hj
          dsimp [q]
          omega
        rw [hjform, add_comm, orbit_add, ← stageMap_is_actual]
        exact ih hchildPos hchildSet hmapLe q hqclock

/-- On every sufficiently large shell, deleting the finite multiplicative
hit event gives a common shortcut/raw relative-height bound for the entire
fixed-barrier bootstrap chain. -/
theorem eventuallyShellBootstrapRelativeHeight
    {r eta omega : ℝ} (p : StageSetup r eta)
    (homega : 0 < omega) (hre : r * (1 + eta) ≤ 1) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, ∀ H : ℝ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      4 ≤ H → n ∉ shellMultiplicativeHit M (H / 4) →
      (∀ j : ℕ, j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) * H / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n (stageClock p (stageCount omega M) n) →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * H) := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 4)) atTop atTop :=
    Real.tendsto_log_atTop.comp hxT
  have hscaledT : Tendsto
      (fun M : ℕ => omega * Real.log ((M : ℝ) + 4)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop homega hlogT
  have hstageLarge : ∀ᶠ M : ℕ in atTop,
      2 ≤ omega * Real.log ((M : ℝ) + 4) :=
    (tendsto_atTop.1 hscaledT) 2
  filter_upwards [eventually_ge_atTop p.M0, hstageLarge] with M hM hstageLarge
  intro n H hn hnshell hnboot hH hnHit
  have hstageCast := stageCount_gt_sub_one (omega := omega) M
  have hstagePos : 0 < stageCount omega M := by
    have hreal : (0 : ℝ) < stageCount omega M := by linarith
    exact_mod_cast hreal
  obtain ⟨R, hstageEq⟩ := Nat.exists_eq_succ_of_ne_zero hstagePos.ne'
  rw [hstageEq, bootstrapSet_succ] at hnboot
  have hnW : n ∈ extendedWindow p := hnboot.1
  have hchildSet : stageMap p n ∈ bootstrapSet p R := hnboot.2
  have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW (by
    simpa [log_two_eq_of_mem_dyadicShell hnshell] using hM)
  have hlen : stageLength p n ≤ M :=
    stageLength_le_shell p hM hnshell hgood
  have hmapPos : 0 < stageMap p n := by
    rw [stageMap_is_actual]
    exact orbit_pos hn _
  have hmap : (stageMap p n : ℝ) ≤ (n : ℝ) ^ r :=
    stageMap_le_rpow_of_large p hn hnW (by
      simpa [log_two_eq_of_mem_dyadicShell hnshell] using hM)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hinitial :=
    initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
      hnshell hnHit
  have hshortcut : ∀ j : ℕ,
      j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) * H / 2 := by
    intro j hj
    rw [hstageEq, stageClock_succ] at hj
    by_cases hjlen : j ≤ stageLength p n
    · exact (hinitial.1 j (hjlen.trans hlen)).le
    · let q := j - stageLength p n
      have hjform : j = stageLength p n + q := by
        dsimp [q]
        omega
      have hqclock : q ≤ stageClock p R (stageMap p n) := by
        dsimp [q]
        omega
      have htail := orbit_le_root_of_stageClock_of_le_rpow
        p hre hmapPos hchildSet hnOne hmap q hqclock
      rw [hjform, add_comm, orbit_add, ← stageMap_is_actual]
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hhalf : 1 ≤ H / 2 := by linarith
      exact htail.trans (by
        calc
          (n : ℝ) = (n : ℝ) * 1 := by ring
          _ ≤ (n : ℝ) * (H / 2) :=
            mul_le_mul_of_nonneg_left hhalf hn0
          _ = (n : ℝ) * H / 2 := by ring)
  refine ⟨hshortcut, ?_⟩
  intro i hi
  have hraw := rawOrbit_le_two_mul_of_shortcut_prefix_le hshortcut i hi
  calc
    (rawOrbit i n : ℝ) ≤ 2 * ((n : ℝ) * H / 2) := hraw
    _ = (n : ℝ) * H := by ring

/-- Shellwise relative-height allowance for a stretched-logarithmic target. -/
def stretchedHeightShellAllowance (zeta alpha : ℝ) (M : ℕ) : ℝ :=
  Real.exp (zeta * (((M : ℝ) * Real.log 2) ^ alpha))

/-- Retain the fixed-barrier bootstrap sources whose first-shell
multiplicative prefixes stay below the quarter allowance. -/
def heightCertifiedShell
    {r eta : ℝ} (p : StageSetup r eta)
    (omega zeta alpha : ℝ) (M : ℕ) : Set ℕ :=
  shellBootstrap p omega M ∩
    {n | n ∉ shellMultiplicativeHit M
      (stretchedHeightShellAllowance zeta alpha M / 4)}

/-- Global set assembled from the height-certified shells. -/
def assembledHeightCertified
    {r eta : ℝ} (p : StageSetup r eta)
    (omega zeta alpha : ℝ) : Set ℕ :=
  assembleDyadic (heightCertifiedShell p omega zeta alpha)

theorem shellBad_heightCertifiedShell_subset
    {r eta omega zeta alpha : ℝ} (p : StageSetup r eta) (M : ℕ) :
    shellBad (heightCertifiedShell p omega zeta alpha M) M ⊆
      shellBad (shellBootstrap p omega M) M ∪
        shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4) := by
  classical
  intro n hn
  simp only [shellBad, heightCertifiedShell, Finset.mem_filter,
    Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union] at hn ⊢
  rcases hn with ⟨hnshell, hncert⟩
  by_cases hnboot : n ∈ shellBootstrap p omega M
  · exact Or.inr (by
      by_contra hnHit
      exact hncert ⟨hnboot, hnHit⟩)
  · exact Or.inl ⟨hnshell, hnboot⟩

/-- Removing the multiplicative-hit event adds only its exact reciprocal
shell cost to the bootstrap exceptional ratio. -/
theorem shellExceptionalRatio_heightCertifiedShell_le
    {r eta omega zeta alpha : ℝ} (p : StageSetup r eta) (M : ℕ) :
    shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
      shellExceptionalRatio (shellBootstrap p omega M) M +
        ((shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4)).card : ℝ) /
            (2 : ℝ) ^ M := by
  have hsub := shellBad_heightCertifiedShell_subset
    (omega := omega) (zeta := zeta) (alpha := alpha) p M
  have hcardNat := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (shellBad (shellBootstrap p omega M) M)
    (shellMultiplicativeHit M
      (stretchedHeightShellAllowance zeta alpha M / 4))
  have hcard :
      ((shellBad (heightCertifiedShell p omega zeta alpha M) M).card : ℝ) ≤
        (shellBad (shellBootstrap p omega M) M).card +
          (shellMultiplicativeHit M
            (stretchedHeightShellAllowance zeta alpha M / 4)).card := by
    exact_mod_cast hcardNat.trans hunion
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  unfold shellExceptionalRatio
  calc
    ((shellBad (heightCertifiedShell p omega zeta alpha M) M).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((shellBad (shellBootstrap p omega M) M).card : ℝ) +
        (shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4)).card) /
          (2 : ℝ) ^ M :=
      div_le_div_of_nonneg_right hcard hpow.le
    _ = ((shellBad (shellBootstrap p omega M) M).card : ℝ) /
          (2 : ℝ) ^ M +
        ((shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4)).card : ℝ) /
            (2 : ℝ) ^ M := add_div _ _ _

theorem shellExceptionalRatio_heightCertifiedShell_le_inv
    {r eta omega zeta alpha : ℝ} (p : StageSetup r eta) (M : ℕ) :
    shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
      shellExceptionalRatio (shellBootstrap p omega M) M +
        4 / stretchedHeightShellAllowance zeta alpha M := by
  have hbase := shellExceptionalRatio_heightCertifiedShell_le
    (omega := omega) (zeta := zeta) (alpha := alpha) p M
  have hhit := normalized_card_shellMultiplicativeHit_quarter_le
    (R := stretchedHeightShellAllowance zeta alpha M)
    (Real.exp_pos _) M
  exact hbase.trans (add_le_add (le_refl _) hhit)

/-- The reciprocal height cost has the same stretched-power shell form as
the fixed-barrier bootstrap error. -/
theorem eventually_four_div_stretchedHeightShellAllowance_le_stretched
    {zeta alpha sigma : ℝ} (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigmaAlpha : sigma ≤ alpha) :
    ∀ᶠ M : ℕ in atTop,
      4 / stretchedHeightShellAllowance zeta alpha M ≤
        4 * Real.exp
          (-(zeta * (Real.log 2 / 2) ^ alpha) *
            (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with M hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase0 : 0 ≤ Real.log 2 / 2 := (div_pos hlog2 (by norm_num)).le
  have hshift0 : 0 ≤ QuantitativeDensity.stretchedShellScale M :=
    (QuantitativeDensity.stretchedShellScale_pos M).le
  have hM0 : 0 ≤ (M : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg M) hlog2.le
  have hbase :
      (Real.log 2 / 2) * QuantitativeDensity.stretchedShellScale M ≤
        (M : ℝ) * Real.log 2 := by
    unfold QuantitativeDensity.stretchedShellScale
    have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hpow := Real.rpow_le_rpow
    (mul_nonneg hbase0 hshift0) hbase halpha0.le
  rw [Real.mul_rpow hbase0 hshift0] at hpow
  have hscaleOne : 1 ≤ QuantitativeDensity.stretchedShellScale M := by
    unfold QuantitativeDensity.stretchedShellScale
    have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hpowCompare :
      (QuantitativeDensity.stretchedShellScale M) ^ sigma ≤
        (QuantitativeDensity.stretchedShellScale M) ^ alpha := by
    exact Real.rpow_le_rpow_of_exponent_le hscaleOne hsigmaAlpha
  have hcoeff0 : 0 ≤ (Real.log 2 / 2) ^ alpha :=
    Real.rpow_nonneg hbase0 _
  have hpowSigma :
      (Real.log 2 / 2) ^ alpha *
          (QuantitativeDensity.stretchedShellScale M) ^ sigma ≤
        ((M : ℝ) * Real.log 2) ^ alpha := by
    exact (mul_le_mul_of_nonneg_left hpowCompare hcoeff0).trans hpow
  have hexp :
      Real.exp (-(zeta * (((M : ℝ) * Real.log 2) ^ alpha))) ≤
        Real.exp
          (-(zeta * (Real.log 2 / 2) ^ alpha) *
            (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
    apply Real.exp_le_exp.2
    nlinarith
  unfold stretchedHeightShellAllowance
  rw [div_eq_mul_inv, ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- The height-certified shell retains the stretched-exponential bootstrap
rate.  The resulting rate is the minimum of the bootstrap rate and the
reciprocal height-allowance rate. -/
theorem eventually_heightCertifiedShellRatioLeStretched
    {r eta chi Dc omega zeta alpha sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigma0 : 0 < sigma) (hsigmaAlpha : sigma ≤ alpha)
    (hsigmaDensity : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
        6 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
  obtain ⟨cBoot, hcBoot, hboot⟩ :=
    eventuallyShellBootstrapRatioLeStretched p
      hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega0
      hsigma0 hsigmaDensity
  let cHeight := zeta * (Real.log 2 / 2) ^ alpha
  have hcHeight : 0 < cHeight := by
    dsimp [cHeight]
    positivity
  let c := min cBoot cHeight
  have hc : 0 < c := lt_min hcBoot hcHeight
  have hheight :=
    eventually_four_div_stretchedHeightShellAllowance_le_stretched
      hzeta halpha0 hsigmaAlpha
  refine ⟨c, hc, ?_⟩
  filter_upwards [hboot, hheight] with M hbootM hheightM
  have hscale0 :
      0 ≤ (QuantitativeDensity.stretchedShellScale M) ^ sigma :=
    Real.rpow_nonneg
      (QuantitativeDensity.stretchedShellScale_pos M).le _
  have hcBootLe : c ≤ cBoot := min_le_left _ _
  have hcHeightLe : c ≤ cHeight := min_le_right _ _
  have hbootExp :
      Real.exp
          (-cBoot * (QuantitativeDensity.stretchedShellScale M) ^ sigma) ≤
        Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hheightExp :
      Real.exp
          (-cHeight * (QuantitativeDensity.stretchedShellScale M) ^ sigma) ≤
        Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
    apply Real.exp_le_exp.2
    nlinarith
  calc
    shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
        shellExceptionalRatio (shellBootstrap p omega M) M +
          4 / stretchedHeightShellAllowance zeta alpha M :=
      shellExceptionalRatio_heightCertifiedShell_le_inv p M
    _ ≤ 2 * Real.exp
          (-cBoot * (QuantitativeDensity.stretchedShellScale M) ^ sigma) +
        4 * Real.exp
          (-cHeight * (QuantitativeDensity.stretchedShellScale M) ^ sigma) :=
      add_le_add hbootM hheightM
    _ ≤ 2 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) +
        4 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hbootExp (by norm_num))
        (mul_le_mul_of_nonneg_left hheightExp (by norm_num))
    _ = 6 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by ring

/-- The global exceptional count for the height-certified stretched-log set
retains the same stretched power of `log X`. -/
theorem heightCertifiedExceptionalCountEventually
    {r eta chi Dc omega zeta alpha sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≤ 1)
    (hsigmaAlpha : sigma ≤ alpha)
    (hsigmaDensity : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount (assembledHeightCertified p omega zeta alpha) X : ℝ) ≤
        13 * X * Real.exp (-c * (Real.log X) ^ sigma) := by
  obtain ⟨c0, hc0, hratio⟩ :=
    eventually_heightCertifiedShellRatioLeStretched p
      hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega0
      hzeta halpha0 hsigma0 hsigmaAlpha hsigmaDensity
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hratio
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
  have hbound :=
    QuantitativeDensity.badCount_assembleDyadic_le_stretched_log
      (heightCertifiedShell p omega zeta alpha) M0 X 6 c0 sigma
      (by norm_num) hc0 hsigma0 hsigma1
      (fun M hM => hM0 M hM) hX0 hL2 hMhalf
  change (badCount (assembleDyadic
      (heightCertifiedShell p omega zeta alpha)) X : ℝ) ≤
    13 * X * Real.exp
      (-(QuantitativeDensity.stretchedDyadicRate c0 / 2) *
        (Real.log X) ^ sigma)
  norm_num at hbound
  simpa only [neg_mul] using hbound

theorem tendsto_stretchedHeightShellAllowance_atTop
    {zeta alpha : ℝ} (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    Tendsto (stretchedHeightShellAllowance zeta alpha) atTop atTop := by
  have hscale : Tendsto (fun M : ℕ => (M : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const
      (Real.log_pos (by norm_num))
  have hpow : Tendsto
      (fun M : ℕ => (((M : ℝ) * Real.log 2) ^ alpha)) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp hscale
  have hmul : Tendsto
      (fun M : ℕ => zeta * (((M : ℝ) * Real.log 2) ^ alpha)) atTop atTop :=
    hpow.const_mul_atTop hzeta
  change Tendsto
    (fun M : ℕ => Real.exp (zeta * (((M : ℝ) * Real.log 2) ^ alpha)))
      atTop atTop
  exact Real.tendsto_exp_atTop.comp hmul

theorem tendsto_four_div_stretchedHeightShellAllowance_zero
    {zeta alpha : ℝ} (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    Tendsto (fun M : ℕ =>
      4 / stretchedHeightShellAllowance zeta alpha M) atTop (nhds 0) := by
  have h := (tendsto_const_nhds :
    Tendsto (fun _M : ℕ => (4 : ℝ)) atTop (nhds 4)).div_atTop
      (tendsto_stretchedHeightShellAllowance_atTop hzeta halpha)
  simpa using h

theorem heightCertifiedShellRatioTendstoZero
    {r eta chi Dc omega zeta alpha : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega : 0 < omega)
    (hdensity : densityGamma omega chi < 1)
    (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    Tendsto (fun M => shellExceptionalRatio
      (heightCertifiedShell p omega zeta alpha M) M) atTop (nhds 0) := by
  have hboot := shellBootstrapRatioTendstoZero p
    hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega hdensity
  have hheight :=
    tendsto_four_div_stretchedHeightShellAllowance_zero hzeta halpha
  have hsum := hboot.add hheight
  have hsum0 : Tendsto (fun M =>
      shellExceptionalRatio (shellBootstrap p omega M) M +
        4 / stretchedHeightShellAllowance zeta alpha M) atTop (nhds 0) := by
    simpa using hsum
  have hupper : ∀ M : ℕ,
      shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
        shellExceptionalRatio (shellBootstrap p omega M) M +
          4 / stretchedHeightShellAllowance zeta alpha M :=
    shellExceptionalRatio_heightCertifiedShell_le_inv p
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum0
  · filter_upwards with M
    exact shellExceptionalRatio_nonneg _ _
  · filter_upwards with M
    exact hupper M

theorem assembledHeightCertified_naturalDensityOne
    {r eta chi Dc omega zeta alpha : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega : 0 < omega)
    (hdensity : densityGamma omega chi < 1)
    (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    NaturalDensityOne (assembledHeightCertified p omega zeta alpha) := by
  exact naturalDensityOne_assembleDyadic _
    (heightCertifiedShellRatioTendstoZero p hchi0 hchir hchi1
      hDc0 hDc1 hDcRate hchiDc homega hdensity hzeta halpha)

/-- Any headline scalar package admits a narrower envelope width that meets
both the fixed raw-clock budget and the later-block relative-height budget. -/
theorem exists_rawClockHeightStageOfHeadline
    {delta : ℝ} (h : HeadlineScalars delta) :
    ∃ (eta : ℝ) (_p : StageSetup h.r eta),
      eta < h.r - a0 ∧
      rawClockLeading h.r eta < (261 / 25 : ℝ) ∧
      h.r * (1 + eta) < 1 := by
  let base := (3 / (2 * Real.log 2)) / (1 - h.r)
  let gap := (261 / 25 : ℝ) - base
  have hr0 : 0 < h.r := a0_pos.trans h.a0_lt_r
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
  let etaRaw := min ((h.r - a0) / 2)
    (gap * (1 - h.r) * Real.log 3 / 2)
  have hetaRaw0 : 0 < etaRaw := by
    dsimp [etaRaw]
    exact lt_min (by linarith [h.a0_lt_r]) (by positivity)
  let eta := min etaRaw ((1 - h.r) / (2 * h.r))
  have hcap0 : 0 < (1 - h.r) / (2 * h.r) :=
    div_pos hden (mul_pos (by norm_num) hr0)
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact lt_min hetaRaw0 hcap0
  have hetaLeRaw : eta ≤ etaRaw := by
    dsimp [eta]
    exact min_le_left _ _
  have hetaRawGap : etaRaw < h.r - a0 := by
    have hle : etaRaw ≤ (h.r - a0) / 2 := by
      dsimp [etaRaw]
      exact min_le_left _ _
    linarith [h.a0_lt_r]
  have hetaGap : eta < h.r - a0 := hetaLeRaw.trans_lt hetaRawGap
  have hetaBudget :
      eta ≤ gap * (1 - h.r) * Real.log 3 / 2 := by
    exact hetaLeRaw.trans (by
      dsimp [etaRaw]
      exact min_le_right _ _)
  have hcap : eta ≤ (1 - h.r) / (2 * h.r) := by
    dsimp [eta]
    exact min_le_right _ _
  let p : StageSetup h.r eta := Classical.choice
    (exists_stageSetup h.a0_lt_r h.r_lt_one heta0 hetaGap)
  have hextra :
      (eta / Real.log 3) / (1 - h.r) ≤ gap / 2 := by
    apply (div_le_iff₀ hden).2
    apply (div_le_iff₀ hlog3).2
    nlinarith
  have hraw : rawClockLeading h.r eta < (261 / 25 : ℝ) := by
    unfold rawClockLeading
    have hsplit :
        (3 / (2 * Real.log 2) + eta / Real.log 3) / (1 - h.r) =
          base + (eta / Real.log 3) / (1 - h.r) := by
      dsimp [base]
      ring
    rw [hsplit]
    dsimp [gap] at hextra
    linarith
  have hre : h.r * (1 + eta) < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hcap hr0.le
    have hform : h.r * ((1 - h.r) / (2 * h.r)) = (1 - h.r) / 2 := by
      field_simp [hr0.ne']
    rw [hform] at hmul
    nlinarith
  exact ⟨eta, p, hetaGap, hraw, hre⟩

/-- Shrink the raw-clock envelope width once more so that all later
fixed-barrier blocks lie below the original source scale. -/
theorem exists_rawClockHeightStage
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ (h : HeadlineScalars delta) (eta : ℝ) (_p : StageSetup h.r eta),
      eta < h.r - a0 ∧
      rawClockLeading h.r eta < (261 / 25 : ℝ) ∧
      h.r * (1 + eta) < 1 := by
  obtain ⟨h, eta0, _p0, heta0Gap, hraw0⟩ :=
    exists_rawClockStage hdelta0 hdelta1
  let eta := min eta0 ((1 - h.r) / (2 * h.r))
  have heta00 : 0 < eta0 := _p0.eta_pos
  have hr0 : 0 < h.r := a0_pos.trans h.a0_lt_r
  have hr1 : h.r < 1 := h.r_lt_one
  have hcap0 : 0 < (1 - h.r) / (2 * h.r) :=
    div_pos (sub_pos.mpr hr1) (mul_pos (by norm_num) hr0)
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min heta00 hcap0
  have hetaLe : eta ≤ eta0 := by
    dsimp [eta]
    exact min_le_left _ _
  have hetaGap : eta < h.r - a0 := hetaLe.trans_lt heta0Gap
  have hrawLe : rawClockLeading h.r eta ≤ rawClockLeading h.r eta0 := by
    unfold rawClockLeading
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hden : 0 < 1 - h.r := sub_pos.mpr hr1
    apply (div_le_div_iff_of_pos_right hden).2
    have hetaDiv : eta / Real.log 3 ≤ eta0 / Real.log 3 :=
      (div_le_div_iff_of_pos_right hlog3).2 hetaLe
    linarith
  have hcap : eta ≤ (1 - h.r) / (2 * h.r) := by
    dsimp [eta]
    exact min_le_right _ _
  have hre : h.r * (1 + eta) < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hcap hr0.le
    have hform : h.r * ((1 - h.r) / (2 * h.r)) = (1 - h.r) / 2 := by
      field_simp [hr0.ne']
    rw [hform] at hmul
    nlinarith
  let p : StageSetup h.r eta := Classical.choice
    (exists_stageSetup h.a0_lt_r h.r_lt_one heta hetaGap)
  exact ⟨h, eta, p, hetaGap, hrawLe.trans_lt hraw0, hre⟩

theorem stretchedHeightShellAllowance_le_source
    {zeta alpha : ℝ} (hzeta : 0 ≤ zeta) (halpha : 0 ≤ alpha)
    {M n : ℕ} (hn : n ∈ dyadicShell M) :
    stretchedHeightShellAllowance zeta alpha M ≤
      Real.exp (zeta * (Real.log n) ^ alpha) := by
  have hlower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hn).1
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M) hlower
    rw [Real.log_pow] at h
    exact h
  have hbase0 : 0 ≤ (M : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg M)
      (Real.log_pos (by norm_num)).le
  have hpowLe : ((M : ℝ) * Real.log 2) ^ alpha ≤
      (Real.log n) ^ alpha :=
    Real.rpow_le_rpow hbase0 hlogLower halpha
  unfold stretchedHeightShellAllowance
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpowLe hzeta)

theorem eventually_four_le_stretchedHeightShellAllowance
    {zeta alpha : ℝ} (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    ∀ᶠ M : ℕ in atTop, 4 ≤ stretchedHeightShellAllowance zeta alpha M :=
  (tendsto_atTop.1
    (tendsto_stretchedHeightShellAllowance_atTop hzeta halpha)) 4

/-- Density-one stretched-logarithmic descent with one common shortcut/raw
landing and the smaller common relative-height allowance
`n * exp (zeta * (log n)^alpha)`.  This is the qualitative fixed-clock
specialization; the strict-exponent quantitative form follows below. -/
theorem stretchedLogCommonLandingWithRelativeHeight
    {delta zeta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hzeta : 0 < zeta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ k ell : ℕ,
              (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
              (ell : ℝ) < (261 / 25 : ℝ) * Real.log n ∧
              orbit k n = rawOrbit ell n ∧
              (orbit k n : ℝ) ≤
                Real.exp ((Real.log n) ^ (1 - delta)) ∧
              (∀ j : ℕ, j ≤ k →
                (orbit j n : ℝ) ≤
                  (n : ℝ) * Real.exp
                    (zeta * (Real.log n) ^ (1 - delta))) ∧
              (∀ i : ℕ, i ≤ ell →
                (rawOrbit i n : ℝ) ≤
                  (n : ℝ) * Real.exp
                    (zeta * (Real.log n) ^ (1 - delta))) := by
  obtain ⟨h, eta, p, hetaGap, hrawLeading, hre⟩ :=
    exists_rawClockHeightStage hdelta0 hdelta1
  let alpha := 1 - delta
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
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
  let S := assembledHeightCertified p h.omega zeta alpha
  have hSdense : NaturalDensityOne S :=
    assembledHeightCertified_naturalDensityOne p
      h.chi_pos h.chi_lt_r h.chi_le_one hDc0 hDc1 le_rfl hchiDc
      h.omega_pos hdensity hzeta halpha
  have hlandingM := eventuallyShellLanding p h.omega_pos hdelta1 hdescent
  have hclockM := eventuallyShellClockLt6953 p h.r_lt_clock h.omega_pos
  have hrawM := eventuallyShellRawClockLt p h.omega_pos hrawLeading
  have hheightCore :=
    eventuallyShellBootstrapRelativeHeight p h.omega_pos hre.le
  have hH4 := eventually_four_le_stretchedHeightShellAllowance hzeta halpha
  have hheightM : ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ heightCertifiedShell p h.omega zeta alpha M →
      (∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M / 2) ∧
      (∀ i : ℕ,
        i ≤ rawTime n (stageClock p (stageCount h.omega M) n) →
        (rawOrbit i n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M) := by
    filter_upwards [hheightCore, hH4] with M hheight hH
    intro n hn hnshell hncert
    exact hheight n (stretchedHeightShellAllowance zeta alpha M)
      hn hnshell hncert.1 hH hncert.2
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageOrbit p (stageCount h.omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageClock p (stageCount h.omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  have hraw := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (rawTime n (stageClock p (stageCount h.omega M) n) : ℝ) <
        (261 / 25 : ℝ) * Real.log n) hrawM
  have hheight := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ heightCertifiedShell p h.omega zeta alpha M →
      (∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M / 2) ∧
      (∀ i : ℕ,
        i ≤ rawTime n (stageClock p (stageCount h.omega M) n) →
        (rawOrbit i n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M)) hheightM
  refine ⟨S, hSdense, ?_⟩
  filter_upwards [hlanding, hclock, hraw, hheight,
    eventually_gt_atTop (0 : ℕ)] with n hlanding hclock hraw hheight hn hnS
  have hncert :
      n ∈ heightCertifiedShell p h.omega zeta alpha (Nat.log 2 n) := hnS
  have hnboot : n ∈ bootstrapSet p
      (stageCount h.omega (Nat.log 2 n)) := hncert.1
  let k := stageClock p (stageCount h.omega (Nat.log 2 n)) n
  let ell := rawTime n k
  have hallow := stretchedHeightShellAllowance_le_source
    hzeta.le halpha.le (mem_dyadicShell_log hn)
  have hheights := hheight hn hncert
  refine ⟨k, ell, hclock hn hnboot, hraw hn hnboot, ?_, ?_, ?_, ?_⟩
  · exact (rawOrbit_rawTime_eq_orbit n k).symm
  · rw [← stageOrbit_eq_orbit_stageClock]
    exact hlanding hn hnboot
  · intro j hj
    have hj' := hheights.1 j hj
    calc
      (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha
            (Nat.log 2 n) / 2 := hj'
      _ ≤ (n : ℝ) * stretchedHeightShellAllowance zeta alpha
          (Nat.log 2 n) := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        have hH0 : 0 ≤ stretchedHeightShellAllowance zeta alpha
            (Nat.log 2 n) := by
          unfold stretchedHeightShellAllowance
          positivity
        nlinarith
      _ ≤ (n : ℝ) * Real.exp (zeta * (Real.log n) ^ (1 - delta)) := by
        dsimp [alpha] at hallow ⊢
        exact mul_le_mul_of_nonneg_left hallow (by positivity)
  · intro i hi
    have hi' := hheights.2 i hi
    exact hi'.trans (by
      dsimp [alpha] at hallow ⊢
      exact mul_le_mul_of_nonneg_left hallow (by positivity))

/-- Quantitative common-landing stretched-logarithmic descent with the
smaller relative-height allowance.  Every strict exceptional exponent
`sigma < 1 - delta` is retained. -/
theorem stretchedLogCommonLandingWithRelativeHeightQuantitative
    {delta sigma zeta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 - delta)
    (hzeta : 0 < zeta) :
    ∃ S : Set ℕ, ∃ c : ℝ,
      0 < c ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤
          13 * X * Real.exp (-c * (Real.log X) ^ sigma)) ∧
      (∀ᶠ n : ℕ in atTop,
        n ∈ S →
          ∃ k ell : ℕ,
            (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
            (ell : ℝ) < (261 / 25 : ℝ) * Real.log n ∧
            orbit k n = rawOrbit ell n ∧
            (orbit k n : ℝ) ≤
              Real.exp ((Real.log n) ^ (1 - delta)) ∧
            (∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤
                (n : ℝ) * Real.exp
                  (zeta * (Real.log n) ^ (1 - delta))) ∧
            (∀ i : ℕ, i ≤ ell →
              (rawOrbit i n : ℝ) ≤
                (n : ℝ) * Real.exp
                  (zeta * (Real.log n) ^ (1 - delta)))) := by
  let h : QuantitativeHeadlineScalars delta sigma :=
    Classical.choice
      (exists_quantitativeHeadlineScalars hdelta0 hsigma0 hsigma)
  obtain ⟨eta, p, hetaGap, hrawLeading, hre⟩ :=
    exists_rawClockHeightStageOfHeadline h.toHeadlineScalars
  let alpha := 1 - delta
  have halpha0 : 0 < alpha := by dsimp [alpha]; linarith
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
  have hdensityMargin : sigma < 1 - densityGamma h.omega h.chi := by
    simpa [densityGamma, one_div, add_comm] using h.density_margin
  let S := assembledHeightCertified p h.omega zeta alpha
  obtain ⟨c, hc, hcount⟩ :=
    heightCertifiedExceptionalCountEventually p
      h.chi_pos h.chi_lt_r h.chi_le_one hDc0 hDc1 le_rfl hchiDc
      h.omega_pos hzeta halpha0 hsigma0
      (by linarith)
      (by dsimp [alpha]; exact hsigma.le)
      hdensityMargin
  have hlandingM := eventuallyShellLanding p h.omega_pos hdelta1 hdescent
  have hclockM := eventuallyShellClockLt6953 p h.r_lt_clock h.omega_pos
  have hrawM := eventuallyShellRawClockLt p h.omega_pos hrawLeading
  have hheightCore :=
    eventuallyShellBootstrapRelativeHeight p h.omega_pos hre.le
  have hH4 := eventually_four_le_stretchedHeightShellAllowance hzeta halpha0
  have hheightM : ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ heightCertifiedShell p h.omega zeta alpha M →
      (∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M / 2) ∧
      (∀ i : ℕ,
        i ≤ rawTime n (stageClock p (stageCount h.omega M) n) →
        (rawOrbit i n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M) := by
    filter_upwards [hheightCore, hH4] with M hheight hH
    intro n hn hnshell hncert
    exact hheight n (stretchedHeightShellAllowance zeta alpha M)
      hn hnshell hncert.1 hH hncert.2
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageOrbit p (stageCount h.omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageClock p (stageCount h.omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  have hraw := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (rawTime n (stageClock p (stageCount h.omega M) n) : ℝ) <
        (261 / 25 : ℝ) * Real.log n) hrawM
  have hheight := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ heightCertifiedShell p h.omega zeta alpha M →
      (∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M / 2) ∧
      (∀ i : ℕ,
        i ≤ rawTime n (stageClock p (stageCount h.omega M) n) →
        (rawOrbit i n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M)) hheightM
  refine ⟨S, c, hc, hcount, ?_⟩
  filter_upwards [hlanding, hclock, hraw, hheight,
    eventually_gt_atTop (0 : ℕ)] with n hlanding hclock hraw hheight hn hnS
  have hncert :
      n ∈ heightCertifiedShell p h.omega zeta alpha (Nat.log 2 n) := hnS
  have hnboot : n ∈ bootstrapSet p
      (stageCount h.omega (Nat.log 2 n)) := hncert.1
  let k := stageClock p (stageCount h.omega (Nat.log 2 n)) n
  let ell := rawTime n k
  have hallow := stretchedHeightShellAllowance_le_source
    hzeta.le halpha0.le (mem_dyadicShell_log hn)
  have hheights := hheight hn hncert
  refine ⟨k, ell, hclock hn hnboot, hraw hn hnboot, ?_, ?_, ?_, ?_⟩
  · exact (rawOrbit_rawTime_eq_orbit n k).symm
  · rw [← stageOrbit_eq_orbit_stageClock]
    exact hlanding hn hnboot
  · intro j hj
    have hj' := hheights.1 j hj
    calc
      (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha
            (Nat.log 2 n) / 2 := hj'
      _ ≤ (n : ℝ) * stretchedHeightShellAllowance zeta alpha
          (Nat.log 2 n) := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        have hH0 : 0 ≤ stretchedHeightShellAllowance zeta alpha
            (Nat.log 2 n) := by
          unfold stretchedHeightShellAllowance
          positivity
        nlinarith
      _ ≤ (n : ℝ) * Real.exp (zeta * (Real.log n) ^ (1 - delta)) := by
        dsimp [alpha] at hallow ⊢
        exact mul_le_mul_of_nonneg_left hallow (by positivity)
  · intro i hi
    calc
      (rawOrbit i n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha
            (Nat.log 2 n) := hheights.2 i hi
      _ ≤ (n : ℝ) * Real.exp (zeta * (Real.log n) ^ (1 - delta)) := by
        dsimp [alpha] at hallow ⊢
        exact mul_le_mul_of_nonneg_left hallow (by positivity)

end

end FirstPassageLinearTransport
