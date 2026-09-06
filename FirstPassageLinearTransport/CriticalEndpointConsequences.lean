/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutEndpointNaturalDensity
import FirstPassageLinearTransport.PolylogExceptionalCount

/-!
# Public consequences of the sharp timeout endpoint

This module begins the referee-facing Version 4 consumer layer.  It chooses
the high-rank polynomial error exponent independently of the moving terminal
schedule and specializes the relative-height allowance to a fixed power of
the dyadic shell rank.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Every dyadic shell is nonempty. -/
theorem dyadicShell_nonempty (M : ℕ) : (dyadicShell M).Nonempty := by
  refine ⟨2 ^ M, mem_dyadicShell.mpr ⟨le_rfl, ?_⟩⟩
  rw [pow_succ]
  have hpos : 0 < 2 ^ M := pow_pos (by omega) _
  omega

/-- Minimum of a real-valued function on the finite `M`-th dyadic shell. -/
def dyadicShellMinimum (U : ℕ → ℝ) (M : ℕ) : ℝ :=
  ((dyadicShell M).image U).min' ((dyadicShell_nonempty M).image U)

theorem dyadicShellMinimum_le_of_mem
    (U : ℕ → ℝ) {M n : ℕ} (hn : n ∈ dyadicShell M) :
    dyadicShellMinimum U M ≤ U n := by
  unfold dyadicShellMinimum
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)

theorem le_dyadicShellMinimum
    (U : ℕ → ℝ) (M : ℕ) {b : ℝ}
    (hU : ∀ n ∈ dyadicShell M, b ≤ U n) :
    b ≤ dyadicShellMinimum U M := by
  unfold dyadicShellMinimum
  apply Finset.le_min'
  intro y hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  exact hU n hn

/-- Shell minima preserve divergence and require no monotonicity of the
original function. -/
theorem tendsto_dyadicShellMinimum_atTop
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    Tendsto (dyadicShellMinimum U) atTop atTop := by
  rw [tendsto_atTop] at hU ⊢
  intro b
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hU b)
  have hpowT : Tendsto (fun M : ℕ => 2 ^ M) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpow := (tendsto_atTop.1 hpowT) N
  filter_upwards [hpow] with M hMN
  apply le_dyadicShellMinimum U M
  intro n hn
  exact hN n (hMN.trans (mem_dyadicShell.mp hn).1)

theorem dyadicShellMinimum_pos
    {U : ℕ → ℝ} (hU : ∀ n, 0 < U n) (M : ℕ) :
    0 < dyadicShellMinimum U M := by
  unfold dyadicShellMinimum
  have hmem := Finset.min'_mem ((dyadicShell M).image U)
    ((dyadicShell_nonempty M).image U)
  obtain ⟨n, _hn, heq⟩ := Finset.mem_image.mp hmem
  rw [← heq]
  exact hU n

/-- A slowly growing shell multiplier.  The square root absorbs every fixed
constant, while the shell-rank clip keeps the induced exponent bounded. -/
def clippedCriticalMultiplier (U : ℕ → ℝ) (M : ℕ) : ℝ :=
  min (Real.sqrt (dyadicShellMinimum U M)) ((M : ℝ) + 2)

theorem clippedCriticalMultiplier_pos
    {U : ℕ → ℝ} (hU : ∀ n, 0 < U n) (M : ℕ) :
    0 < clippedCriticalMultiplier U M := by
  unfold clippedCriticalMultiplier
  exact lt_min
    (Real.sqrt_pos.2 (dyadicShellMinimum_pos hU M)) (by positivity)

theorem tendsto_sqrt_dyadicShellMinimum_atTop
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    Tendsto (fun M => Real.sqrt (dyadicShellMinimum U M)) atTop atTop := by
  have hminT := tendsto_dyadicShellMinimum_atTop hU
  rw [tendsto_atTop] at hminT ⊢
  intro b
  let b₀ := max b 0
  have hb₀ : 0 ≤ b₀ := le_max_right _ _
  have hlarge := hminT (b₀ ^ 2)
  filter_upwards [hlarge] with M hM
  have hmin0 : 0 ≤ dyadicShellMinimum U M :=
    (sq_nonneg b₀).trans hM
  have hsqrtSq := Real.sq_sqrt hmin0
  have hsqrt0 := Real.sqrt_nonneg (dyadicShellMinimum U M)
  have hb : b ≤ b₀ := le_max_left _ _
  nlinarith

theorem tendsto_clippedCriticalMultiplier_atTop
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    Tendsto (clippedCriticalMultiplier U) atTop atTop := by
  have hleft := tendsto_sqrt_dyadicShellMinimum_atTop hU
  have hright : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  rw [tendsto_atTop] at hleft hright ⊢
  intro b
  filter_upwards [hleft b, hright b] with M hL hR
  exact le_min hL hR

/-- Shellwise relative-height allowance clipped only to preserve a simple
sublinear scalar profile. -/
def clippedShellHeight (R : ℕ → ℝ) (M : ℕ) : ℝ :=
  min (dyadicShellMinimum R M) ((M : ℝ) + 2)

theorem tendsto_clippedShellHeight_atTop
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (clippedShellHeight R) atTop atTop := by
  have hleft := tendsto_dyadicShellMinimum_atTop hR
  have hright : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  rw [tendsto_atTop] at hleft hright ⊢
  intro b
  filter_upwards [hleft b, hright b] with M hL hR
  exact le_min hL hR

/-- Integer terminal rank for the critical exponent with one clipped
divergent multiplier. -/
def criticalMultiplierTerminalRank (U : ℕ → ℝ) (M : ℕ) : ℕ :=
  ⌈timeSupportCriticalExponent * Real.logb 2 ((M : ℝ) + 2) +
    Real.logb 2 (clippedCriticalMultiplier U M)⌉₊

/-- Bounded shell exponent realizing `criticalMultiplierTerminalRank`
exactly through `movingTerminalRank`. -/
def criticalMultiplierExponent (U : ℕ → ℝ) (M : ℕ) : ℝ :=
  (criticalMultiplierTerminalRank U M : ℝ) /
    Real.logb 2 ((M : ℝ) + 2)

theorem movingTerminalRank_criticalMultiplierExponent
    (U : ℕ → ℝ) (M : ℕ) :
    movingTerminalRank (criticalMultiplierExponent U) M =
      criticalMultiplierTerminalRank U M := by
  have hlogb : 0 < Real.logb 2 ((M : ℝ) + 2) := by
    apply Real.logb_pos (by norm_num)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  rw [movingTerminalRank, criticalMultiplierExponent]
  field_simp [ne_of_gt hlogb]
  simp

theorem firstPassageEntropyGap_mul_timeSupportCriticalExponent :
    firstPassageEntropyGap * timeSupportCriticalExponent = 1 / 2 := by
  have hgap := firstPassageEntropyGap_pos
  have hcrit :
      timeSupportCriticalExponent = 1 / (2 * firstPassageEntropyGap) := by
    rw [timeSupportCriticalExponent_eq_entropy]
    rfl
  rw [hcrit]
  field_simp [ne_of_gt hgap]

/-- The critical multiplier pays the sharp buffer directly. -/
theorem sharpMovingRankBuffer_criticalMultiplierExponent_ge
    {U : ℕ → ℝ} (hU : ∀ n, 0 < U n) (M : ℕ) :
    firstPassageEntropyGap *
        Real.logb 2 (clippedCriticalMultiplier U M) ≤
      sharpMovingRankBuffer (criticalMultiplierExponent U) M := by
  let x : ℝ := (M : ℝ) + 2
  let w : ℝ := clippedCriticalMultiplier U M
  have hw : 0 < w := by simpa [w] using clippedCriticalMultiplier_pos hU M
  have hx : 0 < x := by dsimp [x]; positivity
  have htotal :
      timeSupportCriticalExponent * Real.logb 2 x + Real.logb 2 w ≤
        (criticalMultiplierTerminalRank U M : ℝ) := by
    simpa [criticalMultiplierTerminalRank, x, w] using
      (Nat.le_ceil (timeSupportCriticalExponent * Real.logb 2 x +
        Real.logb 2 w))
  have hmul := mul_le_mul_of_nonneg_left htotal firstPassageEntropyGap_pos.le
  rw [sharpMovingRankBuffer_eq,
    movingTerminalRank_criticalMultiplierExponent]
  dsimp [x, w] at hmul ⊢
  rw [mul_add] at hmul
  have hid : firstPassageEntropyGap *
      (timeSupportCriticalExponent * Real.logb 2 ((M : ℝ) + 2)) =
        (1 / 2) * Real.logb 2 ((M : ℝ) + 2) := by
    rw [← mul_assoc,
      firstPassageEntropyGap_mul_timeSupportCriticalExponent]
  rw [hid] at hmul
  linarith

theorem tendsto_sharpMovingRankBuffer_criticalMultiplierExponent
    {U : ℕ → ℝ} (hUpos : ∀ n, 0 < U n)
    (hU : Tendsto U atTop atTop) :
    Tendsto (sharpMovingRankBuffer (criticalMultiplierExponent U))
      atTop atTop := by
  have hwT := tendsto_clippedCriticalMultiplier_atTop hU
  have hlogT : Tendsto
      (fun M => Real.logb 2 (clippedCriticalMultiplier U M)) atTop atTop :=
    Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2) |>.comp hwT
  have hlowerT : Tendsto
      (fun M => firstPassageEntropyGap *
        Real.logb 2 (clippedCriticalMultiplier U M)) atTop atTop :=
    hlogT.const_mul_atTop firstPassageEntropyGap_pos
  rw [tendsto_atTop] at hlowerT ⊢
  intro B
  filter_upwards [hlowerT B] with M hM
  exact hM.trans
    (sharpMovingRankBuffer_criticalMultiplierExponent_ge hUpos M)

/-- The clipped multiplier induces an eventually bounded exponent sequence. -/
theorem eventually_criticalMultiplierExponent_le
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      criticalMultiplierExponent U M < timeSupportCriticalExponent + 2 := by
  have hwT := tendsto_clippedCriticalMultiplier_atTop hU
  have hw1 : ∀ᶠ M : ℕ in atTop, 1 ≤ clippedCriticalMultiplier U M :=
    (tendsto_atTop.1 hwT) 1
  filter_upwards [hw1] with M hw1
  let x : ℝ := (M : ℝ) + 2
  let w : ℝ := clippedCriticalMultiplier U M
  have hx2 : 2 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_left (Nat.cast_nonneg M)
  have hx : 0 < x := zero_lt_two.trans_le hx2
  have hw : 0 < w := zero_lt_one.trans_le hw1
  have hlogx : 0 < Real.logb 2 x :=
    Real.logb_pos (by norm_num) (by linarith)
  have hlogx1 : 1 ≤ Real.logb 2 x := by
    have := Real.logb_le_logb_of_le (b := (2 : ℝ))
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) hx2
    simpa using this
  have hwle : w ≤ x := by
    dsimp [w, clippedCriticalMultiplier]
    exact min_le_right _ _
  have hlogw : Real.logb 2 w ≤ Real.logb 2 x :=
    Real.logb_le_logb_of_le (b := (2 : ℝ))
      (by norm_num : (1 : ℝ) < 2) hw hwle
  have htotal0 : 0 ≤
      timeSupportCriticalExponent * Real.logb 2 x + Real.logb 2 w := by
    have hlogw0 : 0 ≤ Real.logb 2 w :=
      Real.logb_nonneg (by norm_num) hw1
    exact add_nonneg
      (mul_nonneg timeSupportCriticalExponent_pos.le hlogx.le) hlogw0
  have hceil : (criticalMultiplierTerminalRank U M : ℝ) <
      timeSupportCriticalExponent * Real.logb 2 x + Real.logb 2 w + 1 := by
    simpa [criticalMultiplierTerminalRank, x, w] using
      (Nat.ceil_lt_add_one htotal0)
  have hrank : (criticalMultiplierTerminalRank U M : ℝ) <
      (timeSupportCriticalExponent + 2) * Real.logb 2 x := by
    calc
      (criticalMultiplierTerminalRank U M : ℝ) <
          timeSupportCriticalExponent * Real.logb 2 x +
            Real.logb 2 w + 1 := hceil
      _ ≤ (timeSupportCriticalExponent + 2) * Real.logb 2 x := by
        nlinarith
  rw [criticalMultiplierExponent]
  exact (div_lt_iff₀ hlogx).2 (by simpa [x] using hrank)

theorem criticalMultiplierExponent_nonneg (U : ℕ → ℝ) (M : ℕ) :
    0 ≤ criticalMultiplierExponent U M := by
  unfold criticalMultiplierExponent
  have hlogb : 0 < Real.logb 2 ((M : ℝ) + 2) := by
    apply Real.logb_pos (by norm_num)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  positivity

/-- The exponent representation is exact: raising the shifted shell rank to
the induced exponent gives the chosen integer power of two. -/
theorem shellRank_rpow_criticalMultiplierExponent
    (U : ℕ → ℝ) (M : ℕ) :
    (((M : ℝ) + 2) ^ (criticalMultiplierExponent U M)) =
      (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) := by
  let x : ℝ := (M : ℝ) + 2
  let L : ℕ := criticalMultiplierTerminalRank U M
  have hx : 0 < x := by dsimp [x]; positivity
  have hlogb : 0 < Real.logb 2 x := by
    apply Real.logb_pos (by norm_num)
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  calc
    x ^ (criticalMultiplierExponent U M) =
        ((2 : ℝ) ^ (Real.logb 2 x)) ^
          ((L : ℝ) / Real.logb 2 x) := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) hx]
      rfl
    _ = (2 : ℝ) ^ (Real.logb 2 x *
          ((L : ℝ) / Real.logb 2 x)) := by
      rw [Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (L : ℝ) := by
      field_simp [ne_of_gt hlogb]
    _ = (2 : ℝ) ^ L := by rw [Real.rpow_natCast]

/-- On its source shell, the induced polylogarithmic target is bounded by
the selected integer terminal scale. -/
theorem shellLog_rpow_criticalMultiplierExponent_le
    (U : ℕ → ℝ) {M n : ℕ} (hM : 1 ≤ M)
    (hnShell : n ∈ dyadicShell M) :
    (Real.log n) ^ (criticalMultiplierExponent U M) ≤
      (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) := by
  let x : ℝ := (M : ℝ) + 2
  have hn : 0 < n := by
    have hnLower := (mem_dyadicShell.mp hnShell).1
    have : 0 < 2 ^ M := pow_pos (by omega) _
    omega
  have hnUpperR : (n : ℝ) < ((2 ^ (M + 1) : ℕ) : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hnShell).2
  have hlogUpper := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by exact_mod_cast hn : (0 : ℝ) < n))
    (Set.mem_Ioi.mpr
      (by positivity : (0 : ℝ) < ((2 ^ (M + 1) : ℕ) : ℝ))) hnUpperR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlogUpper
  rw [Real.log_pow] at hlogUpper
  push_cast at hlogUpper
  have hlogTwoLt : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hlogx : Real.log n ≤ x := by
    dsimp [x]
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hlogn0 : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hpow := Real.rpow_le_rpow hlogn0 hlogx
    (criticalMultiplierExponent_nonneg U M)
  calc
    (Real.log n) ^ (criticalMultiplierExponent U M) ≤
        x ^ (criticalMultiplierExponent U M) := hpow
    _ = (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) := by
      simpa [x] using shellRank_rpow_criticalMultiplierExponent U M

/-- The chosen integer scale is at most one factor two above the critical
rank times the clipped multiplier. -/
theorem two_pow_criticalMultiplierTerminalRank_lt
    {U : ℕ → ℝ} (hUpos : ∀ n, 0 < U n) {M : ℕ}
    (hw1 : 1 ≤ clippedCriticalMultiplier U M) :
    (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) <
      2 * (((M : ℝ) + 2) ^ timeSupportCriticalExponent) *
        clippedCriticalMultiplier U M := by
  let x : ℝ := (M : ℝ) + 2
  let w : ℝ := clippedCriticalMultiplier U M
  have hx : 0 < x := by dsimp [x]; positivity
  have hw : 0 < w := by simpa [w] using clippedCriticalMultiplier_pos hUpos M
  have hlogx0 : 0 ≤ Real.logb 2 x := by
    apply Real.logb_nonneg (by norm_num)
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlogw0 : 0 ≤ Real.logb 2 w :=
    Real.logb_nonneg (by norm_num) (by simpa [w] using hw1)
  have htotal0 : 0 ≤
      timeSupportCriticalExponent * Real.logb 2 x + Real.logb 2 w :=
    add_nonneg (mul_nonneg timeSupportCriticalExponent_pos.le hlogx0) hlogw0
  have hceil := Nat.ceil_lt_add_one htotal0
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt
    (by norm_num : (1 : ℝ) < 2) hceil
  calc
    (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) <
        (2 : ℝ) ^
          (timeSupportCriticalExponent * Real.logb 2 x +
            Real.logb 2 w + 1) := by
      rw [← Real.rpow_natCast]
      simpa [criticalMultiplierTerminalRank, x, w] using hrpow
    _ = 2 * (x ^ timeSupportCriticalExponent) * w := by
      rw [show timeSupportCriticalExponent * Real.logb 2 x =
          Real.logb 2 x * timeSupportCriticalExponent by ring,
        Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
        Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hx,
        Real.rpow_logb (by norm_num) (by norm_num) hw,
        Real.rpow_one]
      ring
    _ = 2 * (((M : ℝ) + 2) ^ timeSupportCriticalExponent) *
        clippedCriticalMultiplier U M := by rfl

theorem clippedCriticalMultiplier_le_sqrt
    (U : ℕ → ℝ) (M : ℕ) :
    clippedCriticalMultiplier U M ≤
      Real.sqrt (dyadicShellMinimum U M) := by
  exact min_le_left _ _

theorem clippedShellHeight_pos
    {R : ℕ → ℝ} (hR : ∀ n, 0 < R n) (M : ℕ) :
    0 < clippedShellHeight R M := by
  unfold clippedShellHeight
  exact lt_min (dyadicShellMinimum_pos hR M) (by positivity)

theorem clippedShellHeight_le_of_mem
    (R : ℕ → ℝ) {M n : ℕ} (hn : n ∈ dyadicShell M) :
    clippedShellHeight R M ≤ R n :=
  (min_le_left _ _).trans (dyadicShellMinimum_le_of_mem R hn)

/-- The exact shell-power margin at a fixed exponent. -/
def fixedSharpEndpointMargin (A : ℝ) : ℝ :=
  firstPassageEntropyGap * A - 1 / 2

/-- Every exponent strictly above the first-passage threshold has a positive
sharp shell-power margin. -/
theorem fixedSharpEndpointMargin_pos {A : ℝ}
    (hA : timeSupportCriticalExponent < A) :
    0 < fixedSharpEndpointMargin A := by
  have hgap := firstPassageEntropyGap_pos
  have hcrit :
      timeSupportCriticalExponent = 1 / (2 * firstPassageEntropyGap) := by
    rw [timeSupportCriticalExponent_eq_entropy]
    rfl
  rw [hcrit] at hA
  unfold fixedSharpEndpointMargin
  have hden : 0 < 2 * firstPassageEntropyGap := by positivity
  have hmul := (div_lt_iff₀ hden).mp hA
  nlinarith

/-- For a fixed exponent, the integer terminal-rank ceiling can only enlarge
the sharp critical buffer. -/
theorem sharpMovingRankBuffer_const_ge
    (A : ℝ) (M : ℕ) :
    fixedSharpEndpointMargin A * Real.logb 2 ((M : ℝ) + 2) ≤
      sharpMovingRankBuffer (fun _ => A) M := by
  let x : ℝ := (M : ℝ) + 2
  have hceil : A * Real.logb 2 x ≤
      (movingTerminalRank (fun _ => A) M : ℝ) := by
    simpa [movingTerminalRank, x] using
      (Nat.le_ceil (A * Real.logb 2 x))
  have hmul := mul_le_mul_of_nonneg_left hceil firstPassageEntropyGap_pos.le
  rw [sharpMovingRankBuffer_eq]
  unfold fixedSharpEndpointMargin
  dsimp [x] at hmul ⊢
  linarith

/-- The fixed-exponent sharp buffer diverges precisely above the critical
first-passage exponent. -/
theorem tendsto_sharpMovingRankBuffer_const_atTop
    {A : ℝ} (hA : timeSupportCriticalExponent < A) :
    Tendsto (sharpMovingRankBuffer (fun _ => A)) atTop atTop := by
  have hq : 0 < fixedSharpEndpointMargin A :=
    fixedSharpEndpointMargin_pos hA
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hlogT : Tendsto
      (fun M : ℕ => Real.logb 2 ((M : ℝ) + 2)) atTop atTop :=
    Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2) |>.comp hxT
  have hlowerT : Tendsto
      (fun M : ℕ => fixedSharpEndpointMargin A *
        Real.logb 2 ((M : ℝ) + 2)) atTop atTop :=
    hlogT.const_mul_atTop hq
  rw [tendsto_atTop] at hlowerT ⊢
  intro B
  filter_upwards [hlowerT B] with M hM
  exact hM.trans (sharpMovingRankBuffer_const_ge A M)

/-- The sharp timeout term at a fixed exponent is bounded by the exact
negative power dictated by the endpoint margin. -/
theorem two_rpow_neg_sharpMovingRankBuffer_const_le
    {A : ℝ} (_hA : timeSupportCriticalExponent < A) (M : ℕ) :
    (2 : ℝ) ^ (-(sharpMovingRankBuffer (fun _ => A) M)) ≤
      (((M : ℝ) + 2) ^ (-(fixedSharpEndpointMargin A))) := by
  let x : ℝ := (M : ℝ) + 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hbuf := sharpMovingRankBuffer_const_ge A M
  have hrpow :
      (2 : ℝ) ^ (-(sharpMovingRankBuffer (fun _ => A) M)) ≤
        (2 : ℝ) ^ (-(fixedSharpEndpointMargin A * Real.logb 2 x)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [x] at hbuf ⊢
    linarith
  calc
    (2 : ℝ) ^ (-(sharpMovingRankBuffer (fun _ => A) M))
        ≤ (2 : ℝ) ^ (-(fixedSharpEndpointMargin A *
            Real.logb 2 x)) := hrpow
    _ = (2 : ℝ) ^ (Real.logb 2 x *
          (-(fixedSharpEndpointMargin A))) := by congr 1 <;> ring
    _ = ((2 : ℝ) ^ (Real.logb 2 x)) ^
          (-(fixedSharpEndpointMargin A)) := by
        rw [Real.rpow_mul (by norm_num)]
    _ = x ^ (-(fixedSharpEndpointMargin A)) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) hx]
    _ = (((M : ℝ) + 2) ^ (-(fixedSharpEndpointMargin A))) := rfl

/-- Every positive power of the shifted shell rank tends to infinity. -/
theorem tendsto_shellRankRpow_atTop {N : ℝ} (hN : 0 < N) :
    Tendsto (fun M : ℕ => ((M : ℝ) + 2) ^ N) atTop atTop := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_atTop hN).comp hxT

/-- Sharp moving-endpoint conclusion with an independently prescribed
polynomial shell error and relative-height allowance.  Shortcut and raw
times reach the same physical state and are centered on their respective
mean drifts. -/
theorem moving_polylogarithmic_common_landing_centered_clocks
    {A : ℕ → ℝ} {Amax c beta N : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hN : 0 < N)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ S : Set ℕ, ∃ C : ℝ,
      0 < C ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-N)))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N)) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N))) := by
  obtain ⟨P, hPeps⟩ :=
    exists_movingEndpointParameterPackage_epsilon_gt
      hAmax hc hbeta hN
  let R : ℕ → ℝ := fun M => ((M : ℝ) + 2) ^ N
  have hRT : Tendsto R atTop atTop := by
    simpa [R] using tendsto_shellRankRpow_atTop hN
  obtain ⟨S, C₀, hC₀, hDense, hShell, hWitness⟩ :=
    timeoutStrengthenedEndpointNaturalDensityDescentOfPackage
      P hbuffer hUpper hRT
  let C := C₀ + 4
  have hC : 0 < C := by dsimp [C]; linarith
  have hShell' : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-N))) := by
    filter_upwards [hShell] with M hShell
    let x : ℝ := (M : ℝ) + 2
    have hx1 : 1 ≤ x := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      dsimp [x]
      linarith
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    have hpow : x ^ (-P.epsilon) ≤ x ^ (-N) := by
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hheight : 4 / R M = 4 * x ^ (-N) := by
      dsimp [R, x]
      rw [Real.rpow_neg (by positivity)]
      rfl
    have ha0 : 0 ≤ (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) := by positivity
    have hb0 : 0 ≤ x ^ (-N) := Real.rpow_nonneg hx0 _
    have hbE0 : 0 ≤ x ^ (-P.epsilon) := Real.rpow_nonneg hx0 _
    rw [hheight] at hShell
    dsimp [C]
    dsimp [R, x] at hShell ⊢
    nlinarith [hC₀.le]
  have hWitness' : ∀ᶠ n : ℕ in atTop, n ∈ S →
      ∃ k ell : ℕ,
        (k : ℝ) < c * Real.log n ∧
        |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        ell = rawTime n k ∧
        rawOrbit ell n = orbit k n ∧
        (orbit k n : ℝ) <
          C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤
            (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N)) ∧
        (∀ i : ℕ, i ≤ ell →
          (rawOrbit i n : ℝ) ≤
            (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N)) := by
    filter_upwards [hWitness] with n hWitness hnS
    obtain ⟨k, ell, hk, hkCentered, hellCentered, _hshortcutTube,
        _hoddTube, _hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw⟩ :=
      hWitness hnS
    let root := Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
      Real.log ((Nat.log 2 n : ℝ) + 2))
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hpow0 : 0 ≤ (Real.log n) ^ (A (Nat.log 2 n)) := by positivity
    have hR0 : 0 ≤ R (Nat.log 2 n) := by dsimp [R]; positivity
    refine ⟨k, ell, hk,
      hkCentered.trans ?_, hellCentered.trans ?_, hell, hlandingEq,
      hlanding.trans_le ?_, ?_, ?_⟩
    · dsimp [C, root]
      nlinarith
    · dsimp [C, root]
      nlinarith
    · dsimp [C]
      nlinarith
    · intro j hj
      have hjBound := hshortcut j hj
      dsimp [R] at hjBound ⊢
      nlinarith
    · intro i hi
      simpa [R] using hraw i hi
  exact ⟨S, C, hC, hDense, hShell', hWitness'⟩

/-- Fixed-exponent Version 4 consequence with the exact endpoint power
`κ_* A - 1/2` in the global exceptional count.  The same shortcut and raw
witnesses reach one physical landing and satisfy their centered clocks and
common relative-height allowance. -/
theorem fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
    {A c beta : ℝ}
    (hA : timeSupportCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta) :
    ∃ S : Set ℕ, ∃ C Cexc : ℝ,
      0 < C ∧ 0 < Cexc ∧ NaturalDensityOne S ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤
          Cexc * X * (Real.log X) ^
            (-(fixedSharpEndpointMargin A))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ A ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A))) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A)))) := by
  let q := fixedSharpEndpointMargin A
  have hq : 0 < q := by
    simpa [q] using fixedSharpEndpointMargin_pos hA
  have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA
  have hbuffer : Tendsto
      (sharpMovingRankBuffer (fun _ => A)) atTop atTop :=
    tendsto_sharpMovingRankBuffer_const_atTop hA
  obtain ⟨S, C, hC, hDense, hShell, hWitness⟩ :=
    moving_polylogarithmic_common_landing_centered_clocks
      hA0 hc hbeta hq hbuffer (Eventually.of_forall fun _ => le_rfl)
  have hShellPower : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        (2 * C) * (((M : ℝ) + 2) ^ (-q)) := by
    filter_upwards [hShell] with M hShell
    have hterm := two_rpow_neg_sharpMovingRankBuffer_const_le hA M
    have hxpow : 0 ≤ ((M : ℝ) + 2) ^ (-q) := by positivity
    dsimp [q] at hterm ⊢
    nlinarith [hC.le]
  rcases (eventually_atTop.1 hShellPower) with ⟨M₀, hM₀⟩
  let B := 2 * C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hPrefixRaw : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) ≤
        (1 + 2 * B) * X *
          ((((Nat.log 2 X) / 2 : ℕ) : ℝ) + 2) ^ (-q) := by
    have h := eventually_badCount_assembleDyadic_le_polylog_profile
      (fun _ => S) M₀ B q hB hq.le
      (fun M hM => by
        simpa [B, assembleDyadic] using hM₀ M hM)
    simpa [assembleDyadic] using h
  have hConvert := eventually_halfNatLog_profile_le_natLog hq.le
  let Cexc := (1 + 2 * B) * (2 * Real.log 2) ^ q
  have hCexc : 0 < Cexc := by
    dsimp [Cexc, B]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hCount : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) ≤
        Cexc * X * (Real.log X) ^ (-q) := by
    filter_upwards [hPrefixRaw, hConvert] with X hRaw hConv
    have hcoef : 0 ≤ (1 + 2 * B) * (X : ℝ) := by positivity
    calc
      (badCount S X : ℝ) ≤
          (1 + 2 * B) * X *
            ((((Nat.log 2 X) / 2 : ℕ) : ℝ) + 2) ^ (-q) := hRaw
      _ ≤ (1 + 2 * B) * X *
          ((2 * Real.log 2) ^ q * (Real.log X) ^ (-q)) := by
            exact mul_le_mul_of_nonneg_left hConv hcoef
      _ = Cexc * X * (Real.log X) ^ (-q) := by
            dsimp [Cexc]
            ring
  refine ⟨S, C, Cexc, hC, hCexc, hDense, ?_, ?_⟩
  · simpa [q] using hCount
  · simpa [q] using hWitness

/-- Critical polylogarithmic descent with arbitrary prescribed divergent
target and height multipliers.  The functions need not be monotone: finite
dyadic-shell minima are built into the proof. -/
theorem critical_polylogarithmic_descent_with_arbitrary_multipliers
    {U R : ℕ → ℝ}
    (hUpos : ∀ n, 0 < U n) (hRpos : ∀ n, 0 < R n)
    (hU : Tendsto U atTop atTop) (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ K : ℝ,
      0 < K ∧ NaturalDensityOne S ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            (Real.log n) ^ timeSupportCriticalExponent * U n ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
            |(shortcutFirstPassageTime n z : ℝ) -
                fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
              |(rawFirstPassageTime n z : ℝ) -
                (3 / 2) * fixedPolylogClockCritical *
                  Real.log ((n : ℝ) / z)| ≤
                K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                  Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
            rawOrbit (rawFirstPassageTime n z) n =
              orbit (shortcutFirstPassageTime n z) n)) := by
  let Aseq := criticalMultiplierExponent U
  let Rsh := clippedShellHeight R
  let Amax := timeSupportCriticalExponent + 2
  let c := fixedPolylogClockCritical + 1
  let beta : ℝ := 1
  have hAmax : 0 < Amax := by
    dsimp [Amax]
    linarith [timeSupportCriticalExponent_pos]
  have hc : fixedPolylogClockCritical < c := by dsimp [c]; linarith
  have hbeta : 0 < beta := by dsimp [beta]; norm_num
  have hbuffer : Tendsto (sharpMovingRankBuffer Aseq) atTop atTop := by
    simpa [Aseq] using
      tendsto_sharpMovingRankBuffer_criticalMultiplierExponent hUpos hU
  have hUpper : ∀ᶠ M : ℕ in atTop, Aseq M ≤ Amax := by
    have h := eventually_criticalMultiplierExponent_le hU
    filter_upwards [h] with M hM
    exact hM.le
  have hRsh : Tendsto Rsh atTop atTop := by
    simpa [Rsh] using tendsto_clippedShellHeight_atTop hR
  obtain ⟨S, C, _eps, hC, _heps, hDense, _hShell, hWitness⟩ :=
    timeoutStrengthenedEndpointNaturalDensityDescentWithFirstPassage
      hAmax hc hbeta hbuffer hUpper hRsh
  let D := C * fixedPolylogTargetConstant timeSupportCriticalExponent
  have hTargetConstant :
      0 < fixedPolylogTargetConstant timeSupportCriticalExponent := by
    unfold fixedPolylogTargetConstant
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hw1 : ∀ᶠ M : ℕ in atTop,
      1 ≤ clippedCriticalMultiplier U M :=
    (tendsto_atTop.1 (tendsto_clippedCriticalMultiplier_atTop hU)) 1
  have hsqrtD : ∀ᶠ M : ℕ in atTop,
      D ≤ Real.sqrt (dyadicShellMinimum U M) :=
    (tendsto_atTop.1 (tendsto_sqrt_dyadicShellMinimum_atTop hU)) D
  have hScalar : ∀ᶠ M : ℕ in atTop,
      1 ≤ M ∧ 1 ≤ clippedCriticalMultiplier U M ∧
        D ≤ Real.sqrt (dyadicShellMinimum U M) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hw1, hsqrtD]
      with M hM hw hsqrt
    exact ⟨hM, hw, hsqrt⟩
  have hScalarAtLog := tendsto_natLogTwo_atTop.eventually hScalar
  have hFinal : ∀ᶠ n : ℕ in atTop, n ∈ S →
      ∃ k ell : ℕ,
        |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        (∀ j : ℕ, j ≤ k →
          |shortcutLogDeviation n j| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        (∀ j : ℕ, j ≤ k →
          |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        (∀ i : ℕ, i ≤ ell →
          |rawLogDeviation n i| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        ell = rawTime n k ∧
        rawOrbit ell n = orbit k n ∧
        (orbit k n : ℝ) <
          (Real.log n) ^ timeSupportCriticalExponent * U n ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) * R n) ∧
        (∀ i : ℕ, i ≤ ell →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * R n) ∧
        (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
          |(shortcutFirstPassageTime n z : ℝ) -
              fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
            |(rawFirstPassageTime n z : ℝ) -
              (3 / 2) * fixedPolylogClockCritical *
                Real.log ((n : ℝ) / z)| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          rawOrbit (rawFirstPassageTime n z) n =
            orbit (shortcutFirstPassageTime n z) n) := by
    filter_upwards [hWitness, hScalarAtLog,
        eventually_ge_atTop (8 : ℕ)] with n hWitness hScalar hn8
    intro hnS
    obtain ⟨k, ell, _hkBudget, hkCentered, hellCentered, hshortcutTube,
        hoddTube, hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw,
        hactual⟩ := hWitness hnS
    let M := Nat.log 2 n
    have hnpos : 0 < n := by omega
    have hnShell : n ∈ dyadicShell M := mem_dyadicShell_log hnpos
    obtain ⟨hM, hw, hsqrt⟩ := hScalar
    have hlogn : 1 ≤ Real.log n := by
      have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
        have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
          (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
            Real.log_two_gt_d9
        norm_num only [Nat.cast_ofNat]
        nlinarith
      exact hlog8.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn8))
    have hlogpow0 : 0 ≤
        (Real.log n) ^ timeSupportCriticalExponent := by positivity
    have hAseqScale := shellLog_rpow_criticalMultiplierExponent_le
      U hM hnShell
    have hTerminal := two_pow_criticalMultiplierTerminalRank_lt hUpos hw
    have hShellTarget := shellPolylogTarget_le_natLog
      timeSupportCriticalExponent_pos.le hnShell hlogn
    have hw0 : 0 ≤ clippedCriticalMultiplier U M :=
      (clippedCriticalMultiplier_pos hUpos M).le
    have hScaledShellTarget :
        2 * (((M : ℝ) + 2) ^ timeSupportCriticalExponent) *
            clippedCriticalMultiplier U M ≤
          fixedPolylogTargetConstant timeSupportCriticalExponent *
            (Real.log n) ^ timeSupportCriticalExponent *
              clippedCriticalMultiplier U M := by
      exact mul_le_mul_of_nonneg_right hShellTarget hw0
    have hMin0 : 0 ≤ dyadicShellMinimum U M :=
      (dyadicShellMinimum_pos hUpos M).le
    have hsqrt0 : 0 ≤ Real.sqrt (dyadicShellMinimum U M) :=
      Real.sqrt_nonneg _
    have hDw : D * clippedCriticalMultiplier U M ≤ U n := by
      have hwle := clippedCriticalMultiplier_le_sqrt U M
      have h₁ : D * clippedCriticalMultiplier U M ≤
          D * Real.sqrt (dyadicShellMinimum U M) :=
        mul_le_mul_of_nonneg_left hwle hD.le
      have h₂ : D * Real.sqrt (dyadicShellMinimum U M) ≤
          Real.sqrt (dyadicShellMinimum U M) *
            Real.sqrt (dyadicShellMinimum U M) :=
        mul_le_mul_of_nonneg_right hsqrt hsqrt0
      have h₃ : Real.sqrt (dyadicShellMinimum U M) *
          Real.sqrt (dyadicShellMinimum U M) =
            dyadicShellMinimum U M := by
        nlinarith [Real.sq_sqrt hMin0]
      exact h₁.trans (h₂.trans_eq h₃) |>.trans
        (dyadicShellMinimum_le_of_mem U hnShell)
    have hTarget : (orbit k n : ℝ) <
        (Real.log n) ^ timeSupportCriticalExponent * U n := by
      calc
        (orbit k n : ℝ) < C * (Real.log n) ^ (Aseq M) := by
          simpa [Aseq, M] using hlanding
        _ ≤ C * (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) :=
          mul_le_mul_of_nonneg_left hAseqScale hC.le
        _ < C * (2 * (((M : ℝ) + 2) ^ timeSupportCriticalExponent) *
            clippedCriticalMultiplier U M) :=
          mul_lt_mul_of_pos_left hTerminal hC
        _ ≤ C * (fixedPolylogTargetConstant timeSupportCriticalExponent *
            (Real.log n) ^ timeSupportCriticalExponent *
              clippedCriticalMultiplier U M) :=
          mul_le_mul_of_nonneg_left hScaledShellTarget hC.le
        _ = (Real.log n) ^ timeSupportCriticalExponent *
            (D * clippedCriticalMultiplier U M) := by
          dsimp [D]
          ring
        _ ≤ (Real.log n) ^ timeSupportCriticalExponent * U n :=
          mul_le_mul_of_nonneg_left hDw hlogpow0
    have hRshLe : Rsh M ≤ R n := by
      simpa [Rsh] using clippedShellHeight_le_of_mem R hnShell
    have hRsh0 : 0 ≤ Rsh M := by
      simpa [Rsh] using (clippedShellHeight_pos hRpos M).le
    refine ⟨k, ell, hkCentered, hellCentered, hshortcutTube, hoddTube,
      hrawTube, hell, hlandingEq, hTarget, ?_, ?_, hactual⟩
    · intro j hj
      have hjBound := hshortcut j hj
      have hhalf : (n : ℝ) * Rsh M / 2 ≤ (n : ℝ) * Rsh M := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith [mul_nonneg hn0 hRsh0]
      exact hjBound.trans (hhalf.trans
        (mul_le_mul_of_nonneg_left hRshLe (by positivity)))
    · intro i hi
      exact (hraw i hi).trans
        (mul_le_mul_of_nonneg_left hRshLe (by positivity))
  exact ⟨S, C, hC, hDense, hFinal⟩

end

end FirstPassageLinearTransport
