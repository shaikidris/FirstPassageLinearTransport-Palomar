/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.SharpJointExceptionalOrders
import FirstPassageLinearTransport.CriticalEndpointConsequences

/-!
# Fixed-polylogarithmic joint exceptional-order lower bound

This module specializes the reciprocal height obstruction to a fixed
polylogarithmic target and a logarithmic relative-height allowance.  The final
lower bound concerns failure of the joint target-and-height conclusion.  It is
not a lower bound for target-only failure.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- The fixed-polylog target used by the sharpness consumer. -/
def fixedJointPolylogTarget (C A : ℝ) (n : ℕ) : ℝ :=
  C * (Real.log n) ^ A

/-- The balanced fixed-polylog relative-height profile. -/
def fixedJointPolylogHeight (q : ℝ) (n : ℕ) : ℝ :=
  (((Nat.log 2 n : ℕ) : ℝ) + 2) ^ q

theorem shell_log_le_rank_add_two
    {M n : ℕ} (hn : n ∈ dyadicShell M) :
    Real.log n ≤ (M : ℝ) + 2 := by
  have hnPos : 0 < n := by
    have hpow : 0 < 2 ^ M := by positivity
    exact hpow.trans_le (mem_dyadicShell.mp hn).1
  have hnUpper : (n : ℝ) < (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast (mem_dyadicShell.mp hn).2
  have hlog := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by exact_mod_cast hnPos))
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < (2 : ℝ) ^ (M + 1)))
    hnUpper
  rw [Real.log_pow] at hlog
  have hlog2lt : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  push_cast at hlog
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

/-- A fixed polylogarithmic target cannot be reached in the first half of a
large shell solely by repeated halvings. -/
theorem eventually_fixedJointPolylogTarget_lt_halfShell
    {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, n ∈ dyadicShell M →
      fixedJointPolylogTarget C A n <
        (n : ℝ) / (2 : ℝ) ^ (M / 2) := by
  let b : ℝ := Real.log 2 / 8
  let d : ℝ := 1 / (C + 1)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hsmallReal :=
    (isLittleO_rpow_exp_pos_mul_atTop A hb).bound hd
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (8 : ℕ)] with M hsmall hM
  intro n hn
  let x : ℝ := (M : ℝ) + 2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hlogn0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    have hnLower := (mem_dyadicShell.mp hn).1
    have hpow : 1 ≤ 2 ^ M := one_le_pow₀ (by norm_num)
    exact_mod_cast hpow.trans hnLower
  have hlogUpper : Real.log n ≤ x := by
    simpa [x] using shell_log_le_rank_add_two hn
  have hpowUpper : (Real.log n) ^ A ≤ x ^ A :=
    Real.rpow_le_rpow hlogn0 hlogUpper hA
  have hsmall' : x ^ A ≤ d * Real.exp (b * x) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 A)] at hsmall
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hsmall
    simpa [x] using hsmall
  have hCd : C * d < 1 := by
    dsimp [d]
    have hC1 : 0 < C + 1 := by linarith
    rw [mul_one_div]
    exact (div_lt_one hC1).2 (by linarith)
  have htargetExp : fixedJointPolylogTarget C A n <
      Real.exp (b * x) := by
    unfold fixedJointPolylogTarget
    calc
      C * (Real.log n) ^ A ≤ C * (x ^ A) :=
        mul_le_mul_of_nonneg_left hpowUpper hC.le
      _ ≤ C * (d * Real.exp (b * x)) :=
        mul_le_mul_of_nonneg_left hsmall' hC.le
      _ < 1 * Real.exp (b * x) := by
        have hexp := Real.exp_pos (b * x)
        nlinarith
      _ = Real.exp (b * x) := one_mul _
  let h := M / 2
  have hhM : h ≤ M := by dsimp [h]; omega
  have hbx : b * x ≤ ((M - h : ℕ) : ℝ) * Real.log 2 := by
    dsimp [b, x, h]
    have hlog2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hMx : (M : ℝ) + 2 ≤ 2 * (M : ℝ) := by
      exact_mod_cast (by omega : M + 2 ≤ 2 * M)
    have hquarter : ((M : ℝ) + 2) / 8 ≤ (M : ℝ) / 4 := by linarith
    have htwiceNat : M ≤ 2 * (M - M / 2) := by omega
    have htwice : (M : ℝ) ≤ 2 * ((M - M / 2 : ℕ) : ℝ) := by
      exact_mod_cast htwiceNat
    have hgap : (M : ℝ) / 4 ≤ ((M - M / 2 : ℕ) : ℝ) := by
      linarith
    nlinarith
  have hexpPow : Real.exp (b * x) ≤ (2 : ℝ) ^ (M - h) := by
    calc
      Real.exp (b * x) ≤
          Real.exp (((M - h : ℕ) : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hbx
      _ = (2 : ℝ) ^ (M - h) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hn).1
  have hpowhPos : 0 < (2 : ℝ) ^ h := by positivity
  have hhalving : (2 : ℝ) ^ (M - h) ≤
      (n : ℝ) / (2 : ℝ) ^ h := by
    apply (le_div_iff₀ hpowhPos).2
    rw [← pow_add]
    have hadd : M - h + h = M := Nat.sub_add_cancel hhM
    simpa [hadd] using hnLower
  exact htargetExp.trans_le (hexpPow.trans hhalving)

theorem fixedJointPolylogHeight_eq_on_shell
    (q : ℝ) {M n : ℕ} (hn : n ∈ dyadicShell M) :
    fixedJointPolylogHeight q n = ((M : ℝ) + 2) ^ q := by
  simp [fixedJointPolylogHeight, log_two_eq_of_mem_dyadicShell hn]

/-- Every fixed power of the shell rank satisfies the logarithmic-slope
hypothesis of the reciprocal maximum theorem at the half-shell prefix. -/
theorem eventually_log_shellRankRpow_le_halfShell
    {q : ℝ} (hq : 0 ≤ q) :
    ∀ᶠ M : ℕ in atTop,
      Real.log (((M : ℝ) + 2) ^ q) ≤
        reciprocalMaximumEpsilon * ((M / 2 : ℕ) : ℝ) * Real.log 3 := by
  let d := reciprocalMaximumEpsilon * Real.log 3 / (4 * (q + 1))
  have hq1 : 0 < q + 1 := by linarith
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos
      (mul_pos reciprocalMaximumEpsilon_pos
        (Real.log_pos (by norm_num)))
      (mul_pos (by norm_num) hq1)
  have hsmallReal := Real.isLittleO_log_id_atTop.bound hd
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (5 : ℕ)] with M hsmall hM
  let x : ℝ := (M : ℝ) + 2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxPos : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  change |Real.log x| ≤ d * |x| at hsmall
  rw [abs_of_nonneg hlog0, abs_of_nonneg hx0] at hsmall
  have hxHalfNat : M + 2 ≤ 4 * (M / 2) := by omega
  have hxHalf : x ≤ 4 * ((M / 2 : ℕ) : ℝ) := by
    dsimp [x]
    exact_mod_cast hxHalfNat
  have hqd : q * d ≤ reciprocalMaximumEpsilon * Real.log 3 / 4 := by
    dsimp [d]
    have hden : 0 < 4 * (q + 1) := by positivity
    have hfrac : q / (q + 1) ≤ 1 := by
      exact (div_le_one hq1).2 (by linarith)
    have hpos : 0 ≤ reciprocalMaximumEpsilon * Real.log 3 / 4 := by
      exact (div_nonneg
        (mul_nonneg reciprocalMaximumEpsilon_pos.le
          (Real.log_pos (by norm_num)).le) (by norm_num))
    calc
      q * (reciprocalMaximumEpsilon * Real.log 3 / (4 * (q + 1))) =
          (q / (q + 1)) *
            (reciprocalMaximumEpsilon * Real.log 3 / 4) := by
        field_simp [ne_of_gt hq1]
      _ ≤ 1 * (reciprocalMaximumEpsilon * Real.log 3 / 4) :=
        mul_le_mul_of_nonneg_right hfrac hpos
      _ = reciprocalMaximumEpsilon * Real.log 3 / 4 := one_mul _
  change Real.log (x ^ q) ≤ _
  rw [Real.log_rpow hxPos]
  calc
    q * Real.log x ≤ q * (d * x) :=
      mul_le_mul_of_nonneg_left hsmall hq
    _ = (q * d) * x := by ring
    _ ≤ (reciprocalMaximumEpsilon * Real.log 3 / 4) * x :=
      mul_le_mul_of_nonneg_right hqd hx0
    _ ≤ (reciprocalMaximumEpsilon * Real.log 3 / 4) *
        (4 * ((M / 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hxHalf (by
        exact div_nonneg
          (mul_nonneg reciprocalMaximumEpsilon_pos.le
            (Real.log_pos (by norm_num)).le) (by norm_num))
    _ = reciprocalMaximumEpsilon * ((M / 2 : ℕ) : ℝ) *
        Real.log 3 := by ring

/-- The finite reciprocal correction is eventually at least one half on the
half-shell prefix. -/
theorem eventually_half_le_reciprocalMaximum_halfShell_correction :
    ∀ᶠ M : ℕ in atTop,
      (1 / 2 : ℝ) ≤
        1 - reciprocalMaximumConstant / ((M / 2 : ℕ) : ℝ) := by
  let N : ℕ := ⌈max 1 (2 * reciprocalMaximumConstant)⌉₊
  have hhalfT : Tendsto (fun M : ℕ => M / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hlarge := (tendsto_atTop.1 hhalfT) N
  filter_upwards [hlarge] with M hM
  have hceil : max 1 (2 * reciprocalMaximumConstant) ≤ (N : ℝ) := by
    dsimp [N]
    exact Nat.le_ceil _
  have hden1 : 1 ≤ ((M / 2 : ℕ) : ℝ) := by
    have : 1 ≤ N := by
      exact_mod_cast (le_max_left (1 : ℝ) _ |>.trans hceil)
    exact_mod_cast this.trans hM
  have hdenPos : 0 < ((M / 2 : ℕ) : ℝ) := zero_lt_one.trans_le hden1
  have hK : 2 * reciprocalMaximumConstant ≤ ((M / 2 : ℕ) : ℝ) := by
    have hKN : 2 * reciprocalMaximumConstant ≤ (N : ℝ) :=
      (le_max_right _ _).trans hceil
    have hNM : (N : ℝ) ≤ ((M / 2 : ℕ) : ℝ) := by exact_mod_cast hM
    exact hKN.trans hNM
  have hdiv : reciprocalMaximumConstant /
      ((M / 2 : ℕ) : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hdenPos).2
    nlinarith
  linarith

theorem tendsto_lastCompleteDyadicShell_atTop :
    Tendsto lastCompleteDyadicShell atTop atTop := by
  exact (tendsto_sub_atTop_nat 1).comp tendsto_natLogTwo_atTop

/-- Quantitative height-forced lower bound for the balanced fixed-polylog
profile, expressed at the exact last-complete-shell scale. -/
theorem eventually_fixedJointPolylogHeightFailureCount_ge
    {C A q : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hq : 0 < q) :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) /
          (12 * (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by
  have hTargetM := eventually_fixedJointPolylogTarget_lt_halfShell hC hA
  have hLogM := eventually_log_shellRankRpow_le_halfShell hq.le
  have hCorrectionM :=
    eventually_half_le_reciprocalMaximum_halfShell_correction
  have hMlarge : ∀ᶠ M : ℕ in atTop, 2 ≤ M := eventually_ge_atTop 2
  have hTarget := tendsto_lastCompleteDyadicShell_atTop.eventually hTargetM
  have hLog := tendsto_lastCompleteDyadicShell_atTop.eventually hLogM
  have hCorrection :=
    tendsto_lastCompleteDyadicShell_atTop.eventually hCorrectionM
  have hLarge := tendsto_lastCompleteDyadicShell_atTop.eventually hMlarge
  filter_upwards [eventually_ge_atTop (4 : ℕ), hTarget, hLog,
    hCorrection, hLarge] with X hX hTarget hLog hCorrection hMlarge
  let M := lastCompleteDyadicShell X
  let h := M / 2
  let U := ((M : ℝ) + 2) ^ q
  have hh : 0 < h := by dsimp [h]; omega
  have hhM : h ≤ M := by dsimp [h]; omega
  have hbase : 1 ≤ (M : ℝ) + 2 := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hU : 1 ≤ U := by
    dsimp [U]
    exact Real.one_le_rpow hbase hq.le
  have hUPos : 0 < U := zero_lt_one.trans_le hU
  have hLog' : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3 := by
    simpa [M, h, U] using hLog
  have hTarget' : ∀ n : ℕ, n ∈ dyadicShell M →
      fixedJointPolylogTarget C A n <
        (n : ℝ) / (2 : ℝ) ^ h := by
    simpa [M, h] using hTarget
  have hHeight : ∀ n : ℕ, n ∈ dyadicShell M →
      fixedJointPolylogHeight q n ≤ U := by
    intro n hn
    rw [fixedJointPolylogHeight_eq_on_shell q hn]
  have hraw :=
    variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
      hX hU hLog' hh hhM hTarget' hHeight
  have hcoef0 : 0 ≤ (1 / 4 : ℝ) * (2 / (3 * U)) := by positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hweaken :
      ((1 / 4 : ℝ) * (2 / (3 * U)) * (1 / 2)) * (X : ℝ) ≤
        ((1 / 4 : ℝ) * (2 / (3 * U)) *
          (1 - reciprocalMaximumConstant / (h : ℝ))) * (X : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCorrection hcoef0) hX0
  have hsimple :
      (X : ℝ) / (12 * U) =
        ((1 / 4 : ℝ) * (2 / (3 * U)) * (1 / 2)) * (X : ℝ) := by
    field_simp [ne_of_gt hUPos]
    ring
  rw [hsimple]
  exact hweaken.trans (by simpa [M, h, U] using hraw)

theorem lastCompleteDyadicShell_add_two
    {X : ℕ} (hX : 4 ≤ X) :
    lastCompleteDyadicShell X + 2 = Nat.log 2 X + 1 := by
  have h := lastCompleteDyadicShell_succ hX
  omega

/-- The binary shell rank is bounded by the natural logarithm with one
explicit harmless factor. -/
theorem natLogTwo_add_one_le_two_div_log_two_mul_log
    {X : ℕ} (hX : 2 ≤ X) :
    ((Nat.log 2 X : ℕ) : ℝ) + 1 ≤
      (2 / Real.log 2) * Real.log X := by
  have hXpos : 0 < X := by omega
  have hpowNat := Nat.pow_log_le_self 2 hXpos.ne'
  have hpow : (2 : ℝ) ^ Nat.log 2 X ≤ (X : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow := Real.log_le_log (by positivity :
      (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 X) hpow
  rw [Real.log_pow] at hlogPow
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogXLower : Real.log 2 ≤ Real.log X := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by exact_mod_cast hXpos))
      (by exact_mod_cast hX)
  have hone : 1 ≤ Real.log X / Real.log 2 := by
    exact (le_div_iff₀ hlogTwo).2 (by simpa using hlogXLower)
  have hJ : ((Nat.log 2 X : ℕ) : ℝ) ≤
      Real.log X / Real.log 2 := by
    exact (le_div_iff₀ hlogTwo).2 (by
      simpa [mul_comm] using hlogPow)
  calc
    ((Nat.log 2 X : ℕ) : ℝ) + 1 ≤
        Real.log X / Real.log 2 + Real.log X / Real.log 2 :=
      add_le_add hJ hone
    _ = (2 / Real.log 2) * Real.log X := by field_simp; ring

/-- Height-forced lower half of the fixed-polylogarithmic balanced joint
exceptional order.  It is a target-and-height lower bound, not a lower bound
for target-only failure. -/
theorem eventually_fixedJointPolylogHeightFailureCount_ge_log_order
    {C A q : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hq : 0 < q) :
    ∀ᶠ X : ℕ in atTop,
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by
  have hraw := eventually_fixedJointPolylogHeightFailureCount_ge hC hA hq
  filter_upwards [hraw, eventually_ge_atTop (4 : ℕ)] with X hraw hX
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKPos : 0 < 2 / Real.log 2 := by positivity
  have hlogXPos : 0 < Real.log X :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hbase :
      (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ≤
        (2 / Real.log 2) * Real.log X := by
    rw [show ((lastCompleteDyadicShell X : ℕ) : ℝ) + 2 =
      (((Nat.log 2 X : ℕ) : ℝ) + 1) by
        exact_mod_cast lastCompleteDyadicShell_add_two hX]
    exact natLogTwo_add_one_le_two_div_log_two_mul_log (by omega)
  have hbase0 : 0 ≤ ((lastCompleteDyadicShell X : ℕ) : ℝ) + 2 := by
    positivity
  have hpow :
      (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q ≤
        ((2 / Real.log 2) * Real.log X) ^ q :=
    Real.rpow_le_rpow hbase0 hbase hq.le
  have hfactor :
      (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q ≤
        (2 / Real.log 2) ^ q * (Real.log X) ^ q := by
    simpa [Real.mul_rpow hKPos.le hlogXPos.le] using hpow
  have hdenPos : 0 <
      12 * (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q := by
    positivity
  have hdiv :
      (X : ℝ) /
          (12 * ((2 / Real.log 2) ^ q * (Real.log X) ^ q)) ≤
        (X : ℝ) /
          (12 * (((lastCompleteDyadicShell X : ℕ) : ℝ) + 2) ^ q) := by
    exact div_le_div_of_nonneg_left (by positivity) hdenPos
      (mul_le_mul_of_nonneg_left hfactor (by norm_num))
  have hrewrite :
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) =
        (X : ℝ) /
          (12 * ((2 / Real.log 2) ^ q * (Real.log X) ^ q)) := by
    rw [Real.rpow_neg hlogXPos.le]
    field_simp
  rw [hrewrite]
  exact hdiv.trans hraw

end

end FirstPassageLinearTransport
