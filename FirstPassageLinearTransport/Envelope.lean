/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.Ring.GeomSum
import FirstPassageLinearTransport.Barrier

/-!
# Maximal-barrier orbit envelope

This module formalizes the deterministic payload of Section 3: a maximal
parity barrier gives a uniform geometric bound for the affine correction and
hence a two-sided orbit envelope.  The geometric argument is source-adapted
from CET, but is connected to V2's independently proved affine iterate.
-/

namespace FirstPassageLinearTransport

open scoped Real BigOperators

noncomputable section

/-- Base-two logarithm of three. -/
def logTwoThree : ℝ := Real.log 3 / Real.log 2

/-- Central exponent `a₀ = log₂(3)/2`. -/
def a0 : ℝ := logTwoThree / 2

/-- Central multiplicative ratio `ρ = sqrt(3)/2`. -/
def rho : ℝ := Real.sqrt 3 / 2

/-- Deterministic central scale `3^(k/2)/2^k`. -/
def centralOrbitScale (k : ℕ) : ℝ :=
  (3 : ℝ) ^ ((k : ℝ) / 2) / (2 : ℝ) ^ k

theorem logTwoThree_pos : 0 < logTwoThree := by
  unfold logTwoThree
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

theorem logTwoThree_one_lt : 1 < logTwoThree := by
  unfold logTwoThree
  rw [one_lt_div (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  exact Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
    (by norm_num)

theorem a0_pos : 0 < a0 := by
  unfold a0
  exact div_pos logTwoThree_pos (by norm_num)

theorem rho_pos : 0 < rho := by
  unfold rho
  positivity

theorem rho_lt_one : rho < 1 := by
  unfold rho
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith

theorem centralOrbitScale_pos (k : ℕ) : 0 < centralOrbitScale k := by
  unfold centralOrbitScale
  positivity

theorem centralOrbitScale_eq_rho_pow (k : ℕ) :
    centralOrbitScale k = rho ^ k := by
  unfold centralOrbitScale rho
  rw [Real.rpow_div_two_eq_sqrt (k : ℝ) (by norm_num),
    Real.rpow_natCast, div_pow]

/-- The `0/1` parity digit as a real number. -/
def parityDigitR (n i : ℕ) : ℝ := (parityBit n i : ℕ)

theorem parityDigitR_nonneg (n i : ℕ) : 0 ≤ parityDigitR n i := by
  unfold parityDigitR
  positivity

theorem parityDigitR_le_one (n i : ℕ) : parityDigitR n i ≤ 1 := by
  unfold parityDigitR
  exact_mod_cast (show (parityBit n i : ℕ) ≤ 1 by omega)

/-- One summand of the paper's normalized correction `r_k(n)`. -/
def normalizedCorrectionTerm (k n i : ℕ) : ℝ :=
  parityDigitR n i /
    ((3 : ℝ) ^ oddCount n (i + 1) * (2 : ℝ) ^ (k - i))

/-- The normalized correction `r_k(n)` from equation (3.3). -/
def normalizedCorrection (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, normalizedCorrectionTerm k n i

theorem normalizedCorrectionTerm_nonneg (k n i : ℕ) :
    0 ≤ normalizedCorrectionTerm k n i := by
  unfold normalizedCorrectionTerm
  exact div_nonneg (parityDigitR_nonneg n i) (by positivity)

theorem normalizedCorrection_nonneg (k n : ℕ) :
    0 ≤ normalizedCorrection k n := by
  exact Finset.sum_nonneg fun i _ => normalizedCorrectionTerm_nonneg k n i

theorem normalizedCorrectionTerm_mul_pow {k n i : ℕ} (hi : i < k) :
    normalizedCorrectionTerm k n i * (3 : ℝ) ^ oddCount n k =
      parityDigitR n i *
        (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
          (2 : ℝ) ^ (k - i) := by
  have hmono : oddCount n (i + 1) ≤ oddCount n k :=
    oddCount_mono (by omega)
  have hsplit : oddCount n k =
      oddCount n (i + 1) +
        (oddCount n k - oddCount n (i + 1)) := by omega
  unfold normalizedCorrectionTerm
  rw [hsplit, pow_add]
  field_simp
  simp

/-- V2 exact affine iterate in the normalized correction coordinate used by
the paper. -/
theorem orbit_eq_normalizedCorrection (k n : ℕ) :
    (orbit k n : ℝ) =
      ((n : ℝ) / (2 : ℝ) ^ k + normalizedCorrection k n) *
        (3 : ℝ) ^ oddCount n k := by
  rw [exact_affine_iterate_real]
  unfold normalizedCorrection
  calc
    (3 : ℝ) ^ oddCount n k / (2 : ℝ) ^ k * (n : ℝ) +
          ∑ i ∈ Finset.range k,
            parityDigitR n i *
              (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
                (2 : ℝ) ^ (k - i) =
        (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k +
          ∑ i ∈ Finset.range k,
            normalizedCorrectionTerm k n i *
              (3 : ℝ) ^ oddCount n k := by
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i hi
        exact (normalizedCorrectionTerm_mul_pow
          (Finset.mem_range.mp hi)).symm
    _ = ((n : ℝ) / (2 : ℝ) ^ k + normalizedCorrection k n) *
          (3 : ℝ) ^ oddCount n k := by
      unfold normalizedCorrection
      rw [add_mul, Finset.sum_mul]

theorem oddCount_lower_of_maximalRegular {n M H : ℕ} {h : ℝ}
    (hreg : MaximalParityRegular n M h) (hHM : H ≤ M) :
    (H : ℝ) / 2 - h ≤ oddCount n H := by
  have habs := hreg H hHM
  have hlower := (abs_le.mp habs).1
  linarith

/-- A single normalized correction term is bounded by one term of the fixed
geometric series with ratio `rho`. -/
theorem normalizedCorrectionTerm_scaled_le_maximal
    {n M k i : ℕ} {h : ℝ}
    (hik : i < k) (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    normalizedCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i) := by
  have hiM : i + 1 ≤ M := by omega
  have hS := oddCount_lower_of_maximalRegular hreg hiM
  have hki : k = (i + 1) + (k - 1 - i) := by omega
  have hExp :
      (k : ℝ) / 2 ≤
        oddCount n (i + 1) + h + ((k - 1 - i : ℕ) : ℝ) / 2 := by
    have hkiR :
        (k : ℝ) = (i + 1 : ℕ) + (k - 1 - i : ℕ) := by
      exact_mod_cast hki
    push_cast at hS hkiR
    nlinarith
  have hbase :
      (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ oddCount n (i + 1) *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := by
    calc
      (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^
            ((oddCount n (i + 1) : ℝ) + h +
              ((k - 1 - i : ℕ) : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
      _ = (3 : ℝ) ^ oddCount n (i + 1) *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
          Real.rpow_natCast]
  have hden :
      0 < (3 : ℝ) ^ oddCount n (i + 1) * (2 : ℝ) ^ (k - i) := by
    positivity
  have hraw :
      normalizedCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i) := by
    unfold normalizedCorrectionTerm
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    calc
      parityDigitR n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^ ((k : ℝ) / 2) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (parityDigitR_le_one n i)
            (Real.rpow_nonneg (by norm_num) _)
      _ ≤ (3 : ℝ) ^ oddCount n (i + 1) *
          (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) := hbase
      _ = ((3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i)) *
          ((3 : ℝ) ^ oddCount n (i + 1) *
            (2 : ℝ) ^ (k - i)) := by
        field_simp
  calc
    _ ≤ (3 : ℝ) ^ h *
          (3 : ℝ) ^ (((k - 1 - i : ℕ) : ℝ) / 2) /
            (2 : ℝ) ^ (k - i) := hraw
    _ = (3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i) := by
      have hd : k - i = (k - 1 - i) + 1 := by omega
      rw [hd, pow_succ, Real.rpow_div_two_eq_sqrt _ (by norm_num),
        Real.rpow_natCast]
      unfold rho
      rw [div_pow]
      field_simp

/-- The affine-correction estimate in the uniform form consumed downstream. -/
theorem normalizedCorrection_scaled_le_maximal
    {n M k : ℕ} {h : ℝ}
    (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (2 + Real.sqrt 3) * (3 : ℝ) ^ h := by
  have hterm :
      ∀ i ∈ Finset.range k,
        normalizedCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
          (3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i) := by
    intro i hi
    exact normalizedCorrectionTerm_scaled_le_maximal
      (Finset.mem_range.mp hi) hkM hreg
  have hsum :
      normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (3 : ℝ) ^ h / 2 * ∑ j ∈ Finset.range k, rho ^ j := by
    calc
      normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) =
          ∑ i ∈ Finset.range k,
            normalizedCorrectionTerm k n i *
              (3 : ℝ) ^ ((k : ℝ) / 2) := by
        simp only [normalizedCorrection, Finset.sum_mul]
      _ ≤ ∑ i ∈ Finset.range k,
          ((3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i)) :=
        Finset.sum_le_sum hterm
      _ = (3 : ℝ) ^ h / 2 *
          ∑ j ∈ Finset.range k, rho ^ (k - 1 - j) := by
        rw [Finset.mul_sum]
      _ = (3 : ℝ) ^ h / 2 *
          ∑ j ∈ Finset.range k, rho ^ j := by
        rw [Finset.sum_range_reflect]
  have hgeom :
      ∑ j ∈ Finset.range k, rho ^ j < (1 - rho)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ (sub_pos.mpr rho_lt_one)]
    rw [geom_sum_mul_neg]
    have hpow : 0 < rho ^ k := pow_pos rho_pos k
    linarith
  have hconstant : ((1 - rho)⁻¹ : ℝ) = 2 * (2 + Real.sqrt 3) := by
    unfold rho
    have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hden : 2 - Real.sqrt 3 ≠ 0 := by
      nlinarith [rho_lt_one]
    field_simp
    nlinarith
  calc
    _ ≤ (3 : ℝ) ^ h / 2 * ∑ j ∈ Finset.range k, rho ^ j := hsum
    _ ≤ (3 : ℝ) ^ h / 2 * (1 - rho)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeom.le (by positivity)
    _ = (2 + Real.sqrt 3) * (3 : ℝ) ^ h := by
      rw [hconstant]
      ring

/-- Change of base specialized to `log₂ 3`. -/
theorem three_rpow_eq_two_rpow_logTwoThree (x : ℝ) :
    (3 : ℝ) ^ x = (2 : ℝ) ^ (logTwoThree * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hlog2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  unfold logTwoThree
  field_simp

theorem a0_lt_one : a0 < 1 := by
  unfold a0 logTwoThree
  rw [div_div, div_lt_one (by positivity)]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  calc
    Real.log 3 < Real.log 4 := Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3))
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 4))
      (by norm_num)
    _ = Real.log 2 * 2 := by rw [hlog4]; ring

/-- Strict logarithmic contraction gap at the central parity drift. -/
def driftGap : ℝ := 1 - a0

theorem driftGap_pos : 0 < driftGap := by
  unfold driftGap
  linarith [a0_lt_one]

theorem centralOrbitScale_eq_two_rpow_neg_gap (k : ℕ) :
    centralOrbitScale k = (2 : ℝ) ^ (-driftGap * k) := by
  unfold centralOrbitScale
  rw [three_rpow_eq_two_rpow_logTwoThree, ← Real.rpow_natCast,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold driftGap a0
  ring

theorem centralOrbitScale_ge_n_rpow_neg_gap
    {n k M : ℕ} (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M) :
    (n : ℝ) ^ (-driftGap) ≤ centralOrbitScale k := by
  have hb := driftGap_pos
  have hkMR : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hExp : -driftGap * M ≤ -driftGap * k := by nlinarith
  have hScaleM :
      (2 : ℝ) ^ (-driftGap * M) ≤ centralOrbitScale k := by
    rw [centralOrbitScale_eq_two_rpow_neg_gap]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hBase :
      (n : ℝ) ^ (-driftGap) ≤ ((2 : ℝ) ^ M) ^ (-driftGap) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hnLower (by linarith)
  have hEq :
      ((2 : ℝ) ^ M) ^ (-driftGap) =
        (2 : ℝ) ^ (-driftGap * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hEq] at hBase
  exact hBase.trans hScaleM

/-- Barrier height chosen on shell `M` for tolerance `t`. -/
def maximalBarrierHeight (t : ℝ) (M : ℕ) : ℝ :=
  t * M / (2 * logTwoThree)

theorem maximalBarrierHeight_nonneg {t : ℝ} {M : ℕ} (ht : 0 ≤ t) :
    0 ≤ maximalBarrierHeight t M := by
  unfold maximalBarrierHeight
  exact div_nonneg (mul_nonneg ht (Nat.cast_nonneg M))
    (mul_nonneg (by norm_num) logTwoThree_pos.le)

theorem three_rpow_maximalBarrierHeight (t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ maximalBarrierHeight t M =
      (2 : ℝ) ^ (t * (M : ℝ) / 2) := by
  rw [three_rpow_eq_two_rpow_logTwoThree]
  congr 1
  unfold maximalBarrierHeight
  have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
  field_simp [hlog]

theorem maximalBarrier_phase_half {n M : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hnShell : n ∈ dyadicShell M) :
    (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ (t / 2) := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  rw [three_rpow_maximalBarrierHeight]
  calc
    (2 : ℝ) ^ (t * (M : ℝ) / 2) =
        ((2 : ℝ) ^ M) ^ (t / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ (t / 2) :=
      Real.rpow_le_rpow (by positivity) hnLower (by positivity)

theorem maximalBarrier_phase_two {n M : ℕ} {t : ℝ}
    (ht : 0 < t) (hstart : 2 ≤ t * M)
    (hnShell : n ∈ dyadicShell M) :
    2 * (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ t := by
  have hhalf := maximalBarrier_phase_half ht.le hnShell
  have htwoExp : (1 : ℝ) ≤ t * (M : ℝ) / 2 := by
    linarith
  have htwo : (2 : ℝ) ≤ (n : ℝ) ^ (t / 2) := by
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ (t * (M : ℝ) / 2) := by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) htwoExp
    exact h2pow.trans (by
      rw [← three_rpow_maximalBarrierHeight]
      exact hhalf)
  have hnPos : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hp (mem_dyadicShell.mp hnShell).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  calc
    2 * (3 : ℝ) ^ maximalBarrierHeight t M ≤
        (n : ℝ) ^ (t / 2) * (n : ℝ) ^ (t / 2) :=
      mul_le_mul htwo hhalf (by positivity) (by positivity)
    _ = (n : ℝ) ^ t := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring

theorem two_affineConstant_le_n_mul_central
    {n k M : ℕ} (hM : 4 ≤ M) (hkM : k ≤ M)
    (hnShell : n ∈ dyadicShell M) :
    2 * (2 + Real.sqrt 3) ≤ (n : ℝ) * centralOrbitScale k := by
  have hs2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hconst : 2 * (2 + Real.sqrt 3) ≤ (9 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 3]
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hnPos : 0 < n := by
    exact lt_of_lt_of_le (pow_pos (by omega) M) hnLowerNat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hscale := centralOrbitScale_ge_n_rpow_neg_gap hkM hnShell
  have h16 : (16 : ℝ) ≤ n := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hM
      _ ≤ n := hnLower
  have hnA0 : (16 : ℝ) ^ a0 ≤ (n : ℝ) ^ a0 :=
    Real.rpow_le_rpow (by norm_num) h16 a0_pos.le
  have h16a0 : (16 : ℝ) ^ a0 = 9 := by
    calc
      (16 : ℝ) ^ a0 = (2 : ℝ) ^ (4 * a0) := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      _ = (3 : ℝ) ^ (2 : ℝ) := by
        rw [three_rpow_eq_two_rpow_logTwoThree]
        congr 1
        unfold a0
        ring
      _ = 9 := by norm_num
  have hA0Scale : (n : ℝ) ^ a0 ≤ (n : ℝ) * centralOrbitScale k := by
    have hExp : a0 = 1 + (-driftGap) := by
      unfold driftGap
      ring
    rw [hExp, Real.rpow_add hnR, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hscale hnR.le
  calc
    2 * (2 + Real.sqrt 3) ≤ 9 := hconst
    _ = (16 : ℝ) ^ a0 := h16a0.symm
    _ ≤ (n : ℝ) ^ a0 := hnA0
    _ ≤ (n : ℝ) * centralOrbitScale k := hA0Scale

theorem orbit_lower_of_fixed_barrier {n k : ℕ} {h t : ℝ}
    (hn : 0 < n)
    (hS : (k : ℝ) / 2 - h ≤ (oddCount n k : ℝ))
    (hphase : (3 : ℝ) ^ h ≤ (n : ℝ) ^ t) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hInv : (n : ℝ) / (n : ℝ) ^ t ≤ (n : ℝ) / (3 : ℝ) ^ h :=
    div_le_div_of_nonneg_left hnR.le (by positivity) hphase
  have hThree :
      (3 : ℝ) ^ ((k : ℝ) / 2 - h) ≤ (3 : ℝ) ^ oddCount n k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  rw [orbit_eq_normalizedCorrection]
  calc
    centralOrbitScale k * (n : ℝ) ^ (1 - t) =
        centralOrbitScale k * ((n : ℝ) / (n : ℝ) ^ t) := by
      rw [Real.rpow_sub hnR, Real.rpow_one]
    _ ≤ centralOrbitScale k * ((n : ℝ) / (3 : ℝ) ^ h) :=
      mul_le_mul_of_nonneg_left hInv (centralOrbitScale_pos k).le
    _ = (n : ℝ) / (2 : ℝ) ^ k *
        (3 : ℝ) ^ ((k : ℝ) / 2 - h) := by
      unfold centralOrbitScale
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
      ring
    _ ≤ (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k :=
      mul_le_mul_of_nonneg_left hThree (by positivity)
    _ ≤ ((n : ℝ) / (2 : ℝ) ^ k + normalizedCorrection k n) *
        (3 : ℝ) ^ oddCount n k :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (normalizedCorrection_nonneg k n))
        (by positivity)

theorem orbit_upper_of_fixed_barrier {n k : ℕ} {h t C : ℝ}
    (hn : 0 < n)
    (hS : (oddCount n k : ℝ) ≤ (k : ℝ) / 2 + h)
    (hphase : 2 * (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hcorr : normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      C * (3 : ℝ) ^ h)
    (hcorrAbsorb :
      2 * (C * (3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hThree :
      (3 : ℝ) ^ oddCount n k ≤ (3 : ℝ) ^ ((k : ℝ) / 2 + h) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
  have hMain :
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      _ ≤ (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ ((k : ℝ) / 2 + h) :=
        mul_le_mul_of_nonneg_left hThree (by positivity)
      _ = centralOrbitScale k * ((n : ℝ) * (3 : ℝ) ^ h) := by
        unfold centralOrbitScale
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ centralOrbitScale k * ((n : ℝ) * ((n : ℝ) ^ t / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (centralOrbitScale_pos k).le
        apply mul_le_mul_of_nonneg_left _ hnR.le
        linarith
      _ = (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        rw [Real.rpow_add hnR, Real.rpow_one]
        ring
  have hCorr :
      normalizedCorrection k n * (3 : ℝ) ^ oddCount n k ≤
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
    calc
      _ ≤ normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2 + h) :=
        mul_le_mul_of_nonneg_left hThree
          (normalizedCorrection_nonneg k n)
      _ = (normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2)) *
          (3 : ℝ) ^ h := by
        rw [Real.rpow_add (by norm_num)]
        ring
      _ ≤ (C * (3 : ℝ) ^ h) * (3 : ℝ) ^ h :=
        mul_le_mul_of_nonneg_right hcorr (by positivity)
      _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 := by
        linarith
  rw [orbit_eq_normalizedCorrection]
  calc
    _ = (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k +
        normalizedCorrection k n * (3 : ℝ) ^ oddCount n k := by ring
    _ ≤ (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 +
        (centralOrbitScale k * (n : ℝ) ^ (1 + t)) / 2 :=
      add_le_add hMain hCorr
    _ = _ := by ring

/-- The maximal barrier supplies the complete two-sided orbit envelope. -/
theorem orbit_envelope_of_maximalBarrier
    {n k M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M)
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg : MaximalParityRegular n M (maximalBarrierHeight t M)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnPos : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hp (mem_dyadicShell.mp hnShell).1
  have hbounds := hreg k hkM
  have hSlo :
      (k : ℝ) / 2 - maximalBarrierHeight t M ≤ oddCount n k := by
    have := (abs_le.mp hbounds).1
    linarith
  have hShi :
      (oddCount n k : ℝ) ≤ (k : ℝ) / 2 + maximalBarrierHeight t M := by
    have := (abs_le.mp hbounds).2
    linarith
  have hphaseHalf := maximalBarrier_phase_half ht.le hnShell
  have hphase :
      (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ t := by
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
    exact hphaseHalf.trans
      (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith))
  have hphaseTwo := maximalBarrier_phase_two ht hstart hnShell
  have hcorr := normalizedCorrection_scaled_le_maximal
    (n := n) (M := M) (k := k) (h := maximalBarrierHeight t M)
    hkM hreg
  have hscale := two_affineConstant_le_n_mul_central hM hkM hnShell
  have hcorrAbsorb :
      2 * ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ maximalBarrierHeight t M *
          (3 : ℝ) ^ maximalBarrierHeight t M) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
    have hphaseSq :
        (3 : ℝ) ^ maximalBarrierHeight t M *
            (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ t := by
      calc
        _ = (3 : ℝ) ^ (2 * maximalBarrierHeight t M) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
        _ = (2 : ℝ) ^ (t * M) := by
          rw [three_rpow_eq_two_rpow_logTwoThree]
          congr 1
          unfold maximalBarrierHeight
          have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
          field_simp [hlog]
        _ = ((2 : ℝ) ^ M) ^ t := by
          rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
        _ ≤ (n : ℝ) ^ t := by
          have hnLower : (2 : ℝ) ^ M ≤ n := by
            exact_mod_cast (mem_dyadicShell.mp hnShell).1
          exact Real.rpow_le_rpow (by positivity) hnLower ht.le
    have hmul :
        2 * (2 + Real.sqrt 3) *
            ((3 : ℝ) ^ maximalBarrierHeight t M *
              (3 : ℝ) ^ maximalBarrierHeight t M) ≤
          ((n : ℝ) * centralOrbitScale k) * (n : ℝ) ^ t :=
      mul_le_mul hscale hphaseSq (by positivity)
        (mul_nonneg (Nat.cast_nonneg n) (centralOrbitScale_pos k).le)
    rw [Real.rpow_add (by exact_mod_cast hnPos : (0 : ℝ) < n),
      Real.rpow_one]
    nlinarith
  exact ⟨orbit_lower_of_fixed_barrier hnPos hSlo hphase,
    orbit_upper_of_fixed_barrier hnPos hShi hphaseTwo hcorr hcorrAbsorb⟩

end

end FirstPassageLinearTransport
