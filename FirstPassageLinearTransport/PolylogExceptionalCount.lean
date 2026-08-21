/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.VaryingDensity

/-!
# Polynomial exceptional-count assembly

This module is a generic dyadic summation result.  A shell exceptional ratio
of order `(M+2)^(-kappa)` gives a prefix count with the same logarithmic
power, apart from an explicit early-shell term.  No Collatz input occurs.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology BigOperators

noncomputable section

/-- Exact early/late dyadic decomposition for a polynomial shell profile. -/
theorem badCount_assembleDyadic_le_polylog_profile
    (S : ℕ → Set ℕ) (M₀ N : ℕ) (B kappa : ℝ)
    (hB : 0 ≤ B) (hkappa : 0 ≤ kappa)
    (hshell : ∀ M, M₀ ≤ M →
      shellExceptionalRatio (S M) M ≤
        B * (((M : ℝ) + 2) ^ (-kappa)))
    (hN : 0 < N) (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    (badCount (assembleDyadic S) N : ℝ) ≤
      (2 : ℝ) ^ ((Nat.log 2 N) / 2) +
        2 * B * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
  classical
  let L := Nat.log 2 N
  let K := L / 2
  have hKL : K ≤ L + 1 := by
    dsimp [K]
    omega
  have hprefix := badCount_le_shell_sum (assembleDyadic S) N
  have hprefixR :
      (badCount (assembleDyadic S) N : ℝ) ≤
        ∑ M ∈ Finset.range (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) := by
    dsimp [L]
    exact_mod_cast hprefix
  rw [← Finset.sum_range_add_sum_Ico
    (fun M => ((shellBad (assembleDyadic S) M).card : ℝ)) hKL] at hprefixR
  have hearly :
      ∑ M ∈ Finset.range K,
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (2 : ℝ) ^ K := by
    calc
      ∑ M ∈ Finset.range K,
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        ∑ M ∈ Finset.range K, (2 : ℝ) ^ M := by
          apply Finset.sum_le_sum
          intro M hM
          have hcard : (shellBad (assembleDyadic S) M).card ≤ 2 ^ M := by
            calc
              (shellBad (assembleDyadic S) M).card ≤
                  (dyadicShell M).card := by
                apply Finset.card_le_card
                intro n hn
                exact (Finset.mem_filter.mp hn).1
              _ = 2 ^ M := card_dyadicShell M
          exact_mod_cast hcard
      _ = (2 : ℝ) ^ K - 1 := sum_two_pow_range K
      _ ≤ (2 : ℝ) ^ K := by linarith
  have hlatePoint : ∀ M ∈ Finset.Ico K (L + 1),
      ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 : ℝ) ^ M := by
    intro M hM
    have hKM : K ≤ M := (Finset.mem_Ico.mp hM).1
    have hM₀M : M₀ ≤ M := hM₀.trans hKM
    have hratio := hshell M hM₀M
    have hbase : (K : ℝ) + 2 ≤ (M : ℝ) + 2 := by
      exact_mod_cast Nat.add_le_add_right hKM 2
    have hpow :
        ((M : ℝ) + 2) ^ (-kappa) ≤
          ((K : ℝ) + 2) ^ (-kappa) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
    have hratio' :
        shellExceptionalRatio (S M) M ≤
          B * (((K : ℝ) + 2) ^ (-kappa)) :=
      hratio.trans (mul_le_mul_of_nonneg_left hpow hB)
    rw [shellBad_assembleDyadic, shellBad_card_eq_ratio_mul]
    exact mul_le_mul_of_nonneg_right hratio' (by positivity)
  have hlate :
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 : ℝ) ^ (L + 1) := by
    calc
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        ∑ M ∈ Finset.Ico K (L + 1),
          (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 : ℝ) ^ M := by
            exact Finset.sum_le_sum hlatePoint
      _ = (B * (((K : ℝ) + 2) ^ (-kappa))) *
          ∑ M ∈ Finset.Ico K (L + 1), (2 : ℝ) ^ M := by
            rw [Finset.mul_sum]
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) *
          ∑ M ∈ Finset.range (L + 1), (2 : ℝ) ^ M := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro M hM
              exact Finset.mem_range.2 (Finset.mem_Ico.mp hM).2
            · intro M hM _
              positivity
      _ = (B * (((K : ℝ) + 2) ^ (-kappa))) *
          ((2 : ℝ) ^ (L + 1) - 1) := by
            rw [sum_two_pow_range]
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) *
          (2 : ℝ) ^ (L + 1) := by
            gcongr
            linarith
  have hpowL : (2 : ℝ) ^ L ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have hpowSucc : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
    rw [pow_succ]
    nlinarith
  have hlate' :
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        2 * B * N * (((K : ℝ) + 2) ^ (-kappa)) := by
    calc
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) *
          (2 : ℝ) ^ (L + 1) := hlate
      _ ≤ (B * (((K : ℝ) + 2) ^ (-kappa))) * (2 * N) :=
        mul_le_mul_of_nonneg_left hpowSucc
          (mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
      _ = 2 * B * N * (((K : ℝ) + 2) ^ (-kappa)) := by ring
  calc
    (badCount (assembleDyadic S) N : ℝ) ≤
        ∑ M ∈ Finset.range K,
            ((shellBad (assembleDyadic S) M).card : ℝ) +
          ∑ M ∈ Finset.Ico K (L + 1),
            ((shellBad (assembleDyadic S) M).card : ℝ) := hprefixR
    _ ≤ (2 : ℝ) ^ K +
        2 * B * N * (((K : ℝ) + 2) ^ (-kappa)) :=
      add_le_add hearly hlate'
    _ = (2 : ℝ) ^ ((Nat.log 2 N) / 2) +
        2 * B * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
      rfl

/-- The base-two shell index tends to infinity with the prefix endpoint. -/
theorem tendsto_natLogTwo_atTop :
    Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop := by
  rw [tendsto_atTop]
  intro L
  filter_upwards [eventually_ge_atTop (2 ^ L)] with N hN
  have hlog := Nat.log_mono_right (b := 2) hN
  simpa [Nat.log_pow (by norm_num : 1 < 2)] using hlog

/-- The half-shell cutoff also tends to infinity. -/
theorem tendsto_halfNatLogTwo_atTop :
    Tendsto (fun N : ℕ => (Nat.log 2 N) / 2) atTop atTop :=
  (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
    tendsto_natLogTwo_atTop

/-- The early half of a dyadic prefix is eventually absorbed by every fixed
negative power of the half-shell rank. -/
theorem eventually_two_pow_halfNatLog_le_polylog
    {kappa : ℝ} (_hkappa : 0 ≤ kappa) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ ((Nat.log 2 N) / 2) ≤
        (N : ℝ) *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
  let b : ℝ := Real.log 2 / 2
  have hb : 0 < b := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have htReal : Tendsto
      (fun x : ℝ => x ^ kappa * Real.exp (-(b * x)))
      atTop (nhds 0) :=
    by simpa [neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero kappa b hb
  have hKT := tendsto_halfNatLogTwo_atTop
  have hxT : Tendsto
      (fun N : ℕ => (((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      (tendsto_natCast_atTop_atTop.comp hKT)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ kappa) *
          Real.exp (-(b * ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2))) ≤ 1 :=
    (htReal.comp hxT).eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall,
      (hKT.eventually (eventually_ge_atTop (2 : ℕ))),
      eventually_ge_atTop (1 : ℕ)] with N hsmall hK2 hN1
  let L := Nat.log 2 N
  let K := L / 2
  let x : ℝ := (K : ℝ) + 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hxpow : 0 < x ^ kappa := Real.rpow_pos_of_pos hx _
  have hK2R : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have hrate : b * x ≤ Real.log 2 * (K : ℝ) := by
    dsimp [b, x]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hexp :
      Real.exp (-(Real.log 2 * (K : ℝ))) ≤
        Real.exp (-(b * x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod :
      x ^ kappa * Real.exp (-(Real.log 2 * (K : ℝ))) ≤ 1 := by
    calc
      x ^ kappa * Real.exp (-(Real.log 2 * (K : ℝ))) ≤
          x ^ kappa * Real.exp (-(b * x)) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hx.le _)
      _ ≤ 1 := by simpa [L, K, x, b] using hsmall
  have hxpow_le : x ^ kappa ≤ (2 : ℝ) ^ K := by
    have hmul := mul_le_mul_of_nonneg_right hprod
      (Real.exp_pos (Real.log 2 * (K : ℝ))).le
    have hcancel :
        Real.exp (-(Real.log 2 * (K : ℝ))) *
            Real.exp (Real.log 2 * (K : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hexpPow :
        Real.exp (Real.log 2 * (K : ℝ)) = (2 : ℝ) ^ K := by
      rw [show Real.log 2 * (K : ℝ) = Real.log ((2 : ℝ) ^ K) by
        rw [Real.log_pow]
        ring]
      exact Real.exp_log (by positivity)
    calc
      x ^ kappa = x ^ kappa * 1 := by ring
      _ = x ^ kappa *
          (Real.exp (-(Real.log 2 * (K : ℝ))) *
            Real.exp (Real.log 2 * (K : ℝ))) := by rw [hcancel]
      _ = (x ^ kappa * Real.exp (-(Real.log 2 * (K : ℝ)))) *
            Real.exp (Real.log 2 * (K : ℝ)) := by ring
      _ ≤ 1 * Real.exp (Real.log 2 * (K : ℝ)) := hmul
      _ = (2 : ℝ) ^ K := by rw [one_mul, hexpPow]
  have hone : 1 ≤ (2 : ℝ) ^ K * x ^ (-kappa) := by
    rw [Real.rpow_neg hx.le]
    apply (le_div_iff₀ hxpow).2
    simpa using hxpow_le
  have hKK : (2 : ℝ) ^ K ≤
      (2 : ℝ) ^ (2 * K) * x ^ (-kappa) := by
    calc
      (2 : ℝ) ^ K ≤ (2 : ℝ) ^ K *
          ((2 : ℝ) ^ K * x ^ (-kappa)) := by
        simpa using mul_le_mul_of_nonneg_left hone (by positivity :
          0 ≤ (2 : ℝ) ^ K)
      _ = ((2 : ℝ) ^ K * (2 : ℝ) ^ K) * x ^ (-kappa) := by ring
      _ = (2 : ℝ) ^ (K + K) * x ^ (-kappa) := by rw [pow_add]
      _ = (2 : ℝ) ^ (2 * K) * x ^ (-kappa) := by
        congr 2
        omega
  have h2KL : 2 * K ≤ L := by
    dsimp [K]
    omega
  have hpowKN : (2 : ℝ) ^ (2 * K) ≤ (N : ℝ) := by
    have hpowNat : 2 ^ (2 * K) ≤ N :=
      (Nat.pow_le_pow_right (by omega) h2KL).trans
        (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
    exact_mod_cast hpowNat
  calc
    (2 : ℝ) ^ ((Nat.log 2 N) / 2) = (2 : ℝ) ^ K := by rfl
    _ ≤ (2 : ℝ) ^ (2 * K) * x ^ (-kappa) := hKK
    _ ≤ (N : ℝ) * x ^ (-kappa) :=
      mul_le_mul_of_nonneg_right hpowKN (Real.rpow_nonneg hx.le _)
    _ = (N : ℝ) *
        ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
      rfl

/-- Eventual quantitative prefix count with the same half-logarithmic power
as the shell profile. -/
theorem eventually_badCount_assembleDyadic_le_polylog_profile
    (S : ℕ → Set ℕ) (M₀ : ℕ) (B kappa : ℝ)
    (hB : 0 ≤ B) (hkappa : 0 ≤ kappa)
    (hshell : ∀ M, M₀ ≤ M →
      shellExceptionalRatio (S M) M ≤
        B * (((M : ℝ) + 2) ^ (-kappa))) :
    ∀ᶠ N : ℕ in atTop,
      (badCount (assembleDyadic S) N : ℝ) ≤
        (1 + 2 * B) * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
  have hEarly := eventually_two_pow_halfNatLog_le_polylog hkappa
  have hHalfT := tendsto_halfNatLogTwo_atTop
  have hM₀ : ∀ᶠ N : ℕ in atTop, M₀ ≤ (Nat.log 2 N) / 2 :=
    hHalfT.eventually (eventually_ge_atTop M₀)
  filter_upwards [hEarly, hM₀, eventually_ge_atTop (1 : ℕ)]
    with N hEarly hM₀ hN1
  have hraw := badCount_assembleDyadic_le_polylog_profile
    S M₀ N B kappa hB hkappa hshell (by omega) hM₀
  let xpow : ℝ :=
    ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa)
  calc
    (badCount (assembleDyadic S) N : ℝ) ≤
        (2 : ℝ) ^ ((Nat.log 2 N) / 2) +
          2 * B * N * xpow := by simpa [xpow] using hraw
    _ ≤ (N : ℝ) * xpow + 2 * B * N * xpow :=
      by
        simpa [add_comm] using
          add_le_add_right (by simpa [xpow] using hEarly)
            (2 * B * (N : ℝ) * xpow)
    _ = (1 + 2 * B) * N * xpow := by ring
    _ = (1 + 2 * B) * N *
        ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
      rfl

/-- The explicit half-base-two-logarithmic scale is eventually bounded by
the corresponding negative power of the natural logarithm.  The constant
`(2 * log 2)^kappa` records the entire change of logarithm and the half-shell
split. -/
theorem eventually_halfNatLog_profile_le_natLog
    {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    ∀ᶠ N : ℕ in atTop,
      ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) ≤
        (2 * Real.log 2) ^ kappa * (Real.log N) ^ (-kappa) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN2
  let L := Nat.log 2 N
  let K := L / 2
  let x : ℝ := (K : ℝ) + 2
  let q : ℝ := 2 * Real.log 2
  have hNpos : 0 < N := by omega
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hLX : (N : ℝ) < (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
  have hlogUpper : Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have h := Real.log_le_log hNRpos (le_of_lt hLX)
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
  have hLhalfNat : L ≤ 2 * K + 1 := by
    dsimp [K]
    omega
  have hLhalf : (L : ℝ) + 1 ≤ 2 * x := by
    have hcast : (L : ℝ) ≤ 2 * (K : ℝ) + 1 := by
      exact_mod_cast hLhalfNat
    dsimp [x]
    linarith
  have hlogx : Real.log N ≤ q * x := by
    calc
      Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := hlogUpper
      _ ≤ (2 * x) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hLhalf hlog2.le
      _ = q * x := by
        dsimp [q]
        ring
  have hqx : Real.log N / q ≤ x := (div_le_iff₀ hq).2 (by
    simpa [mul_comm] using hlogx)
  have hmono : x ^ (-kappa) ≤ (Real.log N / q) ^ (-kappa) :=
    Real.rpow_le_rpow_of_exponent_nonpos
      (div_pos hlogN hq) hqx (neg_nonpos.mpr hkappa)
  have hrewrite :
      (Real.log N / q) ^ (-kappa) =
        q ^ kappa * (Real.log N) ^ (-kappa) := by
    rw [Real.div_rpow hlogN.le hq.le]
    rw [Real.rpow_neg hq.le]
    field_simp
  simpa [L, K, x, q, hrewrite] using hmono.trans_eq hrewrite


end

end FirstPassageLinearTransport
