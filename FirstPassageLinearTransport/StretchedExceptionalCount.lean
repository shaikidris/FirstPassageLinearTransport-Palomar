/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import FirstPassageLinearTransport.VaryingDensity

/-!
# Stretched exceptional counts

This module is the V2 source adaptation of the generic dyadic summation
argument from the frozen predecessor repository.  It imports no predecessor
module and contains no Collatz input.

If the exceptional proportion on shell `M` is at most

`A * exp (-c * (M + 4)^alpha)`,

then the exceptional count up to `N` has the same stretched-exponential
power, with explicit prefactor `1 + 2 * A`.
-/

set_option maxHeartbeats 1000000

namespace FirstPassageLinearTransport

namespace QuantitativeDensity

open scoped Real Topology BigOperators

noncomputable section

/-- The harmless four-shell shift used to absorb finite startup effects. -/
def stretchedShellScale (M : ℕ) : ℝ :=
  (M : ℝ) + 4

theorem stretchedShellScale_pos (M : ℕ) :
    0 < stretchedShellScale M := by
  unfold stretchedShellScale
  positivity

/-- A conservative rate paying simultaneously for the late-shell majorant
and the early-shell cutoff. -/
def stretchedDyadicRate (c : ℝ) : ℝ :=
  min (c / 4) (Real.log 2 / 4)

theorem stretchedDyadicRate_pos {c : ℝ} (hc : 0 < c) :
    0 < stretchedDyadicRate c := by
  unfold stretchedDyadicRate
  exact lt_min (div_pos hc (by norm_num))
    (div_pos (Real.log_pos (by norm_num)) (by norm_num))

/-- Quantitative dyadic summation preserving an arbitrary power
`0 < alpha <= 1`. -/
theorem badCount_assembleDyadic_le_stretched_rate
    (S : ℕ → Set ℕ) (M₀ N : ℕ) (A c alpha : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hshell :
      ∀ M, M₀ ≤ M →
        shellExceptionalRatio (S M) M ≤
          A * Real.exp
            (-c * (stretchedShellScale M) ^ alpha))
    (hN : 0 < N)
    (hL1 : 1 ≤ Nat.log 2 N)
    (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    (badCount (assembleDyadic S) N : ℝ) ≤
      (1 + 2 * A) * N *
        Real.exp
          (-(stretchedDyadicRate c) *
            (Nat.log 2 N : ℝ) ^ alpha) := by
  classical
  let L := Nat.log 2 N
  let K := L / 2
  let rate := stretchedDyadicRate c
  have hrate0 : 0 < rate := by
    dsimp [rate]
    exact stretchedDyadicRate_pos hc
  have hrateC : rate ≤ c / 4 := by
    dsimp [rate, stretchedDyadicRate]
    exact min_le_left _ _
  have hrateLog : rate ≤ Real.log 2 / 4 := by
    dsimp [rate, stretchedDyadicRate]
    exact min_le_right _ _
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
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.range K, (2 : ℝ) ^ M := by
            apply Finset.sum_le_sum
            intro M hMr
            have hcard :
                (shellBad (assembleDyadic S) M).card ≤ 2 ^ M := by
              calc
                (shellBad (assembleDyadic S) M).card
                    ≤ (dyadicShell M).card := by
                      apply Finset.card_le_card
                      intro x hx
                      exact (Finset.mem_filter.mp hx).1
                _ = 2 ^ M := card_dyadicShell M
            exact_mod_cast hcard
      _ = (2 : ℝ) ^ K - 1 := sum_two_pow_range K
      _ ≤ (2 : ℝ) ^ K := by linarith
  have hshiftMono :
      ∀ M, K ≤ M →
        Real.exp (-c * (stretchedShellScale M) ^ alpha) ≤
          Real.exp (-c * (stretchedShellScale K) ^ alpha) := by
    intro M hKM
    apply Real.exp_le_exp.2
    have hshift :
        stretchedShellScale K ≤ stretchedShellScale M := by
      unfold stretchedShellScale
      exact_mod_cast Nat.add_le_add_right hKM 4
    have hpow :
        (stretchedShellScale K) ^ alpha ≤
          (stretchedShellScale M) ^ alpha :=
      Real.rpow_le_rpow (stretchedShellScale_pos K).le hshift halpha0.le
    nlinarith [hc]
  have hlate :
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        A * Real.exp (-c * (stretchedShellScale K) ^ alpha) *
          (2 : ℝ) ^ (L + 1) := by
    calc
      ∑ M ∈ Finset.Ico K (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.Ico K (L + 1),
              (A * Real.exp
                (-c * (stretchedShellScale K) ^ alpha)) *
                (2 : ℝ) ^ M := by
            apply Finset.sum_le_sum
            intro M hM
            rw [shellBad_assembleDyadic, shellBad_card_eq_ratio_mul]
            have hKM := (Finset.mem_Ico.mp hM).1
            have hM₀M : M₀ ≤ M := hM₀.trans hKM
            exact mul_le_mul_of_nonneg_right
              ((hshell M hM₀M).trans
                (mul_le_mul_of_nonneg_left
                  (hshiftMono M hKM) hA))
              (by positivity)
      _ ≤ (A * Real.exp
              (-c * (stretchedShellScale K) ^ alpha)) *
            (∑ M ∈ Finset.range (L + 1), (2 : ℝ) ^ M) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_range.2 (Finset.mem_Ico.mp hx).2
          · intro i _ _
            positivity
      _ = (A * Real.exp
              (-c * (stretchedShellScale K) ^ alpha)) *
            ((2 : ℝ) ^ (L + 1) - 1) := by
          rw [sum_two_pow_range]
      _ ≤ A * Real.exp
              (-c * (stretchedShellScale K) ^ alpha) *
            (2 : ℝ) ^ (L + 1) := by
          have hcoef :
              0 ≤ A * Real.exp
                (-c * (stretchedShellScale K) ^ alpha) := by
            positivity
          nlinarith [show 0 ≤ (2 : ℝ) ^ (L + 1) by positivity]
  have hpowN : (2 : ℝ) ^ L ≤ N := by
    dsimp [L]
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have hpowSuccN : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
    rw [pow_succ]
    nlinarith
  have hLK : L ≤ 2 * K + 1 := by
    dsimp [K]
    omega
  have hquarter :
      (L : ℝ) / 4 ≤ stretchedShellScale K := by
    have hcast : (L : ℝ) ≤ 2 * K + 1 := by exact_mod_cast hLK
    unfold stretchedShellScale
    nlinarith
  have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hquarterPow :
      (L : ℝ) ^ alpha / 4 ≤
        (stretchedShellScale K) ^ alpha := by
    have hbase :
        ((L : ℝ) / 4) ^ alpha ≤
          (stretchedShellScale K) ^ alpha :=
      Real.rpow_le_rpow (by positivity) hquarter halpha0.le
    have hfour :
        (4 : ℝ) ^ alpha ≤ 4 := by
      have h :=
        Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ 4 by norm_num) halpha1
      simpa using h
    have hfourPos : 0 < (4 : ℝ) ^ alpha := by positivity
    have hdiv :
        (L : ℝ) ^ alpha / 4 ≤
          (L : ℝ) ^ alpha / (4 : ℝ) ^ alpha := by
      exact div_le_div_of_nonneg_left
        (Real.rpow_nonneg hL0 _) hfourPos hfour
    rw [← Real.div_rpow hL0 (by norm_num : (0 : ℝ) ≤ 4)] at hdiv
    exact hdiv.trans hbase
  have hhighRate :
      Real.exp (-c * (stretchedShellScale K) ^ alpha) ≤
        Real.exp (-rate * (L : ℝ) ^ alpha) := by
    apply Real.exp_le_exp.2
    have hpow0 : 0 ≤ (L : ℝ) ^ alpha :=
      Real.rpow_nonneg hL0 _
    nlinarith
  have hLpowLe :
      (L : ℝ) ^ alpha ≤ (L : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_exponent_le hLone halpha1
    simpa using h
  have hlogLinear :
      rate * (L : ℝ) ^ alpha ≤
        Real.log 2 * (L : ℝ) / 2 := by
    have hstep :
        rate * (L : ℝ) ^ alpha ≤
          (Real.log 2 / 4) * (L : ℝ) := by
      calc
        rate * (L : ℝ) ^ alpha
            ≤ (Real.log 2 / 4) * (L : ℝ) ^ alpha :=
          mul_le_mul_of_nonneg_right hrateLog
            (Real.rpow_nonneg hL0 _)
        _ ≤ (Real.log 2 / 4) * (L : ℝ) :=
          mul_le_mul_of_nonneg_left hLpowLe
            (div_nonneg (Real.log_pos (by norm_num)).le (by norm_num))
    nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num), hL0]
  have hKLhalf : (K : ℝ) ≤ (L : ℝ) / 2 := by
    have htwo : 2 * K ≤ L := by
      dsimp [K]
      exact Nat.mul_div_le L 2
    have htwoR : (2 : ℝ) * K ≤ L := by exact_mod_cast htwo
    linarith
  have hpowK :
      (2 : ℝ) ^ K ≤ (2 : ℝ) ^ ((L : ℝ) / 2) := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le
        (x := (2 : ℝ)) (by norm_num) hKLhalf
  have hexpIdentity :
      (2 : ℝ) ^ ((L : ℝ) / 2) =
        (2 : ℝ) ^ L *
          Real.exp (-(Real.log 2 * L / 2)) := by
    have hpowL :
        (2 : ℝ) ^ L = Real.exp (Real.log 2 * L) := by
      rw [← Real.rpow_natCast,
        Real.rpow_def_of_pos (by norm_num)]
    rw [Real.rpow_def_of_pos (by norm_num), hpowL]
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpEarly :
      Real.exp (-(Real.log 2 * L / 2)) ≤
        Real.exp (-rate * (L : ℝ) ^ alpha) :=
    Real.exp_le_exp.2 (by linarith)
  have hearlyRate :
      (2 : ℝ) ^ K ≤
        N * Real.exp (-rate * (L : ℝ) ^ alpha) := by
    calc
      (2 : ℝ) ^ K
          ≤ (2 : ℝ) ^ ((L : ℝ) / 2) := hpowK
      _ = (2 : ℝ) ^ L *
            Real.exp (-(Real.log 2 * L / 2)) := hexpIdentity
      _ ≤ N * Real.exp (-rate * (L : ℝ) ^ alpha) :=
        mul_le_mul hpowN hexpEarly
          (Real.exp_nonneg _) (by positivity)
  have hlateRate :
      A * Real.exp (-c * (stretchedShellScale K) ^ alpha) *
          (2 : ℝ) ^ (L + 1) ≤
        2 * A * N *
          Real.exp (-rate * (L : ℝ) ^ alpha) := by
    calc
      A * Real.exp (-c * (stretchedShellScale K) ^ alpha) *
          (2 : ℝ) ^ (L + 1)
          ≤ A * Real.exp (-rate * (L : ℝ) ^ alpha) *
              (2 : ℝ) ^ (L + 1) := by
            gcongr
      _ ≤ A * Real.exp (-rate * (L : ℝ) ^ alpha) *
              (2 * N) := by
            gcongr
      _ = 2 * A * N *
            Real.exp (-rate * (L : ℝ) ^ alpha) := by ring
  calc
    (badCount (assembleDyadic S) N : ℝ)
        ≤ (∑ M ∈ Finset.range K,
            ((shellBad (assembleDyadic S) M).card : ℝ)) +
          ∑ M ∈ Finset.Ico K (L + 1),
            ((shellBad (assembleDyadic S) M).card : ℝ) := hprefixR
    _ ≤ (2 : ℝ) ^ K +
          A * Real.exp (-c * (stretchedShellScale K) ^ alpha) *
            (2 : ℝ) ^ (L + 1) :=
      add_le_add hearly hlate
    _ ≤ N * Real.exp (-rate * (L : ℝ) ^ alpha) +
          2 * A * N * Real.exp (-rate * (L : ℝ) ^ alpha) :=
      add_le_add hearlyRate hlateRate
    _ = _ := by ring

/-- Natural-log form of the stretched shell summation. -/
theorem badCount_assembleDyadic_le_stretched_log
    (S : ℕ → Set ℕ) (M₀ N : ℕ) (A c alpha : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hshell :
      ∀ M, M₀ ≤ M →
        shellExceptionalRatio (S M) M ≤
          A * Real.exp
            (-c * (stretchedShellScale M) ^ alpha))
    (hN : 0 < N)
    (hL2 : 2 ≤ Nat.log 2 N)
    (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    (badCount (assembleDyadic S) N : ℝ) ≤
      (1 + 2 * A) * N *
        Real.exp
          (-(stretchedDyadicRate c / 2) *
            (Real.log N) ^ alpha) := by
  let L := Nat.log 2 N
  have hbase :=
    badCount_assembleDyadic_le_stretched_rate
      S M₀ N A c alpha hA hc halpha0 halpha1 hshell
      hN (by omega) hM₀
  have hNupperNat : N < 2 ^ (L + 1) := by
    dsimp [L]
    exact Nat.lt_pow_succ_log_self (by norm_num) N
  have hNupper : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast hNupperNat.le
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogUpper :
      Real.log N ≤ ((L : ℝ) + 1) * Real.log 2 := by
    have h :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hNR0)
        (Set.mem_Ioi.mpr
          (by positivity : 0 < (2 : ℝ) ^ (L + 1)))
        hNupper
    rw [Real.log_pow] at h
    push_cast at h
    simpa [mul_comm] using h
  have hL2R : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  have hlogTwoLt : Real.log 2 < 1 :=
    (Real.log_two_lt_d9).trans (by norm_num)
  have hlogTwoL :
      Real.log N ≤ 2 * (L : ℝ) := by
    nlinarith
  have hL0 : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hlogN0 : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have htwo :
      (2 : ℝ) ^ alpha ≤ 2 := by
    have h :=
      Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) halpha1
    simpa using h
  have hpowCompare :
      (Real.log N) ^ alpha ≤
        2 * (L : ℝ) ^ alpha := by
    calc
      (Real.log N) ^ alpha
          ≤ (2 * (L : ℝ)) ^ alpha :=
        Real.rpow_le_rpow hlogN0 hlogTwoL halpha0.le
      _ = (2 : ℝ) ^ alpha * (L : ℝ) ^ alpha := by
        rw [Real.mul_rpow (by norm_num) hL0]
      _ ≤ 2 * (L : ℝ) ^ alpha :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hL0 _)
  have hexpCompare :
      Real.exp
          (-(stretchedDyadicRate c) *
            (L : ℝ) ^ alpha) ≤
        Real.exp
          (-(stretchedDyadicRate c / 2) *
            (Real.log N) ^ alpha) := by
    apply Real.exp_le_exp.2
    have hrate0 := stretchedDyadicRate_pos hc
    nlinarith
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hexpCompare
      (mul_nonneg
        (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hA))
        (Nat.cast_nonneg N)))

end

end QuantitativeDensity

end FirstPassageLinearTransport
