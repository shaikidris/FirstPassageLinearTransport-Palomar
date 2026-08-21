/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Density

/-!
# Varying dyadic-shell density

This module is a source adaptation of the generic dyadic assembly argument
from the frozen V1 repository.  It imports no V1/CEP module.  Its sole input
is convergence of the exceptional proportion on the `M`-th shell.
-/

namespace FirstPassageLinearTransport

open scoped Real Topology BigOperators

noncomputable section

/-- Assemble one set per dyadic shell. -/
def assembleDyadic (S : ℕ → Set ℕ) : Set ℕ :=
  {n | n ∈ S (Nat.log 2 n)}

theorem shellBad_assembleDyadic (S : ℕ → Set ℕ) (M : ℕ) :
    shellBad (assembleDyadic S) M = shellBad (S M) M := by
  classical
  ext n
  simp only [shellBad, Finset.mem_filter, assembleDyadic, Set.mem_setOf_eq]
  by_cases hn : n ∈ dyadicShell M
  · have hlog : Nat.log 2 n = M := by
      rw [mem_dyadicShell] at hn
      exact Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2
    rw [hlog]
  · simp [hn]

/-- Exceptional proportion on one complete dyadic shell. -/
def shellExceptionalRatio (S : Set ℕ) (M : ℕ) : ℝ :=
  ((shellBad S M).card : ℝ) / (2 : ℝ) ^ M

theorem shellExceptionalRatio_nonneg (S : Set ℕ) (M : ℕ) :
    0 ≤ shellExceptionalRatio S M := by
  unfold shellExceptionalRatio
  positivity

theorem shellBad_card_eq_ratio_mul (S : Set ℕ) (M : ℕ) :
    ((shellBad S M).card : ℝ) =
      shellExceptionalRatio S M * (2 : ℝ) ^ M := by
  unfold shellExceptionalRatio
  field_simp

/-- A prefix power-density certificate controls its shell exceptional ratio. -/
theorem shellExceptionalRatio_le_of_powerDense
    {S : Set ℕ} {C D : ℝ} (hS : PowerDense S C D) (M : ℕ) :
    shellExceptionalRatio S M ≤
      2 * C * Real.exp (-(Real.log 2 * D * M)) := by
  have hcardNat := shellBad_card_le_badCount S M
  have hcard :
      ((shellBad S M).card : ℝ) ≤
        (badCount S (2 ^ (M + 1)) : ℝ) := by
    exact_mod_cast hcardNat
  have hbad := hS.bad_bound (2 ^ (M + 1))
    (Nat.one_le_pow (M + 1) 2 (by omega))
  have hraw :
      shellExceptionalRatio S M ≤
        C * ((2 : ℝ) ^ (M + 1)) ^ (1 - D) / (2 : ℝ) ^ M := by
    unfold shellExceptionalRatio
    apply (div_le_div_iff_of_pos_right (by positivity)).2
    exact hcard.trans (by simpa using hbad)
  calc
    shellExceptionalRatio S M
        ≤ C * ((2 : ℝ) ^ (M + 1)) ^ (1 - D) /
            (2 : ℝ) ^ M := hraw
    _ = C * (2 : ℝ) ^ (((M : ℝ) + 1) * (1 - D) - M) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      have hmul :
          ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ (1 - D) =
            (2 : ℝ) ^ (((M + 1 : ℕ) : ℝ) * (1 - D)) :=
        (Real.rpow_mul (by norm_num) _ _).symm
      rw [hmul]
      calc
        C * (2 : ℝ) ^ (((M + 1 : ℕ) : ℝ) * (1 - D)) /
              (2 : ℝ) ^ (M : ℝ)
            = C * ((2 : ℝ) ^ (((M + 1 : ℕ) : ℝ) * (1 - D)) /
              (2 : ℝ) ^ (M : ℝ)) := by ring
        _ = C * (2 : ℝ) ^
              ((((M + 1 : ℕ) : ℝ) * (1 - D)) - (M : ℝ)) := by
              rw [Real.rpow_sub (by norm_num)]
        _ = C * (2 : ℝ) ^ (((M : ℝ) + 1) * (1 - D) - M) := by
              push_cast
              rfl
    _ ≤ C * (2 : ℝ) ^ (1 - D * M) := by
      apply mul_le_mul_of_nonneg_left _ hS.C_pos.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [hS.D_pos]
    _ = 2 * C * Real.exp (-(Real.log 2 * D * M)) := by
      rw [show (1 : ℝ) - D * M = 1 + -(D * M) by ring,
        Real.rpow_add (by norm_num), Real.rpow_one,
        Real.rpow_def_of_pos (by norm_num)]
      ring_nf

theorem sum_two_pow_range (L : ℕ) :
    ∑ j ∈ Finset.range L, (2 : ℝ) ^ j = (2 : ℝ) ^ L - 1 := by
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num

/-- Varying-rate dyadic-shell lemma: shellwise exceptional ratios tending
to zero assemble to a natural-density-one set. -/
theorem naturalDensityOne_assembleDyadic
    (S : ℕ → Set ℕ)
    (hvanish :
      Filter.Tendsto
        (fun M => shellExceptionalRatio (S M) M)
        Filter.atTop (nhds 0)) :
    NaturalDensityOne (assembleDyadic S) := by
  classical
  rw [NaturalDensityOne, Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨M₀, hM₀⟩ :=
    (Metric.tendsto_atTop.1 hvanish) (eps / 8) (by linarith)
  let threshold : ℝ :=
    max ((2 : ℝ) ^ M₀) (8 * (2 : ℝ) ^ M₀ / eps)
  obtain ⟨N₀ : ℕ, hN₀⟩ := exists_nat_gt threshold
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNpos : 0 < N := by
    have hthreshold0 : 0 ≤ threshold := by
      dsimp [threshold]
      positivity
    have hN₀pos : 0 < N₀ := by
      exact_mod_cast lt_of_le_of_lt hthreshold0 hN₀
    omega
  have hNR : threshold < (N : ℝ) := by
    have hN₀R : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    exact hN₀.trans_le hN₀R
  have hNlarge : (2 : ℝ) ^ M₀ < N := by
    change max ((2 : ℝ) ^ M₀) (8 * (2 : ℝ) ^ M₀ / eps) < N at hNR
    exact (le_max_left _ _).trans_lt hNR
  have hNerror : 8 * (2 : ℝ) ^ M₀ / eps < N := by
    change max ((2 : ℝ) ^ M₀) (8 * (2 : ℝ) ^ M₀ / eps) < N at hNR
    exact (le_max_right _ _).trans_lt hNR
  let L := Nat.log 2 N
  have hM₀L : M₀ ≤ L + 1 := by
    by_contra h
    have hLM : L + 1 ≤ M₀ := by omega
    have hpowLe : (2 : ℕ) ^ (L + 1) ≤ 2 ^ M₀ :=
      Nat.pow_le_pow_right (by norm_num) hLM
    have hNlt : N < 2 ^ (L + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) N
    have hNRle : (N : ℝ) < (2 : ℝ) ^ M₀ := by
      exact_mod_cast hNlt.trans_le hpowLe
    linarith
  have hprefix := badCount_le_shell_sum (assembleDyadic S) N
  have hprefixR :
      (badCount (assembleDyadic S) N : ℝ) ≤
        ∑ M ∈ Finset.range (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) := by
    dsimp [L]
    exact_mod_cast hprefix
  rw [← Finset.sum_range_add_sum_Ico
    (fun M => ((shellBad (assembleDyadic S) M).card : ℝ)) hM₀L] at hprefixR
  have hearly :
      ∑ M ∈ Finset.range M₀,
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (2 : ℝ) ^ M₀ := by
    calc
      ∑ M ∈ Finset.range M₀,
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.range M₀, (2 : ℝ) ^ M := by
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
      _ = (2 : ℝ) ^ M₀ - 1 := sum_two_pow_range M₀
      _ ≤ (2 : ℝ) ^ M₀ := by linarith
  have hlate :
      ∑ M ∈ Finset.Ico M₀ (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ) ≤
        (eps / 8) * ((2 : ℝ) ^ (L + 1)) := by
    calc
      ∑ M ∈ Finset.Ico M₀ (L + 1),
          ((shellBad (assembleDyadic S) M).card : ℝ)
          ≤ ∑ M ∈ Finset.Ico M₀ (L + 1),
              (eps / 8) * (2 : ℝ) ^ M := by
            apply Finset.sum_le_sum
            intro M hM
            rw [shellBad_assembleDyadic, shellBad_card_eq_ratio_mul]
            have hratioAbs := hM₀ M (Finset.mem_Ico.mp hM).1
            rw [Real.dist_eq] at hratioAbs
            have hratio :
                shellExceptionalRatio (S M) M < eps / 8 := by
              have hnonneg := shellExceptionalRatio_nonneg (S M) M
              simpa [abs_of_nonneg hnonneg] using hratioAbs
            exact mul_le_mul_of_nonneg_right hratio.le (by positivity)
      _ ≤ (eps / 8) *
          (∑ M ∈ Finset.range (L + 1), (2 : ℝ) ^ M) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              exact Finset.mem_range.2 (Finset.mem_Ico.mp hx).2
            · intro i _ _
              positivity
      _ = (eps / 8) * ((2 : ℝ) ^ (L + 1) - 1) := by
            rw [sum_two_pow_range]
      _ ≤ (eps / 8) * ((2 : ℝ) ^ (L + 1)) := by
            have hpow0 : 0 ≤ (2 : ℝ) ^ (L + 1) := by positivity
            nlinarith
  have hpowN : (2 : ℝ) ^ (L + 1) ≤ 2 * N := by
    have hpowL : (2 : ℕ) ^ L ≤ N :=
      Nat.pow_log_le_self 2 hNpos.ne'
    rw [pow_succ]
    have hcast : (2 : ℝ) * (2 : ℝ) ^ L ≤ 2 * N := by
      exact_mod_cast Nat.mul_le_mul_left 2 hpowL
    nlinarith
  have hbad :
      (badCount (assembleDyadic S) N : ℝ) ≤
        (2 : ℝ) ^ M₀ + eps * N / 4 := by
    calc
      (badCount (assembleDyadic S) N : ℝ)
          ≤ (∑ M ∈ Finset.range M₀,
              ((shellBad (assembleDyadic S) M).card : ℝ)) +
            ∑ M ∈ Finset.Ico M₀ (L + 1),
              ((shellBad (assembleDyadic S) M).card : ℝ) := hprefixR
      _ ≤ (2 : ℝ) ^ M₀ + (eps / 8) * (2 : ℝ) ^ (L + 1) :=
        add_le_add hearly hlate
      _ ≤ (2 : ℝ) ^ M₀ + eps * N / 4 := by
        nlinarith
  have hearlySmall : (2 : ℝ) ^ M₀ < eps * N / 8 := by
    have heps0 : 0 < eps := heps
    rw [div_lt_iff₀ heps0] at hNerror
    nlinarith
  have hratio :
      (badCount (assembleDyadic S) N : ℝ) / N < eps := by
    have hNR0 : (0 : ℝ) < N := by exact_mod_cast hNpos
    rw [div_lt_iff₀ hNR0]
    nlinarith
  have hratio0 :
      0 ≤ (badCount (assembleDyadic S) N : ℝ) / N := by
    positivity
  simpa [Real.dist_eq, abs_of_nonneg hratio0] using hratio

end

end FirstPassageLinearTransport
