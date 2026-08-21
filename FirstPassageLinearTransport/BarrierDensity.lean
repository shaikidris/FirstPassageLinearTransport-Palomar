/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import FirstPassageLinearTransport.Envelope

/-!
# Density of the maximal-barrier orbit envelope

This module transfers the finite Boolean-walk tail through the parity
bijection, absorbs the finite startup regime, and applies the generic V2
shell-to-global density bridge.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- The paper's set `W_t`: every time through the dyadic scale of `n`
satisfies the two-sided central orbit envelope. -/
def initialWindowGood (t : ℝ) : Set ℕ :=
  {n | ∀ k : ℕ, k ≤ Nat.log 2 n →
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t)}

/-- Failure of the orbit envelope somewhere in one shell. -/
noncomputable def shellInitialWindowBad (M : ℕ) (t : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n =>
    ∃ k : ℕ, k ≤ M ∧
      ((orbit k n : ℝ) < centralOrbitScale k * (n : ℝ) ^ (1 - t) ∨
        centralOrbitScale k * (n : ℝ) ^ (1 + t) < (orbit k n : ℝ)))

theorem log_two_eq_of_mem_dyadicShell {M n : ℕ}
    (hn : n ∈ dyadicShell M) : Nat.log 2 n = M := by
  have hb := mem_dyadicShell.mp hn
  exact Nat.log_eq_of_pow_le_of_lt_pow hb.1 hb.2

theorem shellBad_initialWindowGood (t : ℝ) (M : ℕ) :
    shellBad (initialWindowGood t) M = shellInitialWindowBad M t := by
  classical
  ext n
  constructor
  · intro hn
    rw [shellBad, Finset.mem_filter] at hn
    have hlog := log_two_eq_of_mem_dyadicShell hn.1
    rw [initialWindowGood, Set.mem_setOf_eq] at hn
    push_neg at hn
    rcases hn.2 with ⟨k, hk, hfail⟩
    rw [shellInitialWindowBad, Finset.mem_filter]
    refine ⟨hn.1, k, by simpa [hlog] using hk, ?_⟩
    by_cases hlower :
        centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ)
    · exact Or.inr (hfail hlower)
    · exact Or.inl (lt_of_not_ge hlower)
  · intro hn
    rw [shellInitialWindowBad, Finset.mem_filter] at hn
    have hlog := log_two_eq_of_mem_dyadicShell hn.1
    rw [shellBad, Finset.mem_filter]
    refine ⟨hn.1, ?_⟩
    rw [initialWindowGood, Set.mem_setOf_eq]
    push_neg
    rcases hn.2 with ⟨k, hk, hfail⟩
    refine ⟨k, by simpa [hlog] using hk, ?_⟩
    intro hlower
    rcases hfail with hfail | hfail
    · exact False.elim ((not_lt_of_ge hlower) hfail)
    · exact hfail

/-- Shell-rate constant from the optimized maximal barrier. -/
def maximalBarrierC0 : ℝ := 1 / (2 * logTwoThree ^ 2)

theorem maximalBarrierC0_pos : 0 < maximalBarrierC0 := by
  unfold maximalBarrierC0
  exact div_pos (by norm_num)
    (mul_pos (by norm_num) (sq_pos_of_pos logTwoThree_pos))

theorem maximalBarrierC0_lt_log_two :
    maximalBarrierC0 < Real.log 2 := by
  have hlg : 1 < logTwoThree := logTwoThree_one_lt
  have hc : maximalBarrierC0 < 1 / 2 := by
    unfold maximalBarrierC0
    have hsq : 1 < logTwoThree ^ 2 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hlogLower : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  exact hc.trans hlogLower

/-- Concrete all-depth shell tail at the barrier height selected by `t`. -/
theorem card_shellMaximalParityBad_le_concrete
    {M : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    ((shellMaximalParityBad M (maximalBarrierHeight t M)).card : ℝ) ≤
      2 * Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by
  classical
  cases M with
  | zero =>
      have hcard :
          (shellMaximalParityBad 0 (maximalBarrierHeight t 0)).card ≤ 1 := by
        calc
          _ ≤ (dyadicShell 0).card := by
            apply Finset.card_le_card
            intro n hn
            exact (Finset.mem_filter.mp hn).1
          _ = 1 := by norm_num [card_dyadicShell]
      have hcardR :
          ((shellMaximalParityBad 0
            (maximalBarrierHeight t 0)).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard
      norm_num at hcardR ⊢
      linarith
  | succ M =>
      have hraw := card_shellMaximalParityBad_le
        (M := M + 1) (h := maximalBarrierHeight t (M + 1))
        (maximalBarrierHeight_nonneg ht) (Nat.succ_pos M)
      have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
      have hexp :
          -(2 * maximalBarrierHeight t (M + 1) ^ 2 /
              ((M + 1 : ℕ) : ℝ)) =
            -(maximalBarrierC0 * t ^ 2 * ((M + 1 : ℕ) : ℝ)) := by
        unfold maximalBarrierHeight maximalBarrierC0
        have hM : (0 : ℝ) < M + 1 := by positivity
        field_simp [hlog]
      calc
        ((shellMaximalParityBad (M + 1)
          (maximalBarrierHeight t (M + 1))).card : ℝ) ≤
            (2 : ℝ) ^ (M + 1 + 1) *
              Real.exp (-(2 * maximalBarrierHeight t (M + 1) ^ 2 /
                ((M + 1 : ℕ) : ℝ))) := hraw
        _ = 2 * Real.exp
              (-(maximalBarrierC0 * t ^ 2 * ((M + 1 : ℕ) : ℝ))) *
              (2 : ℝ) ^ (M + 1) := by
          rw [hexp, pow_succ]
          ring

theorem shellInitialWindowBad_subset_maximal
    {M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M) :
    shellInitialWindowBad M t ⊆
      shellMaximalParityBad M (maximalBarrierHeight t M) := by
  classical
  intro n hn
  rw [shellInitialWindowBad, Finset.mem_filter] at hn
  rw [shellMaximalParityBad, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  intro hreg
  rcases hn.2 with ⟨k, hkM, hfail⟩
  have henv := orbit_envelope_of_maximalBarrier
    ht hM hstart hkM hn.1 hreg
  rcases hfail with hlower | hupper
  · exact (not_lt_of_ge henv.1) hlower
  · exact (not_lt_of_ge henv.2) hupper

/-- Uniform shell prefactor after absorbing the finite startup regime. -/
def quadraticWindowShellConstant : ℝ :=
  2 * Real.exp (4 * maximalBarrierC0)

theorem quadraticWindowShellConstant_pos :
    0 < quadraticWindowShellConstant := by
  unfold quadraticWindowShellConstant
  positivity

theorem quadratic_startup_exponent_le
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    maximalBarrierC0 * t ^ 2 * M ≤ 4 * maximalBarrierC0 := by
  rcases not_and_or.mp hsmall with hM | htM
  · have hMR : (M : ℝ) ≤ 4 := by exact_mod_cast (by omega : M ≤ 4)
    have ht2 : t ^ 2 ≤ (1 : ℝ) := by nlinarith [sq_nonneg t]
    have hprod : t ^ 2 * (M : ℝ) ≤ 1 * 4 :=
      mul_le_mul ht2 hMR (Nat.cast_nonneg M) (by norm_num)
    nlinarith [maximalBarrierC0_pos.le]
  · have htMR : t * (M : ℝ) ≤ 2 := le_of_not_ge htM
    have hprod : t * (t * (M : ℝ)) ≤ 1 * 2 :=
      mul_le_mul ht1 htMR
        (mul_nonneg ht0.le (Nat.cast_nonneg M)) (by norm_num)
    nlinarith [maximalBarrierC0_pos.le]

theorem one_le_quadratic_startup_factor
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    1 ≤ quadraticWindowShellConstant *
      Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) := by
  have hexp := quadratic_startup_exponent_le ht0 ht1 hsmall
  have hnonneg :
      0 ≤ 4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ) := by
    linarith
  unfold quadraticWindowShellConstant
  have hone :
      1 ≤ Real.exp
        (4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ)) :=
    Real.one_le_exp hnonneg
  calc
    1 ≤ 2 * Real.exp
        (4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ)) := by
      nlinarith
    _ = 2 * Real.exp (4 * maximalBarrierC0) *
        Real.exp (-(maximalBarrierC0 * t ^ 2 * (M : ℝ))) := by
      rw [show
        4 * maximalBarrierC0 - maximalBarrierC0 * t ^ 2 * (M : ℝ) =
          4 * maximalBarrierC0 +
            (-(maximalBarrierC0 * t ^ 2 * (M : ℝ))) by ring,
        Real.exp_add]
      ring

/-- All-shell quadratic exceptional count. -/
theorem card_shellInitialWindowBad_le_quadratic
    {M : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((shellInitialWindowBad M t).card : ℝ) ≤
      quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by
  classical
  by_cases hlarge : 4 ≤ M ∧ 2 ≤ t * M
  · have hsubset := shellInitialWindowBad_subset_maximal
      ht0 hlarge.1 hlarge.2
    have hcard :
        (shellInitialWindowBad M t).card ≤
          (shellMaximalParityBad M (maximalBarrierHeight t M)).card :=
      Finset.card_le_card hsubset
    have hcardR :
        ((shellInitialWindowBad M t).card : ℝ) ≤
          ((shellMaximalParityBad M
            (maximalBarrierHeight t M)).card : ℝ) := by exact_mod_cast hcard
    have htail := card_shellMaximalParityBad_le_concrete (M := M) ht0.le
    calc
      _ ≤ ((shellMaximalParityBad M
          (maximalBarrierHeight t M)).card : ℝ) := hcardR
      _ ≤ 2 * Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
          (2 : ℝ) ^ M := htail
      _ ≤ quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
          (2 : ℝ) ^ M := by
        have hK : (2 : ℝ) ≤ quadraticWindowShellConstant := by
          unfold quadraticWindowShellConstant
          have := Real.one_le_exp
            (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
              maximalBarrierC0_pos.le)
          nlinarith
        gcongr
  · have hcard :
        (shellInitialWindowBad M t).card ≤ (dyadicShell M).card := by
      apply Finset.card_le_card
      intro n hn
      exact (Finset.mem_filter.mp hn).1
    have hcardR :
        ((shellInitialWindowBad M t).card : ℝ) ≤ (2 : ℝ) ^ M := by
      rw [card_dyadicShell] at hcard
      exact_mod_cast hcard
    have hfactor := one_le_quadratic_startup_factor ht0 ht1 hlarge
    calc
      _ ≤ (2 : ℝ) ^ M := hcardR
      _ = 1 * (2 : ℝ) ^ M := by ring
      _ ≤ (quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 * t ^ 2 * M))) *
          (2 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring

/-- Density exponent supplied by a quadratic-width maximal barrier. -/
def quadraticWindowDensityRate (t : ℝ) : ℝ :=
  maximalBarrierC0 * t ^ 2 / Real.log 2

/-- Global missing-count prefactor obtained by summing the shell estimates. -/
def quadraticWindowGlobalConstant (t : ℝ) : ℝ :=
  2 * quadraticWindowShellConstant /
    (2 * Real.exp (-(maximalBarrierC0 * t ^ 2)) - 1)

/-- The maximal-barrier set is quantitatively dense. -/
theorem initialWindowGood_powerDense
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    PowerDense (initialWindowGood t)
      (quadraticWindowGlobalConstant t)
      (quadraticWindowDensityRate t) := by
  have hc : 0 < maximalBarrierC0 * t ^ 2 :=
    mul_pos maximalBarrierC0_pos (sq_pos_of_pos ht0)
  have hclt : maximalBarrierC0 * t ^ 2 < Real.log 2 := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    have hle : maximalBarrierC0 * t ^ 2 ≤ maximalBarrierC0 :=
      mul_le_of_le_one_right maximalBarrierC0_pos.le ht2
    exact hle.trans_lt maximalBarrierC0_lt_log_two
  unfold quadraticWindowGlobalConstant quadraticWindowDensityRate
  apply powerDense_of_shell_bound
    quadraticWindowShellConstant_pos hc hclt
  intro M
  rw [shellBad_initialWindowGood]
  simpa [mul_assoc] using
    (card_shellInitialWindowBad_le_quadratic (M := M) ht0 ht1)

end

end FirstPassageLinearTransport
