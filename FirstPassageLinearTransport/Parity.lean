/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import FirstPassageLinearTransport.Basic

/-!
# Parity coding and exact affine iterates

This module formalizes Propositions 2.2 and 2.3 of the V2 manuscript without
using any result from the released endpoint/CEP development.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

theorem two_mul_shortcut_of_even {n : ℕ} (hn : n % 2 = 0) :
    2 * shortcut n = n := by
  rw [shortcut_of_even hn]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn)

theorem two_mul_shortcut_of_odd {n : ℕ} (hn : n % 2 = 1) :
    2 * shortcut n = 3 * n + 1 := by
  rw [shortcut_of_odd hn]
  apply Nat.mul_div_cancel'
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

/-- A division-free form of one shortcut step. -/
theorem two_mul_shortcut (n : ℕ) :
    2 * shortcut n = 3 ^ (n % 2) * n + n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · simp [hn, two_mul_shortcut_of_even hn]
  · simp [hn, two_mul_shortcut_of_odd hn]

/-- Halving a congruence modulo the next power of two consumes one bit. -/
theorem modEq_of_two_mul {H a b : ℕ}
    (h : 2 * a ≡ 2 * b [MOD 2 ^ (H + 1)]) :
    a ≡ b [MOD 2 ^ H] := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  push_cast at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hp : ((2 : ℤ)) ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [hp] at hk
  linarith

/-- One shortcut step consumes exactly one bit of modular information. -/
theorem shortcut_modEq {H n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ (H + 1)]) :
    shortcut n ≡ shortcut n' [MOD 2 ^ H] := by
  have hdvd : (2 : ℕ) ∣ 2 ^ (H + 1) :=
    dvd_pow_self 2 (Nat.succ_ne_zero H)
  have h2 : n % 2 = n' % 2 := h.of_dvd hdvd
  apply modEq_of_two_mul
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hn' : n' % 2 = 0 := by omega
    rw [two_mul_shortcut_of_even hn, two_mul_shortcut_of_even hn']
    exact h
  · have hn' : n' % 2 = 1 := by omega
    rw [two_mul_shortcut_of_odd hn, two_mul_shortcut_of_odd hn']
    exact Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 h)

/-- After `i` shortcut steps, `i` bits of modular information have been
consumed. -/
theorem orbit_modEq :
    ∀ i j n n' : ℕ, n ≡ n' [MOD 2 ^ (i + j)] →
      orbit i n ≡ orbit i n' [MOD 2 ^ j] := by
  intro i
  induction i with
  | zero =>
      intro j n n' h
      simpa using h
  | succ i ih =>
      intro j n n' h
      rw [orbit_succ, orbit_succ]
      apply shortcut_modEq
      apply ih
      rwa [show i + (j + 1) = i + 1 + j by omega]

/-- The first `M` parity bits depend only on the residue modulo `2^M`. -/
theorem parityPrefix_congr {M n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ M]) :
    (fun i : Fin M => parityBit n i) =
      (fun i : Fin M => parityBit n' i) := by
  funext i
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt i.isLt
  have hstep : orbit i n ≡ orbit i n' [MOD 2 ^ (j + 1)] := by
    apply orbit_modEq
    rwa [show (i : ℕ) + (j + 1) = M by omega]
  have hdvd : (2 : ℕ) ∣ 2 ^ (j + 1) :=
    dvd_pow_self 2 (Nat.succ_ne_zero j)
  apply Fin.ext
  exact hstep.of_dvd hdvd

/-- Iterating after one step agrees with shifting the orbit index. -/
theorem orbit_shortcut (i n : ℕ) : orbit i (shortcut n) = orbit (i + 1) n := by
  simp [orbit, Function.iterate_succ_apply]

/-- Equal parity prefixes force congruence modulo the corresponding power of
two.  This is the injective half of the parity-vector bijection. -/
theorem modEq_of_same_parity_prefix :
    ∀ M n n' : ℕ,
      (∀ i : ℕ, i < M → orbit i n % 2 = orbit i n' % 2) →
        n ≡ n' [MOD 2 ^ M] := by
  intro M
  induction M with
  | zero =>
      intro n n' _h
      simpa using Nat.modEq_one
  | succ M ih =>
      intro n n' h
      have hzero : n % 2 = n' % 2 := by
        simpa using h 0 (by omega)
      have htail :
          ∀ i : ℕ, i < M →
            orbit i (shortcut n) % 2 = orbit i (shortcut n') % 2 := by
        intro i hi
        simpa [orbit_shortcut] using h (i + 1) (by omega)
      have hstep : shortcut n ≡ shortcut n' [MOD 2 ^ M] :=
        ih (shortcut n) (shortcut n') htail
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have hn' : n' % 2 = 0 := by omega
        have hscaled := hstep.mul_left' 2
        rw [two_mul_shortcut_of_even hn, two_mul_shortcut_of_even hn'] at hscaled
        simpa [pow_succ, Nat.mul_comm] using hscaled
      · have hn' : n' % 2 = 1 := by omega
        have hscaled := hstep.mul_left' 2
        rw [two_mul_shortcut_of_odd hn, two_mul_shortcut_of_odd hn'] at hscaled
        have hthree : 3 * n ≡ 3 * n' [MOD 2 ^ (M + 1)] := by
          apply Nat.ModEq.add_right_cancel' 1
          simpa [pow_succ, Nat.mul_comm] using hscaled
        have hcoprime : Nat.Coprime (2 ^ (M + 1)) 3 := by
          exact (by norm_num : Nat.Coprime 2 3).pow_left (M + 1)
        exact hthree.cancel_left_of_coprime hcoprime

/-- The first `M` orbit parities of a residue modulo `2^M`. -/
def parityCode (M : ℕ) (n : Fin (2 ^ M)) : Fin M → Fin 2 :=
  fun i => parityBit n i

theorem parityCode_injective (M : ℕ) : Function.Injective (parityCode M) := by
  intro n n' hcode
  apply Fin.ext
  have hprefix :
      ∀ i : ℕ, i < M → orbit i n % 2 = orbit i n' % 2 := by
    intro i hi
    have hbit := congrFun hcode ⟨i, hi⟩
    exact congrArg Fin.val hbit
  exact (modEq_of_same_parity_prefix M n n' hprefix).eq_of_lt_of_lt n.isLt n'.isLt

/-- Parity vectors give a bijection on every complete dyadic
residue block. -/
theorem parityCode_bijective (M : ℕ) : Function.Bijective (parityCode M) := by
  apply (Fintype.bijective_iff_injective_and_card (parityCode M)).2
  constructor
  · exact parityCode_injective M
  · simp

/-- The parity-vector equivalence, packaged for downstream counting. -/
noncomputable def parityEquiv (M : ℕ) : Fin (2 ^ M) ≃ (Fin M → Fin 2) :=
  Equiv.ofBijective (parityCode M) (parityCode_bijective M)

/-- Integer correction term obtained after multiplying the affine iterate by
`2^k`. -/
def affineCorrection (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k,
    (parityBit n i : ℕ) * 2 ^ i *
      3 ^ (oddCount n k - oddCount n (i + 1))

theorem oddCount_mono {n a b : ℕ} (hab : a ≤ b) :
    oddCount n a ≤ oddCount n b := by
  unfold oddCount
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro i _hi _hib
  omega

theorem affineCorrection_succ (n k : ℕ) :
    affineCorrection n (k + 1) =
      3 ^ (parityBit n k : ℕ) * affineCorrection n k +
        (parityBit n k : ℕ) * 2 ^ k := by
  rw [affineCorrection, Finset.sum_range_succ, affineCorrection]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i + 1 ≤ k := by
    simpa using Finset.mem_range.mp hi
  have hmono : oddCount n (i + 1) ≤ oddCount n k :=
    oddCount_mono hik
  have hexponent :
      oddCount n (k + 1) - oddCount n (i + 1) =
        (oddCount n k - oddCount n (i + 1)) + (parityBit n k : ℕ) := by
    rw [oddCount_succ]
    omega
  rw [hexponent, pow_add]
  ring

/-- Exact affine iteration in division-free form. -/
theorem exact_affine_iterate_scaled (n k : ℕ) :
    2 ^ k * orbit k n =
      3 ^ (oddCount n k) * n + affineCorrection n k := by
  induction k with
  | zero => simp [affineCorrection]
  | succ k ih =>
      have hstep :
          2 * orbit (k + 1) n =
            3 ^ (parityBit n k : ℕ) * orbit k n +
              (parityBit n k : ℕ) := by
        rw [orbit_succ, two_mul_shortcut]
        rfl
      calc
        2 ^ (k + 1) * orbit (k + 1) n =
            2 ^ k * (2 * orbit (k + 1) n) := by
              rw [pow_succ]
              ring
        _ = 2 ^ k *
            (3 ^ (parityBit n k : ℕ) * orbit k n +
              (parityBit n k : ℕ)) := by rw [hstep]
        _ = 3 ^ (parityBit n k : ℕ) * (2 ^ k * orbit k n) +
              (parityBit n k : ℕ) * 2 ^ k := by ring
        _ = 3 ^ (parityBit n k : ℕ) *
              (3 ^ (oddCount n k) * n + affineCorrection n k) +
              (parityBit n k : ℕ) * 2 ^ k := by rw [ih]
        _ = 3 ^ (oddCount n (k + 1)) * n +
              affineCorrection n (k + 1) := by
                rw [oddCount_succ, affineCorrection_succ, pow_add]
                ring

/-- The correction term in the rational normalization printed in the paper. -/
def affineCorrectionQ (n k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k,
    ((parityBit n i : ℕ) : ℚ) *
      (3 : ℚ) ^ (oddCount n k - oddCount n (i + 1)) /
        (2 : ℚ) ^ (k - i)

theorem affineCorrection_cast_div (n k : ℕ) :
    (affineCorrection n k : ℚ) / (2 : ℚ) ^ k = affineCorrectionQ n k := by
  unfold affineCorrection affineCorrectionQ
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by
    exact Nat.le_of_lt (Finset.mem_range.mp hi)
  have hk : k = i + (k - i) := by omega
  rw [hk, pow_add]
  field_simp
  simp

/-- Exact affine iteration in the literal rational form used by the manuscript. -/
theorem exact_affine_iterate (n k : ℕ) :
    (orbit k n : ℚ) =
      (3 : ℚ) ^ (oddCount n k) / (2 : ℚ) ^ k * (n : ℚ) +
        affineCorrectionQ n k := by
  rw [← affineCorrection_cast_div]
  rw [div_mul_eq_mul_div, ← add_div]
  have hpow : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (eq_div_iff hpow).2
  have hscaled :
      (2 : ℚ) ^ k * (orbit k n : ℚ) =
        (3 : ℚ) ^ (oddCount n k) * (n : ℚ) +
          (affineCorrection n k : ℚ) := by
    exact_mod_cast exact_affine_iterate_scaled n k
  simpa [mul_comm] using hscaled

/-- Real-valued exact affine iteration, used by the analytic barrier and
bootstrap layers. -/
theorem exact_affine_iterate_real (n k : ℕ) :
    (orbit k n : ℝ) =
      (3 : ℝ) ^ (oddCount n k) / (2 : ℝ) ^ k * (n : ℝ) +
        ∑ i ∈ Finset.range k,
          ((parityBit n i : ℕ) : ℝ) *
            (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
              (2 : ℝ) ^ (k - i) := by
  have hcorrection :
      (affineCorrection n k : ℝ) / (2 : ℝ) ^ k =
        ∑ i ∈ Finset.range k,
          ((parityBit n i : ℕ) : ℝ) *
            (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
              (2 : ℝ) ^ (k - i) := by
    unfold affineCorrection
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := by
      exact Nat.le_of_lt (Finset.mem_range.mp hi)
    have hk : k = i + (k - i) := by omega
    rw [hk, pow_add]
    field_simp
    simp
  rw [← hcorrection]
  rw [div_mul_eq_mul_div, ← add_div]
  have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (eq_div_iff hpow).2
  have hscaled :
      (2 : ℝ) ^ k * (orbit k n : ℝ) =
        (3 : ℝ) ^ (oddCount n k) * (n : ℝ) +
          (affineCorrection n k : ℝ) := by
    exact_mod_cast exact_affine_iterate_scaled n k
  simpa [mul_comm] using hscaled

end FirstPassageLinearTransport
