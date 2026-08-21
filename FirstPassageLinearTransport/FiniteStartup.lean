/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import FirstPassageLinearTransport.Density

/-!
# Finite-startup absorption for quantitative density statements

This module converts an eventual inclusion of a quantitative good set into a
literal exceptional-count estimate for the consumer set.  The only loss is a
finite change of constant and replacement of the logarithmic exponent by its
minimum with one.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- If `S` is eventually contained in `T`, then the bad prefix of `T` is
bounded by the bad prefix of `S` plus the finite startup interval. -/
theorem badCount_le_add_of_tail_subset
    (S T : Set ℕ) (N X : ℕ)
    (hST : ∀ n : ℕ, N ≤ n → n ∈ S → n ∈ T) :
    badCount T X ≤ badCount S X + N := by
  classical
  unfold badCount
  let badT := (Finset.Icc 1 X).filter fun n => n ∉ T
  let badS := (Finset.Icc 1 X).filter fun n => n ∉ S
  have hsub : badT ⊆ badS ∪ Finset.range N := by
    intro n hn
    simp only [badT, badS, Finset.mem_filter, Finset.mem_union,
      Finset.mem_range] at hn ⊢
    by_cases hnS : n ∈ S
    · right
      by_contra hnN
      exact hn.2 (hST n (Nat.le_of_not_gt hnN) hnS)
    · exact Or.inl ⟨hn.1, hnS⟩
  calc
    badT.card ≤ (badS ∪ Finset.range N).card := Finset.card_le_card hsub
    _ ≤ badS.card + (Finset.range N).card :=
      Finset.card_union_le badS (Finset.range N)
    _ = badS.card + N := by simp

/-- Every logarithmic power with exponent in `[0,1]` is eventually at most
the ambient variable.  This is the exact factor needed to absorb a finite
startup into `X (log X)^(-kappa)`. -/
theorem eventually_one_le_nat_mul_log_rpow_neg
    {kappa : ℝ} (_hkappa0 : 0 ≤ kappa) (hkappa1 : kappa ≤ 1) :
    ∀ᶠ X : ℕ in atTop,
      1 ≤ (X : ℝ) * (Real.log X) ^ (-kappa) := by
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with X hX
  have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hXreal : (8 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog : 1 ≤ Real.log X :=
    hlog8.trans (Real.log_le_log (by norm_num) hXreal)
  have hpow : (Real.log X) ^ kappa ≤ Real.log X := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hlog hkappa1)
  have hden : (Real.log X) ^ kappa ≤ (X : ℝ) :=
    hpow.trans (Real.log_le_self (by positivity))
  have hdenPos : 0 < (Real.log X) ^ kappa :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog) _
  have hlog0 : 0 ≤ Real.log X := zero_le_one.trans hlog
  rw [Real.rpow_neg hlog0, ← div_eq_mul_inv]
  exact (le_div_iff₀ hdenPos).2 (by simpa using hden)

/-- A quantitative logarithmic exceptional profile survives eventual set
enlargement after absorbing the finite startup into the coefficient. -/
theorem eventually_badCount_le_polylog_of_tail_subset
    {S T : Set ℕ} {C kappa : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hST : ∀ n : ℕ, N ≤ n → n ∈ S → n ∈ T)
    (hcount : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) ≤
        C * X * (Real.log X) ^ (-kappa)) :
    ∀ᶠ X : ℕ in atTop,
      (badCount T X : ℝ) ≤
        (C + N + 1) * X *
          (Real.log X) ^ (-(min kappa 1)) := by
  have hkappaMin0 : 0 ≤ min kappa 1 :=
    (lt_min hkappa zero_lt_one).le
  have hkappaMin1 : min kappa 1 ≤ 1 := min_le_right _ _
  have hfactor :=
    eventually_one_le_nat_mul_log_rpow_neg hkappaMin0 hkappaMin1
  filter_upwards [hcount, hfactor, eventually_ge_atTop (8 : ℕ)]
      with X hcount hfactor hX
  have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hXreal : (8 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog : 1 ≤ Real.log X :=
    hlog8.trans (Real.log_le_log (by norm_num) hXreal)
  have hpowMono :
      (Real.log X) ^ (-kappa) ≤
        (Real.log X) ^ (-(min kappa 1)) := by
    exact Real.rpow_le_rpow_of_exponent_le hlog (neg_le_neg (min_le_left _ _))
  have hbadNat := badCount_le_add_of_tail_subset S T N X hST
  have hbad : (badCount T X : ℝ) ≤ (badCount S X : ℝ) + N := by
    exact_mod_cast hbadNat
  have hprofileNonneg :
      0 ≤ (X : ℝ) * (Real.log X) ^ (-(min kappa 1)) := by positivity
  calc
    (badCount T X : ℝ) ≤ (badCount S X : ℝ) + N := hbad
    _ ≤ C * X * (Real.log X) ^ (-kappa) + N :=
      by simpa [add_comm] using add_le_add_right hcount (N : ℝ)
    _ ≤ C * X * (Real.log X) ^ (-(min kappa 1)) + N := by
      gcongr
    _ ≤ (C + N + 1) * X *
        (Real.log X) ^ (-(min kappa 1)) := by
      nlinarith [show (0 : ℝ) ≤ N by positivity]

/-- Any positive logarithmic-power exceptional profile implies natural
density one. -/
theorem naturalDensityOne_of_eventually_badCount_le_polylog
    {S : Set ℕ} {C kappa : ℝ}
    (_hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hcount : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) ≤
        C * X * (Real.log X) ^ (-kappa)) :
    NaturalDensityOne S := by
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ => (Real.log X) ^ (-kappa))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hkappa).comp hlog
  have hupper : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) / X ≤
        C * (Real.log X) ^ (-kappa) := by
    filter_upwards [hcount, eventually_ge_atTop (1 : ℕ)] with X hcount hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    calc
      (badCount S X : ℝ) / X ≤
          (C * X * (Real.log X) ^ (-kappa)) / X :=
        div_le_div_of_nonneg_right hcount hXpos.le
      _ = C * (Real.log X) ^ (-kappa) := by
        field_simp
  unfold NaturalDensityOne
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by
      simpa using (tendsto_const_nhds.mul hpow :
        Tendsto (fun X : ℕ => C * (Real.log X) ^ (-kappa))
          atTop (nhds (C * 0))))
  · filter_upwards with X
    positivity
  · exact hupper

end

end FirstPassageLinearTransport
