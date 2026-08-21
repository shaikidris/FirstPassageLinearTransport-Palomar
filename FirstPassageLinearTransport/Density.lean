/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import FirstPassageLinearTransport.Basic

/-!
# Quantitative density bridges

Reusable dyadic shell-to-prefix counting for the V2 `PowerDense` convention.
This is source-adapted from CET's generic density layer and imports no CET
module.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

theorem PowerDense.C_pos {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) : 0 < C := h.1

theorem PowerDense.D_pos {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) : 0 < D := h.2.1

theorem PowerDense.D_le_one {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) : D ≤ 1 := h.2.2.1

theorem PowerDense.bad_bound {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) (X : ℕ) (hX : 1 ≤ X) :
    (badCount S X : ℝ) ≤ C * (X : ℝ) ^ (1 - D) :=
  h.2.2.2 X hX

theorem PowerDense.mono_constant {S : Set ℕ} {C C' D : ℝ}
    (h : PowerDense S C D) (hCC' : C ≤ C') :
    PowerDense S C' D := by
  refine ⟨lt_of_lt_of_le h.C_pos hCC', h.D_pos, h.D_le_one, ?_⟩
  intro X hX
  exact (h.bad_bound X hX).trans
    (mul_le_mul_of_nonneg_right hCC'
      (Real.rpow_nonneg (by positivity) _))

theorem PowerDense.degrade_exponent {S : Set ℕ} {C D D' : ℝ}
    (h : PowerDense S C D) (hD' : 0 < D') (hD'D : D' ≤ D) :
    PowerDense S C D' := by
  refine ⟨h.C_pos, hD', hD'D.trans h.D_le_one, ?_⟩
  intro X hX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ (1 - D) ≤ (X : ℝ) ^ (1 - D') :=
    Real.rpow_le_rpow_of_exponent_le hXR (by linarith)
  exact (h.bad_bound X hX).trans
    (mul_le_mul_of_nonneg_left hpow h.C_pos.le)

theorem PowerDense.mono_set {S T : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) (hST : S ⊆ T) :
    PowerDense T C D := by
  classical
  refine ⟨h.C_pos, h.D_pos, h.D_le_one, ?_⟩
  intro X hX
  have hsub :
      ((Finset.Icc 1 X).filter fun n => n ∉ T) ⊆
        ((Finset.Icc 1 X).filter fun n => n ∉ S) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hnS => hn.2 (hST hnS)⟩
  have hcard : badCount T X ≤ badCount S X := by
    unfold badCount
    exact Finset.card_le_card hsub
  have hcardR : (badCount T X : ℝ) ≤ (badCount S X : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (h.bad_bound X hX)

/-- Every positive power-saving exceptional-count estimate implies natural
density one. -/
theorem PowerDense.naturalDensityOne {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) : NaturalDensityOne S := by
  have hpow : Filter.Tendsto (fun X : ℕ => (X : ℝ) ^ (-D))
      Filter.atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop h.D_pos).comp
      tendsto_natCast_atTop_atTop
  have hupper : ∀ᶠ X : ℕ in Filter.atTop,
      (badCount S X : ℝ) / X ≤ C * (X : ℝ) ^ (-D) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hbad := h.bad_bound X hX
    calc
      (badCount S X : ℝ) / X ≤
          (C * (X : ℝ) ^ (1 - D)) / X :=
        div_le_div_of_nonneg_right hbad hXR.le
      _ = C * (X : ℝ) ^ (-D) := by
        rw [show (1 : ℝ) - D = 1 + (-D) by ring,
          Real.rpow_add hXR, Real.rpow_one]
        field_simp
  have hnonneg : ∀ X : ℕ, 0 ≤ (badCount S X : ℝ) / X := by
    intro X
    positivity
  unfold NaturalDensityOne
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by
      simpa using (tendsto_const_nhds.mul hpow :
        Filter.Tendsto (fun X : ℕ => C * (X : ℝ) ^ (-D))
          Filter.atTop (nhds (C * 0))))
  · filter_upwards with X
    exact hnonneg X
  · exact hupper

/-- Nonmembers of `S` in the `M`-th dyadic shell. -/
noncomputable def shellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n => n ∉ S)

/-- Nonmembers of `S` in the positive prefix `[1,X]`. -/
noncomputable def prefixBad (S : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (fun n => n ∉ S)

@[simp] theorem mem_prefixBad {S : Set ℕ} {X n : ℕ} :
    n ∈ prefixBad S X ↔ 1 ≤ n ∧ n ≤ X ∧ n ∉ S := by
  classical
  simp [prefixBad, and_assoc]

/-- Every positive bad integer up to `X` lies in a shell of index at most
`Nat.log 2 X`. -/
theorem badCount_subset_biUnion (S : Set ℕ) (X : ℕ) :
    prefixBad S X ⊆
      (Finset.range (Nat.log 2 X + 1)).biUnion (shellBad S) := by
  classical
  intro n hn
  rw [mem_prefixBad] at hn
  obtain ⟨hn1, hnX, hnS⟩ := hn
  have hn0 : n ≠ 0 := by omega
  refine Finset.mem_biUnion.2 ⟨Nat.log 2 n, ?_, ?_⟩
  · exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Nat.log_mono_right hnX))
  · rw [shellBad, Finset.mem_filter, mem_dyadicShell]
    exact ⟨⟨Nat.pow_log_le_self 2 hn0,
      Nat.lt_pow_succ_log_self (by norm_num) n⟩, hnS⟩

theorem badCount_le_shell_sum (S : Set ℕ) (X : ℕ) :
    badCount S X ≤
      ∑ M ∈ Finset.range (Nat.log 2 X + 1), (shellBad S M).card := by
  classical
  unfold badCount
  calc
    ((Finset.Icc 1 X).filter fun n => n ∉ S).card ≤
        ((Finset.range (Nat.log 2 X + 1)).biUnion (shellBad S)).card :=
      Finset.card_le_card (by
        simpa [prefixBad] using badCount_subset_biUnion S X)
    _ ≤ ∑ M ∈ Finset.range (Nat.log 2 X + 1), (shellBad S M).card :=
      Finset.card_biUnion_le

theorem shellBad_card_le_badCount (S : Set ℕ) (M : ℕ) :
    (shellBad S M).card ≤ badCount S (2 ^ (M + 1)) := by
  classical
  unfold badCount
  apply Finset.card_le_card
  intro n hn
  rw [shellBad, Finset.mem_filter, mem_dyadicShell] at hn
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hnpos : 1 ≤ n := by
    have hp : 0 < 2 ^ M := by positivity
    omega
  exact ⟨⟨hnpos, hn.1.2.le⟩, hn.2⟩

/-- Shell-to-global power-density transport. -/
theorem powerDense_of_shell_bound
    {S : Set ℕ} {K c : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hclt : c < Real.log 2)
    (hshell : ∀ M : ℕ,
      ((shellBad S M).card : ℝ) ≤
        K * Real.exp (-c * M) * (2 : ℝ) ^ M) :
    PowerDense S
      (2 * K / (2 * Real.exp (-c) - 1))
      (c / Real.log 2) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set r : ℝ := 2 * Real.exp (-c) with hr_def
  have hr1 : 1 < r := by
    have h2 : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
    have h : Real.exp (-Real.log 2) < Real.exp (-c) :=
      Real.exp_lt_exp.2 (by linarith)
    rw [h2] at h
    rw [hr_def]
    linarith
  have hrm1 : 0 < r - 1 := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_one hlog2]
    exact le_of_lt hclt
  intro X hX
  have hXpos : 0 < X := by omega
  set L := Nat.log 2 X with hL_def
  have hsum := badCount_le_shell_sum S X
  have hsumR :
      (badCount S X : ℝ) ≤
        ∑ M ∈ Finset.range (L + 1), ((shellBad S M).card : ℝ) := by
    exact_mod_cast hsum
  have hgeom :
      ∑ M ∈ Finset.range (L + 1), ((shellBad S M).card : ℝ) ≤
        K * ∑ M ∈ Finset.range (L + 1), r ^ M := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro M _
    have hrw : K * r ^ M =
        K * Real.exp (-c * M) * (2 : ℝ) ^ M := by
      rw [hr_def, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [hrw]
    exact hshell M
  have hgs :
      ∑ M ∈ Finset.range (L + 1), r ^ M =
        (r ^ (L + 1) - 1) / (r - 1) :=
    geom_sum_eq (by linarith) _
  have hgs' :
      ∑ M ∈ Finset.range (L + 1), r ^ M ≤
        r ^ (L + 1) / (r - 1) := by
    rw [hgs]
    gcongr
    linarith
  have hXL : (2 : ℝ) ^ L ≤ (X : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hXpos.ne'
  have hLX : (X : ℝ) < 2 ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) X
  have hXRpos : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hpow2 : (2 : ℝ) ^ (L + 1) ≤ 2 * X := by
    rw [pow_succ]
    nlinarith [hXL]
  have hexp :
      Real.exp (-c) ^ (L + 1) ≤
        (X : ℝ) ^ (-(c / Real.log 2)) := by
    have hlnX : Real.log X ≤ ((L : ℝ) + 1) * Real.log 2 := by
      have h := Real.log_le_log hXRpos (le_of_lt hLX)
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hXRpos]
    apply Real.exp_le_exp.2
    have hmul :
        c / Real.log 2 * Real.log X ≤ ((L : ℝ) + 1) * c := by
      have h := mul_le_mul_of_nonneg_left hlnX
        (le_of_lt (div_pos hc hlog2))
      calc
        c / Real.log 2 * Real.log X ≤
            c / Real.log 2 * (((L : ℝ) + 1) * Real.log 2) := h
        _ = ((L : ℝ) + 1) * c := by field_simp
    push_cast
    nlinarith [hmul]
  have hrL :
      r ^ (L + 1) ≤
        2 * X * (X : ℝ) ^ (-(c / Real.log 2)) := by
    rw [hr_def, mul_pow]
    calc
      (2 : ℝ) ^ (L + 1) * Real.exp (-c) ^ (L + 1) ≤
          (2 * X) * Real.exp (-c) ^ (L + 1) :=
        mul_le_mul_of_nonneg_right hpow2 (by positivity)
      _ ≤ (2 * X) * (X : ℝ) ^ (-(c / Real.log 2)) := by
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hXrpow :
      (X : ℝ) * (X : ℝ) ^ (-(c / Real.log 2)) =
        (X : ℝ) ^ (1 - c / Real.log 2) := by
    rw [show (1 : ℝ) - c / Real.log 2 =
        1 + -(c / Real.log 2) by ring,
      Real.rpow_add hXRpos, Real.rpow_one]
  calc
    (badCount S X : ℝ) ≤ K * ∑ M ∈ Finset.range (L + 1), r ^ M :=
      hsumR.trans hgeom
    _ ≤ K * (r ^ (L + 1) / (r - 1)) :=
      mul_le_mul_of_nonneg_left hgs' hK.le
    _ ≤ K * ((2 * X * (X : ℝ) ^ (-(c / Real.log 2))) /
          (r - 1)) := by gcongr
    _ = 2 * K / (r - 1) *
          ((X : ℝ) * (X : ℝ) ^ (-(c / Real.log 2))) := by
      field_simp
    _ = 2 * K / (r - 1) * (X : ℝ) ^ (1 - c / Real.log 2) := by
      rw [hXrpow]

end

end FirstPassageLinearTransport
