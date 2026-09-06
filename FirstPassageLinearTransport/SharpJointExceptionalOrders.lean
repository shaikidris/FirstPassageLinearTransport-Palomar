/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ReciprocalHeightObstruction

/-!
# Sharp joint exceptional-order bridge

This module extends the reciprocal height obstruction to source-dependent
relative ceilings and converts the last complete dyadic shell into a prefix
lower bound.  Profile-specific specializations only need to discharge the
target-unreachability and slow-ceiling hypotheses on that shell.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped BigOperators Real Topology

noncomputable section

/-- A target-and-height witness with a source-dependent relative ceiling. -/
def HasVariableTargetHeightWitness
    (f u : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (orbit k n : ℝ) ≤ f n ∧
      ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ u n * (n : ℝ)

/-- Variable-ceiling failures in one complete dyadic shell. -/
noncomputable def shellVariableTargetHeightFailure
    (M : ℕ) (f u : ℕ → ℝ) :
    Finset {n : ℕ // n ∈ dyadicShell M} := by
  classical
  exact Finset.univ.filter fun n =>
    ¬HasVariableTargetHeightWitness f u n.1

theorem shellTargetHeightFailure_subset_shellVariableTargetHeightFailure
    {M : ℕ} {f u : ℕ → ℝ} {U : ℝ}
    (hu : ∀ n : ℕ, n ∈ dyadicShell M → u n ≤ U) :
    shellTargetHeightFailure M f U ⊆
      shellVariableTargetHeightFailure M f u := by
  classical
  intro n hn
  simp only [shellTargetHeightFailure, shellVariableTargetHeightFailure,
    Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
  intro hvar
  apply hn
  obtain ⟨k, hkTarget, hkHeight⟩ := hvar
  refine ⟨k, hkTarget, ?_⟩
  intro j hj
  have hlocal := hkHeight j hj
  have hn0 : 0 ≤ (n.1 : ℝ) := by positivity
  exact hlocal.trans (mul_le_mul_of_nonneg_right (hu n.1 n.2) hn0)

/-- The exact reciprocal moving-shell obstruction with a variable displayed
ceiling, bounded above on the shell by `U`. -/
theorem normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
    {M h : ℕ} (hhM : h ≤ M) (hh : 0 < h)
    {U : ℝ} (hU : 1 ≤ U)
    (hlog : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f u : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hu : ∀ n : ℕ, n ∈ dyadicShell M → u n ≤ U) :
    (2 / (3 * U)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) ≤
      ((shellVariableTargetHeightFailure M f u).card : ℝ) /
        (2 : ℝ) ^ M := by
  have hconstant := normalized_card_shellTargetHeightFailure_ge_reciprocal
    hhM hh hU hlog htarget
  have hcardNat := Finset.card_le_card
    (shellTargetHeightFailure_subset_shellVariableTargetHeightFailure
      (f := f) hu)
  have hcard :
      ((shellTargetHeightFailure M f U).card : ℝ) ≤
        (shellVariableTargetHeightFailure M f u).card := by
    exact_mod_cast hcardNat
  exact hconstant.trans
    (div_le_div_of_nonneg_right hcard (by positivity))

/-- Prefix failures for a source-dependent target and relative ceiling. -/
noncomputable def variableTargetHeightFailureCount
    (f u : ℕ → ℝ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n =>
    ¬HasVariableTargetHeightWitness f u n).card

/-- A complete shell below `X` contributes all its variable target-height
failures to the prefix count. -/
theorem card_shellVariableTargetHeightFailure_le_failureCount
    {M X : ℕ} {f u : ℕ → ℝ}
    (hMX : 2 ^ (M + 1) ≤ X + 1) :
    (shellVariableTargetHeightFailure M f u).card ≤
      variableTargetHeightFailureCount f u X := by
  classical
  let emb : {n : ℕ // n ∈ dyadicShell M} ↪ ℕ :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsub :
      (shellVariableTargetHeightFailure M f u).map emb ⊆
        (Finset.Icc 1 X).filter fun n =>
          ¬HasVariableTargetHeightWitness f u n := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    have hmFailure := hm
    simp only [shellVariableTargetHeightFailure, Finset.mem_filter,
      Finset.mem_univ, true_and] at hmFailure
    have hnBounds := mem_dyadicShell.mp m.2
    have hnPos : 1 ≤ m.1 := by
      have hpow : 0 < 2 ^ M := by positivity
      omega
    have hnX : m.1 ≤ X := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hnPos, hnX⟩, hmFailure⟩
  calc
    (shellVariableTargetHeightFailure M f u).card =
        ((shellVariableTargetHeightFailure M f u).map emb).card := by
      rw [Finset.card_map]
    _ ≤ ((Finset.Icc 1 X).filter fun n =>
        ¬HasVariableTargetHeightWitness f u n).card :=
      Finset.card_le_card hsub
    _ = variableTargetHeightFailureCount f u X := rfl

/-- Rank of the last complete dyadic shell contained in a sufficiently large
positive prefix. -/
def lastCompleteDyadicShell (X : ℕ) : ℕ := Nat.log 2 X - 1

theorem lastCompleteDyadicShell_succ
    {X : ℕ} (hX : 4 ≤ X) :
    lastCompleteDyadicShell X + 1 = Nat.log 2 X := by
  have hlog : 1 ≤ Nat.log 2 X := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  unfold lastCompleteDyadicShell
  omega

theorem pow_lastCompleteDyadicShell_succ_le
    {X : ℕ} (hX : 4 ≤ X) :
    2 ^ (lastCompleteDyadicShell X + 1) ≤ X := by
  rw [lastCompleteDyadicShell_succ hX]
  exact Nat.pow_log_le_self 2 (by omega)

theorem X_lt_four_mul_pow_lastCompleteDyadicShell
    {X : ℕ} (hX : 4 ≤ X) :
    X < 4 * 2 ^ lastCompleteDyadicShell X := by
  have hlog : 1 ≤ Nat.log 2 X := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have hupper := Nat.lt_pow_succ_log_self (by omega : 1 < 2) X
  calc
    X < 2 ^ (Nat.log 2 X + 1) := by simpa using hupper
    _ = 4 * 2 ^ lastCompleteDyadicShell X := by
      rw [show Nat.log 2 X + 1 = lastCompleteDyadicShell X + 2 by
        unfold lastCompleteDyadicShell
        omega]
      rw [pow_add]
      norm_num
      ring

/-- A normalized lower bound on the last complete shell loses at most the
fixed factor four when converted to the whole prefix. -/
theorem variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
    {X : ℕ} (hX : 4 ≤ X) {f u : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hShell : b ≤
      ((shellVariableTargetHeightFailure
        (lastCompleteDyadicShell X) f u).card : ℝ) /
          (2 : ℝ) ^ lastCompleteDyadicShell X) :
    (b / 4) * (X : ℝ) ≤ variableTargetHeightFailureCount f u X := by
  let M := lastCompleteDyadicShell X
  have hpowPos : 0 < (2 : ℝ) ^ M := by positivity
  have hShellMul : b * (2 : ℝ) ^ M ≤
      (shellVariableTargetHeightFailure M f u).card := by
    exact (le_div_iff₀ hpowPos).mp (by simpa [M] using hShell)
  have hXpowNat : X < 4 * 2 ^ M := by
    simpa [M] using X_lt_four_mul_pow_lastCompleteDyadicShell hX
  have hXpow : (X : ℝ) ≤ 4 * (2 : ℝ) ^ M := by
    exact_mod_cast hXpowNat.le
  have hscaled : (b / 4) * (X : ℝ) ≤ b * (2 : ℝ) ^ M := by
    nlinarith
  have hcardCount := card_shellVariableTargetHeightFailure_le_failureCount
    (f := f) (u := u)
    (show 2 ^ (M + 1) ≤ X + 1 by
      have hpow := pow_lastCompleteDyadicShell_succ_le hX
      dsimp [M]
      omega)
  have hcardCountR :
      ((shellVariableTargetHeightFailure M f u).card : ℝ) ≤
        variableTargetHeightFailureCount f u X := by
    exact_mod_cast hcardCount
  exact hscaled.trans (hShellMul.trans hcardCountR)

/-- Quantitative global consumer of the exact reciprocal shell obstruction.
All profile-specific work is isolated in the four hypotheses imposed on the
last complete shell. -/
theorem variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
    {X h : ℕ} (hX : 4 ≤ X)
    {U : ℝ} (hU : 1 ≤ U)
    (hlog : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f u : ℕ → ℝ}
    (hh : 0 < h) (hhM : h ≤ lastCompleteDyadicShell X)
    (htarget : ∀ n : ℕ,
      n ∈ dyadicShell (lastCompleteDyadicShell X) →
        f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hu : ∀ n : ℕ,
      n ∈ dyadicShell (lastCompleteDyadicShell X) → u n ≤ U) :
    ((1 / 4) * (2 / (3 * U)) *
        (1 - reciprocalMaximumConstant / (h : ℝ))) * (X : ℝ) ≤
      variableTargetHeightFailureCount f u X := by
  let b := (2 / (3 * U)) *
    (1 - reciprocalMaximumConstant / (h : ℝ))
  have hShell : b ≤
      ((shellVariableTargetHeightFailure
        (lastCompleteDyadicShell X) f u).card : ℝ) /
          (2 : ℝ) ^ lastCompleteDyadicShell X := by
    exact normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
      hhM hh hU hlog htarget hu
  by_cases hb : 0 ≤ b
  · have h := variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
      hX hb hShell
    convert h using 1 <;> dsimp [b] <;> ring
  · have hleft :
        ((1 / 4) * (2 / (3 * U)) *
          (1 - reciprocalMaximumConstant / (h : ℝ))) * (X : ℝ) ≤ 0 := by
      have hb' : (2 / (3 * U)) *
          (1 - reciprocalMaximumConstant / (h : ℝ)) < 0 := by
        simpa [b] using hb
      have hX0 : 0 ≤ (X : ℝ) := by positivity
      nlinarith
    exact hleft.trans (by positivity)

end

end FirstPassageLinearTransport
