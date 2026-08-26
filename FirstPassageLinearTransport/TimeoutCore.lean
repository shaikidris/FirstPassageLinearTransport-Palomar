/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.MovingLowParameters
import FirstPassageLinearTransport.SharpEntropyBarrier

/-!
# Timeout low-stage producer

This module begins the timeout low-rank route to the moving-endpoint theorem.
It replaces low-stage all-prefix certification by the literal event that the
orbit has not crossed its prescribed threshold by the shell timeout.

Only neutral parity and entropy infrastructure is imported here.  In
particular, this module does not depend on `MovingLowDensity`,
`MovingRecertificationRun`, or the existing moving first-bad assembly.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Topology

/-- The low-stage target rank used by the timeout construction. -/
noncomputable def timeoutTargetRank (K₀ : ℝ) (L m : ℕ) : ℕ :=
  ⌊movingLowRatio K₀ L * (m : ℝ)⌋₊

/-- A source times out at rank `m` when it has not crossed the target rank by
the deterministic deadline `m`. -/
def LowStageTimeout (K₀ : ℝ) (L m x : ℕ) : Prop :=
  ∀ j : Fin (m + 1), 2 ^ timeoutTargetRank K₀ L m < orbit j x

/-- A moving ratio above one half makes every rank at least five produce a
positive timeout target. -/
theorem timeoutTargetRank_pos_of_half_lt
    {K₀ : ℝ} {L m : ℕ}
    (hr : (1 / 2 : ℝ) < movingLowRatio K₀ L) (hm : 5 ≤ m) :
    0 < timeoutTargetRank K₀ L m := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hlarge : 2 < movingLowRatio K₀ L * (m : ℝ) := by nlinarith
  have hfloor :
      movingLowRatio K₀ L * (m : ℝ) - 1 <
        (timeoutTargetRank K₀ L m : ℝ) := by
    simpa [timeoutTargetRank] using
      (Nat.sub_one_lt_floor (movingLowRatio K₀ L * (m : ℝ)))
  have : (1 : ℝ) < timeoutTargetRank K₀ L m := by linarith
  have hnat : 1 < timeoutTargetRank K₀ L m := by exact_mod_cast this
  omega

/-- A moving ratio in `[0,1)` makes the timeout target strictly smaller than
every positive parent rank. -/
theorem timeoutTargetRank_lt_parent
    {K₀ : ℝ} {L m : ℕ}
    (hr0 : 0 ≤ movingLowRatio K₀ L)
    (hr1 : movingLowRatio K₀ L < 1) (hm : 0 < m) :
    timeoutTargetRank K₀ L m < m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfloor : (timeoutTargetRank K₀ L m : ℝ) ≤
      movingLowRatio K₀ L * (m : ℝ) := by
    simpa [timeoutTargetRank] using
      (Nat.floor_le (mul_nonneg hr0 (Nat.cast_nonneg m)))
  have hlt : (timeoutTargetRank K₀ L m : ℝ) < m := by nlinarith
  exact_mod_cast hlt

/-- One quantitative startup simultaneously supplies positivity and strict
rank decrease for every timeout block with parent rank at least `L`. -/
theorem eventually_timeoutTargetRank_admissible
    {K₀ : ℝ} (hK₀ : 0 < K₀) :
    ∀ᶠ L : ℕ in atTop, ∀ m : ℕ, L ≤ m →
      0 < timeoutTargetRank K₀ L m ∧
        timeoutTargetRank K₀ L m < m := by
  have hhalf : ∀ᶠ L : ℕ in atTop,
      (1 / 2 : ℝ) < movingLowRatio K₀ L :=
    (tendsto_movingLowRatio K₀).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hadm := eventually_movingLow_admissible hK₀
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hhalf, hadm, eventually_ge_atTop (5 : ℕ)]
    with L hhalf hadm hL
  intro m hLm
  exact ⟨timeoutTargetRank_pos_of_half_lt hhalf (hL.trans hLm),
    timeoutTargetRank_lt_parent hadm.2.2.1.le hadm.2.2.2.1
      (by omega)⟩

/-- The affine correction is strictly smaller than one full geometric copy
of the multiplicative term. -/
theorem affineCorrection_lt_two_pow_mul_three_pow (n k : ℕ) :
    affineCorrection n k < 2 ^ k * 3 ^ oddCount n k := by
  unfold affineCorrection
  have hsum :
      ∑ i ∈ Finset.range k,
          (parityBit n i : ℕ) * 2 ^ i *
            3 ^ (oddCount n k - oddCount n (i + 1))
        ≤ ∑ i ∈ Finset.range k, 2 ^ i * 3 ^ oddCount n k := by
    apply Finset.sum_le_sum
    intro i hi
    have hbit : (parityBit n i : ℕ) ≤ 1 := by
      have := parityBit_lt_two n i
      omega
    have hexp :
        3 ^ (oddCount n k - oddCount n (i + 1)) ≤
          3 ^ oddCount n k := by
      exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    calc
      (parityBit n i : ℕ) * 2 ^ i *
            3 ^ (oddCount n k - oddCount n (i + 1))
          ≤ 1 * 2 ^ i *
            3 ^ (oddCount n k - oddCount n (i + 1)) := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbit)
      _ ≤ 2 ^ i * 3 ^ oddCount n k := by
        simpa using Nat.mul_le_mul_left (2 ^ i) hexp
  calc
    ∑ i ∈ Finset.range k,
        (parityBit n i : ℕ) * 2 ^ i *
          3 ^ (oddCount n k - oddCount n (i + 1))
        ≤ ∑ i ∈ Finset.range k, 2 ^ i * 3 ^ oddCount n k := hsum
    _ = (∑ i ∈ Finset.range k, 2 ^ i) * 3 ^ oddCount n k := by
      rw [Finset.sum_mul]
    _ = (2 ^ k - 1) * 3 ^ oddCount n k := by
      rw [Nat.geomSum_eq (by omega : 2 ≤ 2)]
      norm_num
    _ < 2 ^ k * 3 ^ oddCount n k := by
      have hpow : 0 < 3 ^ oddCount n k := pow_pos (by omega) _
      have htwo : 0 < 2 ^ k := pow_pos (by omega) _
      exact Nat.mul_lt_mul_of_pos_right (by omega) hpow

/-- Every shell source lies below the pure multiplicative envelope with one
extra factor of `3` at its shell timeout. -/
theorem orbit_timeout_lt_three_pow_succ {m x : ℕ}
    (hx : x ∈ dyadicShell m) :
    orbit m x < 3 ^ (oddCount x m + 1) := by
  have haffine := exact_affine_iterate_scaled x m
  have hcorr := affineCorrection_lt_two_pow_mul_three_pow x m
  have hxupper : x < 2 ^ (m + 1) := (mem_dyadicShell.mp hx).2
  have htwo : 0 < 2 ^ m := pow_pos (by omega) _
  have hthree : 0 < 3 ^ oddCount x m := pow_pos (by omega) _
  have hscaled :
      2 ^ m * orbit m x < 2 ^ m * 3 ^ (oddCount x m + 1) := by
    rw [haffine, pow_succ]
    have hxscaled :
        3 ^ oddCount x m * x <
          3 ^ oddCount x m * (2 * 2 ^ m) := by
      rw [pow_succ] at hxupper
      nlinarith
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left hscaled

/-- Timeout forces a terminal upper-tail inequality for the parity word. -/
theorem three_pow_timeoutTargetRank_lt_three_pow_oddCount_succ
    {K₀ : ℝ} {L m x : ℕ}
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x) :
    2 ^ timeoutTargetRank K₀ L m < 3 ^ (oddCount x m + 1) := by
  exact lt_trans (htimeout ⟨m, by omega⟩)
    (orbit_timeout_lt_three_pow_succ hx)

/-- Shortcut iteration simply peels powers of two. -/
theorem shortcut_two_pow_succ (k : ℕ) :
    shortcut (2 ^ (k + 1)) = 2 ^ k := by
  rw [shortcut_of_even]
  · rw [pow_succ]
    omega
  · rw [pow_succ]
    omega

/-- Exact halving orbit of a power of two up to its exponent. -/
theorem timeout_orbit_two_pow {m j : ℕ} (hj : j ≤ m) :
    orbit j (2 ^ m) = 2 ^ (m - j) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
      rw [orbit_succ, ih (m := m) (by omega)]
      have hpos : 0 < m - j := by omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero
        (by omega : m - j ≠ 0)
      rw [hd, shortcut_two_pow_succ]
      congr
      omega

/-- The upper endpoint `2^(m+1)` of a landing band cannot time out once the
next target rank is positive: repeated halving reaches that target before
the deadline `m`. -/
theorem not_lowStageTimeout_two_pow_succ
    {K₀ : ℝ} {L m : ℕ}
    (hqpos : 0 < timeoutTargetRank K₀ L m)
    (hqlt : timeoutTargetRank K₀ L m < m + 1) :
    ¬LowStageTimeout K₀ L m (2 ^ (m + 1)) := by
  intro htimeout
  let j := m + 1 - timeoutTargetRank K₀ L m
  have hjm : j ≤ m := by
    dsimp [j]
    omega
  have hjexp : j ≤ m + 1 := hjm.trans (by omega)
  have horbit := timeout_orbit_two_pow hjexp
  have hexponent :
      m + 1 - j = timeoutTargetRank K₀ L m := by
    dsimp [j]
    omega
  have hstrict := htimeout ⟨j, by omega⟩
  rw [horbit, hexponent] at hstrict
  exact (lt_irrefl _ hstrict)

end FirstPassageLinearTransport
