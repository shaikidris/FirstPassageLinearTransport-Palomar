/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat

/-!
# First-passage V2: independent basic definitions

This module restates the shortcut Collatz dynamics and the quantitative
density language used by the standalone V2 paper.  It imports only Mathlib.
-/

namespace FirstPassageLinearTransport

/-- The shortcut Collatz map.  The value at zero makes the map total. -/
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The `k`-fold shortcut iterate. -/
def orbit (k n : ℕ) : ℕ := (shortcut^[k]) n

/-- The parity bit at time `i`, represented as a member of `Fin 2`. -/
def parityBit (n i : ℕ) : Fin 2 :=
  ⟨orbit i n % 2, Nat.mod_lt _ (by omega)⟩

/-- Number of odd states among times `0, ..., k-1`. -/
def oddCount (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (parityBit n i : ℕ)

/-- The complete dyadic shell `[2^M, 2^(M+1))`. -/
def dyadicShell (M : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ M) (2 ^ (M + 1))

/-- Number of missing positive integers up to `X`. -/
noncomputable def badCount (S : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n => n ∉ S).card

/-- The quantitative density convention of the V2 paper. -/
def PowerDense (S : Set ℕ) (C D : ℝ) : Prop :=
  0 < C ∧ 0 < D ∧ D ≤ 1 ∧
    ∀ X : ℕ, 1 ≤ X → (badCount S X : ℝ) ≤ C * (X : ℝ) ^ (1 - D)

/-- Natural density one, expressed through the missing-count ratio. -/
def NaturalDensityOne (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun X : ℕ => (badCount S X : ℝ) / (X : ℝ))
    Filter.atTop (nhds 0)

/-- An orbit of `n` reaches the real threshold `Y`. -/
def ReachesBelow (n : ℕ) (Y : ℝ) : Prop :=
  ∃ k : ℕ, (orbit k n : ℝ) ≤ Y

/-- The stretched-logarithmic conclusion at exponent `delta`. -/
def HasStretchedLogDescent (δ : ℝ) (n : ℕ) : Prop :=
  ReachesBelow n (Real.exp ((Real.log n) ^ (1 - δ)))

/-- Descent below a fixed power of the starting value. -/
def HasFixedPowerDescent (alpha : ℝ) (n : ℕ) : Prop :=
  ReachesBelow n ((n : ℝ) ^ alpha)

/-- The least value attained by the full shortcut orbit.  This is the literal
formal counterpart of the manuscript's `T_min`. -/
noncomputable def orbitMinimum (n : ℕ) : ℕ :=
  sInf (Set.range fun k : ℕ => orbit k n)

theorem orbitMinimum_eq_orbit (n : ℕ) :
    ∃ k : ℕ, orbitMinimum n = orbit k n := by
  obtain ⟨k, hk⟩ :=
    Nat.sInf_mem (Set.range_nonempty fun k : ℕ => orbit k n)
  exact ⟨k, by simpa [orbitMinimum] using hk.symm⟩

theorem orbitMinimum_le_iff_reachesBelow {n : ℕ} {Y : ℝ} :
    (orbitMinimum n : ℝ) ≤ Y ↔ ReachesBelow n Y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := orbitMinimum_eq_orbit n
    exact ⟨k, by simpa [hk] using h⟩
  · rintro ⟨k, hk⟩
    calc
      (orbitMinimum n : ℝ) ≤ orbit k n := by
        exact_mod_cast Nat.sInf_le (Set.mem_range_self k)
      _ ≤ Y := hk

theorem orbitMinimum_le_power_iff_hasFixedPowerDescent {alpha : ℝ} {n : ℕ} :
    (orbitMinimum n : ℝ) ≤ (n : ℝ) ^ alpha ↔
      HasFixedPowerDescent alpha n := by
  exact orbitMinimum_le_iff_reachesBelow

/-- The same conclusion together with a shortcut-time clock. -/
def HasTimedStretchedLogDescent (δ clock : ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (k : ℝ) < clock * Real.log n ∧
      (orbit k n : ℝ) ≤ Real.exp ((Real.log n) ^ (1 - δ))

@[simp] theorem shortcut_zero : shortcut 0 = 0 := by
  simp [shortcut]

theorem shortcut_of_even {n : ℕ} (hn : n % 2 = 0) :
    shortcut n = n / 2 := by
  simp [shortcut, hn]

theorem shortcut_of_odd {n : ℕ} (hn : n % 2 = 1) :
    shortcut n = (3 * n + 1) / 2 := by
  simp [shortcut, hn]

theorem shortcut_pos {n : ℕ} (hn : 0 < n) : 0 < shortcut n := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · rw [shortcut_of_even heven]
    apply Nat.div_pos
    · omega
    · omega
  · rw [shortcut_of_odd hodd]
    apply Nat.div_pos
    · omega
    · omega

@[simp] theorem orbit_zero (n : ℕ) : orbit 0 n = n := by
  simp [orbit]

theorem orbit_succ (k n : ℕ) : orbit (k + 1) n = shortcut (orbit k n) := by
  simp [orbit, Function.iterate_succ_apply']

theorem orbit_add (j k n : ℕ) : orbit (j + k) n = orbit j (orbit k n) := by
  simp [orbit, Function.iterate_add_apply]

theorem orbit_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < orbit k n := by
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [orbit_succ]
      exact shortcut_pos ih

@[simp] theorem parityBit_zero (n : ℕ) : (parityBit n 0 : ℕ) = n % 2 := by
  simp [parityBit]

theorem parityBit_lt_two (n i : ℕ) : (parityBit n i : ℕ) < 2 :=
  (parityBit n i).isLt

@[simp] theorem oddCount_zero (n : ℕ) : oddCount n 0 = 0 := by
  simp [oddCount]

theorem oddCount_succ (n k : ℕ) :
    oddCount n (k + 1) = oddCount n k + (parityBit n k : ℕ) := by
  simp [oddCount, Finset.sum_range_succ]


@[simp] theorem mem_dyadicShell {M n : ℕ} :
    n ∈ dyadicShell M ↔ 2 ^ M ≤ n ∧ n < 2 ^ (M + 1) := by
  simp [dyadicShell]

theorem card_dyadicShell (M : ℕ) : (dyadicShell M).card = 2 ^ M := by
  simp [dyadicShell, pow_succ]
  omega


end FirstPassageLinearTransport
