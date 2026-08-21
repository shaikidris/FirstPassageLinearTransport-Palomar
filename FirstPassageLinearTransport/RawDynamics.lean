/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Basic

/-!
# Raw and shortcut Collatz clocks

Exact comparison between the raw Collatz map and the shortcut map.  The raw
time of a shortcut segment is its shortcut length plus the number of odd
shortcut states in that segment.
-/

namespace FirstPassageLinearTransport

/-- The raw Collatz map, totalized at zero by the same formula. -/
def rawCollatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The `j`-fold raw Collatz iterate. -/
def rawOrbit (j n : ℕ) : ℕ := (rawCollatz^[j]) n

@[simp] theorem rawOrbit_zero (n : ℕ) : rawOrbit 0 n = n := by
  simp [rawOrbit]

theorem rawOrbit_succ (j n : ℕ) :
    rawOrbit (j + 1) n = rawCollatz (rawOrbit j n) := by
  simp [rawOrbit, Function.iterate_succ_apply']

theorem rawOrbit_add (j k n : ℕ) :
    rawOrbit (j + k) n = rawOrbit j (rawOrbit k n) := by
  simp [rawOrbit, Function.iterate_add_apply]

theorem rawCollatz_of_even {n : ℕ} (hn : n % 2 = 0) :
    rawCollatz n = n / 2 := by
  simp [rawCollatz, hn]

theorem rawCollatz_of_odd {n : ℕ} (hn : n % 2 = 1) :
    rawCollatz n = 3 * n + 1 := by
  simp [rawCollatz, hn]

/-- One even shortcut step is one raw step. -/
theorem rawCollatz_eq_shortcut_of_even {n : ℕ} (hn : n % 2 = 0) :
    rawCollatz n = shortcut n := by
  rw [rawCollatz_of_even hn, shortcut_of_even hn]

/-- One odd shortcut step is exactly two raw steps. -/
theorem rawOrbit_two_eq_shortcut_of_odd {n : ℕ} (hn : n % 2 = 1) :
    rawOrbit 2 n = shortcut n := by
  have heven : (3 * n + 1) % 2 = 0 := by omega
  rw [show 2 = 1 + 1 by omega, rawOrbit_succ, rawOrbit_succ,
    rawOrbit_zero, rawCollatz_of_odd hn, rawCollatz_of_even heven,
    shortcut_of_odd hn]

/-- Exact raw time represented by a shortcut prefix. -/
def rawTime (n k : ℕ) : ℕ := k + oddCount n k

/-- The raw iterate at `k + oddCount n k` is the `k`-th shortcut iterate. -/
theorem rawOrbit_rawTime_eq_orbit (n k : ℕ) :
    rawOrbit (rawTime n k) n = orbit k n := by
  induction k with
  | zero => simp [rawTime]
  | succ k ih =>
      rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
      · have hbit : (parityBit n k : ℕ) = 0 := by
          simpa [parityBit] using heven
        have ih' : rawOrbit (k + oddCount n k) n = orbit k n := by
          simpa [rawTime] using ih
        rw [rawTime, oddCount_succ, hbit, add_zero]
        rw [show k + 1 + oddCount n k = 1 + (k + oddCount n k) by omega,
          rawOrbit_add, ih', rawOrbit_succ, rawOrbit_zero, orbit_succ,
          rawCollatz_eq_shortcut_of_even heven]
      · have hbit : (parityBit n k : ℕ) = 1 := by
          simpa [parityBit] using hodd
        have ih' : rawOrbit (k + oddCount n k) n = orbit k n := by
          simpa [rawTime] using ih
        rw [rawTime, oddCount_succ, hbit]
        rw [show k + 1 + (oddCount n k + 1) =
            2 + (k + oddCount n k) by omega,
          rawOrbit_add, ih', orbit_succ,
          rawOrbit_two_eq_shortcut_of_odd hodd]

/-- Parity bits shift with the source after a shortcut prefix. -/
theorem parityBit_add (n k j : ℕ) :
    parityBit n (k + j) = parityBit (orbit k n) j := by
  apply Fin.ext
  simp [parityBit, Nat.add_comm k j, orbit_add]

/-- Odd counts split exactly under concatenation of shortcut segments. -/
theorem oddCount_add (n k j : ℕ) :
    oddCount n (k + j) = oddCount n k + oddCount (orbit k n) j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show k + (j + 1) = (k + j) + 1 by omega,
        oddCount_succ, ih, oddCount_succ, parityBit_add]
      omega

end FirstPassageLinearTransport
