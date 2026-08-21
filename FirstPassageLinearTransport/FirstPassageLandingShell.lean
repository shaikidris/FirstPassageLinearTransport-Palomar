/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.FirstPassage

/-!
# Shell rank of a first-passage landing

This neutral module records the shell-rank consequence of the first-passage
band.  Both the canonical shrinking-barrier execution and the retained
two-regime route use it, so it must not be owned by either execution package.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- The shell rank of a positive first-passage landing differs from the
threshold rank by at most one. -/
theorem firstPassage_landing_shell_rank
    {n elapsed q m : ℕ} (helapsed : 0 < elapsed)
    (hfp : IsFirstPassage (2 ^ q) n elapsed)
    (hshell : orbit elapsed n ∈ dyadicShell m) :
    m ≤ q ∧ q ≤ m + 1 := by
  have hpowLe : 2 ^ m ≤ 2 ^ q :=
    (mem_dyadicShell.mp hshell).1.trans hfp.1
  have hmq : m ≤ q := by
    by_contra hnot
    have hstrict : 2 ^ q < 2 ^ m :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hband := firstPassage_band helapsed hfp
  have hshellUpper := (mem_dyadicShell.mp hshell).2
  have hpowLt : 2 ^ q < 2 ^ (m + 2) := by
    calc
      2 ^ q < 2 * orbit elapsed n := hband.1
      _ < 2 * 2 ^ (m + 1) := Nat.mul_lt_mul_of_pos_left hshellUpper (by omega)
      _ = 2 ^ (m + 2) := by rw [pow_succ]; ring
  have hqm : q < m + 2 := by
    by_contra hnot
    have hpowBack : 2 ^ (m + 2) ≤ 2 ^ q :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  exact ⟨hmq, by omega⟩

end

end FirstPassageLinearTransport
