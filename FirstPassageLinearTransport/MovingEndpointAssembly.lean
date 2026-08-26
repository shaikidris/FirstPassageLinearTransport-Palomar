/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.MovingEndpointScalars
import FirstPassageLinearTransport.PolylogExceptionalCount

/-!
# Varying-shell assembly for the moving endpoint

This module is the final deterministic consumer for a future moving low-barrier
profile.  It turns the literal shell error and shell witness statements into
one natural-density-one set.  It does not assume or manufacture the missing
moving barrier estimate.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Assemble a moving shell profile after its literal density and witness
estimates have been proved. -/
theorem movingEndpointNaturalDensityAssembly
    (S : ℕ → Set ℕ) {A : ℕ → ℝ} {c beta C eps : ℝ}
    (heps : 0 < eps)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (S M) M ≤
        C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))))
    (hWitness : ∀ᶠ M : ℕ in atTop,
      ∀ n : ℕ, n ∈ dyadicShell M → n ∈ S M →
        ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) :
    NaturalDensityOne (assembleDyadic S) ∧
      ∀ᶠ n : ℕ in atTop,
        n ∈ assembleDyadic S →
          ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) <
              C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  refine ⟨naturalDensityOne_of_movingShellError S heps hbuffer hShell, ?_⟩
  have hAtLog := tendsto_natLogTwo_atTop.eventually hWitness
  filter_upwards [hAtLog, eventually_ge_atTop (1 : ℕ)] with n hAtLog hn
  intro hnSet
  have hnpos : 0 < n := by omega
  let M := Nat.log 2 n
  have hnShell : n ∈ dyadicShell M := mem_dyadicShell_log hnpos
  have hnGood : n ∈ S M := by
    simpa [assembleDyadic, M] using hnSet
  simpa [M] using hAtLog n hnShell hnGood

end

end FirstPassageLinearTransport
