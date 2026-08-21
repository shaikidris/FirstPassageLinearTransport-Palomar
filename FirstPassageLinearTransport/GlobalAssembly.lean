/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.HeadlineParameters

/-! # Global varying-shell assembly -/

namespace FirstPassageLinearTransport

open scoped Real Topology

noncomputable section

/-- The bootstrap-good set selected at shell depth `M`. -/
def shellBootstrap {r eta : ℝ} (p : StageSetup r eta)
    (omega : ℝ) (M : ℕ) : Set ℕ :=
  bootstrapSet p (stageCount omega M)

/-- Global set obtained by assembling the shell-dependent bootstrap sets. -/
def assembledBootstrap {r eta : ℝ} (p : StageSetup r eta)
    (omega : ℝ) : Set ℕ :=
  assembleDyadic (shellBootstrap p omega)

theorem assembledBootstrap_naturalDensityOne_of_vanish
    {r eta : ℝ} (p : StageSetup r eta) (omega : ℝ)
    (hvanish : Filter.Tendsto
      (fun M => shellExceptionalRatio (shellBootstrap p omega M) M)
      Filter.atTop (nhds 0)) :
    NaturalDensityOne (assembledBootstrap p omega) := by
  exact naturalDensityOne_assembleDyadic (shellBootstrap p omega) hvanish

theorem mem_shellBootstrap_of_mem_assembled
    {r eta : ℝ} (p : StageSetup r eta) {omega : ℝ} {n : ℕ}
    (hn : n ∈ assembledBootstrap p omega) :
    n ∈ bootstrapSet p (stageCount omega (Nat.log 2 n)) := by
  exact hn

/-- The varying-shell endpoint is one literal shortcut iterate. -/
theorem assembledBootstrap_actual_endpoint
    {r eta : ℝ} (p : StageSetup r eta) {omega : ℝ} {n : ℕ}
    : stageOrbit p (stageCount omega (Nat.log 2 n)) n =
      orbit (stageClock p (stageCount omega (Nat.log 2 n)) n) n :=
  stageOrbit_eq_orbit_stageClock _ _ _

/-- Final logical assembly once the two scalar schedule inequalities have
been discharged.  No Collatz statement is hidden in these scalar premises. -/
theorem assembledBootstrap_timed_descent_of_scalar_bounds
    {r eta delta omega clock : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hlanding :
      (stageOrbit p (stageCount omega (Nat.log 2 n)) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta)))
    (htime :
      (stageClock p (stageCount omega (Nat.log 2 n)) n : ℝ) <
        clock * Real.log n) :
    HasTimedStretchedLogDescent delta clock n := by
  refine ⟨stageClock p (stageCount omega (Nat.log 2 n)) n, htime, ?_⟩
  rw [← assembledBootstrap_actual_endpoint p]
  exact hlanding

end

end FirstPassageLinearTransport
