import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat

/-!
# Polylogarithmic Collatz descent in natural density

This is the independent statement surface for the fixed-exponent theorem in
*Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density*.

For the shortcut Collatz map, every fixed exponent `A` above
`A_FP = 1 / (2 * (1 - H₂(log₃ 2)))`, every clock coefficient above
`2 / log(4/3)`, every positive orbit-height allowance, and every exceptional
exponent `γ` strictly below `κ_*(A - A_FP)` give a natural-density-one set
of starting values with one witness that simultaneously has a polylogarithmic
landing, a logarithmic clock, and an orbit ceiling.  The number of exceptions
up to `X` is eventually bounded by `C_exc X (log X)^(-γ)`.

This is an almost-all theorem. It does not prove pointwise Collatz convergence,
exclude exceptional cycles or divergent trajectories, or control the orbit
after the selected witness.
-/

namespace CollatzFirstPassage

open Filter
open scoped Real Topology

/-- The shortcut Collatz map, totalized at zero. -/
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The `k`-fold iterate of the shortcut Collatz map. -/
def orbit (k n : ℕ) : ℕ := (shortcut^[k]) n

/-- The number of positive integers at most `X` that do not belong to `S`. -/
noncomputable def badCount (S : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n => n ∉ S).card

/-- Natural density one, expressed through the complementary counting ratio. -/
def NaturalDensityOne (S : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (badCount S X : ℝ) / (X : ℝ)) atTop (nhds 0)

/-- Base-three logarithm of two. -/
noncomputable def logThreeTwo : ℝ := Real.log 2 / Real.log 3

/-- Binary entropy in base two. -/
noncomputable def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

/-- The endpoint entropy rate `κ_* = 1 - H₂(log₃ 2)`. -/
noncomputable def kappaStar : ℝ :=
  1 - binaryEntropyBaseTwo logThreeTwo

/-- The first-passage critical exponent `A_FP = 1 / (2 κ_*)`. -/
noncomputable def firstPassageCriticalExponent : ℝ :=
  1 / (2 * kappaStar)

/--
For every fixed polylogarithmic exponent above the displayed first-passage
threshold, every shortcut-clock coefficient above the displayed drift
threshold, every positive ceiling allowance, and every exceptional exponent
strictly below `κ_*(A - A_FP)`, there are positive constants `Ctar` and
`Cexc` such that:

* the starting values possessing one witness `k < c log n` with
  `orbit k n ≤ Ctar (log n)^A` and every earlier iterate at most `n^(1+beta)`
  have natural density one; and
* the number of starting values at most `X` without such a witness is
  eventually at most `Cexc X (log X)^(-gamma)`.
-/
theorem polylogarithmic_natural_density_descent
    {A c beta gamma : ℝ}
    (hA : firstPassageCriticalExponent < A)
    (hc : 2 / Real.log (4 / 3) < c)
    (hbeta : 0 < beta)
    (hgamma : 0 < gamma)
    (hgamma_lt : gamma < kappaStar * (A - firstPassageCriticalExponent)) :
    ∃ Ctar Cexc : ℝ,
      0 < Ctar ∧ 0 < Cexc ∧
      NaturalDensityOne
        {n : ℕ | ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) ≤ Ctar * (Real.log n) ^ A ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)} ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount
          {n : ℕ | ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) ≤ Ctar * (Real.log n) ^ A ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)} X : ℝ) ≤
          Cexc * X * (Real.log X) ^ (-gamma)) := by
  sorry

end CollatzFirstPassage
