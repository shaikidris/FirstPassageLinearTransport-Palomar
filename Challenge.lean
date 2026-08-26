import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat

/-!
# Almost-all Collatz descent in natural density

This independent statement surface exposes four formally proved results from
*Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density*:

* the general moving-endpoint first-passage theorem, including its dyadic-shell
  exceptional-ratio estimate;
* the fixed-exponent polylogarithmic specialization with the explicit entropy
  threshold and a power-logarithmic exceptional-count bound;
* a stretched-logarithmic same-witness companion with a `6.953 log n` clock
  and an orbit ceiling; and
* a quantitative stretched-logarithmic exceptional-count theorem retaining
  every strict exponent `sigma < 1 - delta`.

All four are almost-all results. They do not prove pointwise Collatz
convergence, exclude exceptional cycles or divergent trajectories, or control
an orbit after the selected witness.
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

/-- The dyadic shell `[2^M, 2^(M+1))`. -/
def dyadicShell (M : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ M) (2 ^ (M + 1))

/-- The elements of a dyadic shell outside a set. -/
noncomputable def shellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n => n ∉ S

/-- The exceptional proportion of a set on one dyadic shell. -/
noncomputable def shellExceptionalRatio (S : Set ℕ) (M : ℕ) : ℝ :=
  ((shellBad S M).card : ℝ) / (2 : ℝ) ^ M

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
The moving-endpoint first-passage theorem. A bounded exponent profile whose
explicit entropy buffer tends to infinity produces positive constants `C` and
`eps`, a natural-density-one same-witness landing set, and the displayed
quantitative exceptional-ratio estimate on every sufficiently large dyadic
shell.
-/
theorem moving_polylogarithmic_natural_density_descent
    {A : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hUpper : ∀ M : ℕ, A M ≤ Amax)
    (hc : 2 / Real.log (4 / 3) < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto
      (fun M : ℕ =>
        kappaStar *
            (⌈A M * Real.logb 2 ((M : ℝ) + 2)⌉₊ : ℝ) -
          (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
          Real.logb 2 (Real.log ((M : ℝ) + 3)))
      atTop atTop) :
    ∃ C eps : ℝ,
      0 < C ∧ 0 < eps ∧
      NaturalDensityOne
        {n : ℕ | ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)} ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio
          {n : ℕ | ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)} M ≤
          C * ((2 : ℝ) ^ (-(kappaStar *
              (⌈A M * Real.logb 2 ((M : ℝ) + 2)⌉₊ : ℝ) -
            (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
            Real.logb 2 (Real.log ((M : ℝ) + 3)))) +
            (((M : ℝ) + 2) ^ (-eps)))) := by
  sorry

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

/--
For every `0 < delta < 1` and `beta > 0`, a natural-density-one set of
starting values has one shortcut-Collatz witness before `6.953 log n` steps
that reaches `exp((log n)^(1-delta))`; every iterate through that same witness
is at most `n^(1+beta)`.
-/
theorem stretched_logarithmic_descent_with_orbit_ceiling
    {delta beta : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta1 : delta < 1)
    (hbeta : 0 < beta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
      ∀ᶠ n : ℕ in atTop,
        n ∈ S →
          ∃ k : ℕ,
            (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
            (orbit k n : ℝ) ≤
              Real.exp ((Real.log n) ^ (1 - delta)) ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  sorry

/--
For every `0 < delta < 1` and every strict exceptional exponent
`0 < sigma < 1 - delta`, the number of starting values at most `X` that do
not have any shortcut-Collatz iterate below
`exp((log n)^(1-delta))` is eventually at most
`5 X exp(-c (log X)^sigma)` for some `c > 0`.

This quantitative declaration counts the unclocked landing predicate.  It is
separate from the preceding same-witness clock-and-ceiling declaration and
does not assert the endpoint exponent `sigma = 1 - delta`.
-/
theorem stretched_logarithmic_quantitative_exceptional_count
    {delta sigma : ℝ}
    (hdelta0 : 0 < delta)
    (hdelta1 : delta < 1)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - delta) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount
        {n : ℕ | ∃ k : ℕ,
          (orbit k n : ℝ) ≤
            Real.exp ((Real.log n) ^ (1 - delta))} X : ℝ) ≤
        5 * X * Real.exp (-c * (Real.log X) ^ sigma) := by
  sorry

end CollatzFirstPassage
