import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat

/-!
# Strengthened almost-all Collatz descent in natural density

This Mathlib-only Challenge exposes four proved Version 4 consequences:
critical descent with arbitrary divergent multipliers and first-passage
profiles; the fixed-exponent exact upper rate; the height-forced joint
lower bound; and the quantitative stretched-logarithmic companion with a
common shortcut/raw landing and smaller relative-height ceilings.

All four are almost-all statements. They do not prove pointwise Collatz
convergence, exclude exceptional cycles or divergent trajectories, control
an orbit after the selected witness, or attain a fixed multiple of the pure
critical target.
-/

namespace CollatzFirstPassage

open Filter
open scoped BigOperators Real Topology

def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def orbit (k n : ℕ) : ℕ := (shortcut^[k]) n

def parityBit (n i : ℕ) : Fin 2 :=
  ⟨orbit i n % 2, Nat.mod_lt _ (by omega)⟩

def oddCount (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (parityBit n i : ℕ)

def rawCollatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def rawOrbit (i n : ℕ) : ℕ := (rawCollatz^[i]) n

def rawTime (n k : ℕ) : ℕ := k + oddCount n k

noncomputable def badCount (S : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n => n ∉ S).card

def NaturalDensityOne (S : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (badCount S X : ℝ) / (X : ℝ)) atTop (nhds 0)

noncomputable def logTwoThree : ℝ := Real.log 3 / Real.log 2

noncomputable def a0 : ℝ := logTwoThree / 2

noncomputable def driftGap : ℝ := 1 - a0

noncomputable def logThreeTwo : ℝ := Real.log 2 / Real.log 3

noncomputable def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

noncomputable def kappaStar : ℝ :=
  1 - binaryEntropyBaseTwo logThreeTwo

noncomputable def firstPassageCriticalExponent : ℝ :=
  1 / (2 * kappaStar)

noncomputable def fixedPolylogClockCritical : ℝ :=
  1 / (driftGap * Real.log 2)

noncomputable def fixedSharpEndpointMargin (A : ℝ) : ℝ :=
  kappaStar * A - 1 / 2

noncomputable def shortcutLogDeviation (n j : ℕ) : ℝ :=
  Real.log (orbit j n) - Real.log n +
    driftGap * (j : ℝ) * Real.log 2

noncomputable def rawLogDeviation (n i : ℕ) : ℝ :=
  Real.log (rawOrbit i n) - Real.log n +
    (2 * driftGap / 3) * (i : ℝ) * Real.log 2

noncomputable def shortcutFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {j : ℕ | (orbit j n : ℝ) ≤ z}

noncomputable def rawFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {i : ℕ | (rawOrbit i n : ℝ) ≤ z}

def HasVariableTargetHeightWitness
    (f u : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (orbit k n : ℝ) ≤ f n ∧
      ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ u n * (n : ℝ)

noncomputable def variableTargetHeightFailureCount
    (f u : ℕ → ℝ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n =>
    ¬HasVariableTargetHeightWitness f u n).card

noncomputable def fixedJointPolylogTarget (C A : ℝ) (n : ℕ) : ℝ :=
  C * (Real.log n) ^ A

noncomputable def fixedJointPolylogHeight (q : ℝ) (n : ℕ) : ℝ :=
  (((Nat.log 2 n : ℕ) : ℝ) + 2) ^ q

theorem critical_polylogarithmic_descent_with_arbitrary_multipliers
    {U R : ℕ → ℝ}
    (hUpos : ∀ n, 0 < U n) (hRpos : ∀ n, 0 < R n)
    (hU : Tendsto U atTop atTop) (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ K : ℝ,
      0 < K ∧ NaturalDensityOne S ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            (Real.log n) ^ firstPassageCriticalExponent * U n ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
            |(shortcutFirstPassageTime n z : ℝ) -
                fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
              |(rawFirstPassageTime n z : ℝ) -
                (3 / 2) * fixedPolylogClockCritical *
                  Real.log ((n : ℝ) / z)| ≤
                K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                  Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
            rawOrbit (rawFirstPassageTime n z) n =
              orbit (shortcutFirstPassageTime n z) n)) := by
  sorry
theorem fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
    {A c beta : ℝ}
    (hA : firstPassageCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta) :
    ∃ S : Set ℕ, ∃ C Cexc : ℝ,
      0 < C ∧ 0 < Cexc ∧ NaturalDensityOne S ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤
          Cexc * X * (Real.log X) ^
            (-(fixedSharpEndpointMargin A))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ A ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A))) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A)))) := by
  sorry
theorem eventually_fixedJointPolylogHeightFailureCount_ge_log_order
    {C A q : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hq : 0 < q) :
    ∀ᶠ X : ℕ in atTop,
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by
  sorry
theorem stretchedLogCommonLandingWithRelativeHeightQuantitative
    {delta sigma zeta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 - delta)
    (hzeta : 0 < zeta) :
    ∃ S : Set ℕ, ∃ c : ℝ,
      0 < c ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤
          13 * X * Real.exp (-c * (Real.log X) ^ sigma)) ∧
      (∀ᶠ n : ℕ in atTop,
        n ∈ S →
          ∃ k ell : ℕ,
            (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
            (ell : ℝ) < (261 / 25 : ℝ) * Real.log n ∧
            orbit k n = rawOrbit ell n ∧
            (orbit k n : ℝ) ≤
              Real.exp ((Real.log n) ^ (1 - delta)) ∧
            (∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤
                (n : ℝ) * Real.exp
                  (zeta * (Real.log n) ^ (1 - delta))) ∧
            (∀ i : ℕ, i ≤ ell →
              (rawOrbit i n : ℝ) ≤
                (n : ℝ) * Real.exp
                  (zeta * (Real.log n) ^ (1 - delta)))) := by
  sorry
end CollatzFirstPassage
