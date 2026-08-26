import FirstPassageLinearTransport.PaperCor12Item1
import FirstPassageLinearTransport.TimeoutEndpointNaturalDensity
import FirstPassageLinearTransport.OrbitCeiling
import FirstPassageLinearTransport.QuantitativeNaturalDensityDescent

/-!
# Proved solution for the advertised Collatz statement

Comparator builds this module separately from `Challenge.lean`, checks that
the declarations below have exactly the same statement dependencies, and then
checks the proof against the permitted axiom surface.
-/

namespace CollatzFirstPassage

open Filter
open scoped Real Topology

def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def orbit (k n : ℕ) : ℕ := (shortcut^[k]) n

noncomputable def badCount (S : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n => n ∉ S).card

def NaturalDensityOne (S : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (badCount S X : ℝ) / (X : ℝ)) atTop (nhds 0)

def dyadicShell (M : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ M) (2 ^ (M + 1))

noncomputable def shellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n => n ∉ S

noncomputable def shellExceptionalRatio (S : Set ℕ) (M : ℕ) : ℝ :=
  ((shellBad S M).card : ℝ) / (2 : ℝ) ^ M

noncomputable def logThreeTwo : ℝ := Real.log 2 / Real.log 3

noncomputable def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

noncomputable def kappaStar : ℝ :=
  1 - binaryEntropyBaseTwo logThreeTwo

noncomputable def firstPassageCriticalExponent : ℝ :=
  1 / (2 * kappaStar)

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
  have hc' : FirstPassageLinearTransport.fixedPolylogClockCritical < c := by
    simpa [FirstPassageLinearTransport.fixedPolylogClockCritical_eq_paper] using hc
  have hbuffer' : Tendsto
      (FirstPassageLinearTransport.movingRankBuffer A) atTop atTop := by
    change Tendsto
      (fun M : ℕ =>
        (1 - FirstPassageLinearTransport.binaryEntropyBaseTwo
            FirstPassageLinearTransport.logThreeTwo) *
            (⌈A M * Real.logb 2 ((M : ℝ) + 2)⌉₊ : ℝ) -
          (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
          Real.logb 2 (Real.log ((M : ℝ) + 3)))
      atTop atTop
    simpa [kappaStar, binaryEntropyBaseTwo, logThreeTwo,
      FirstPassageLinearTransport.binaryEntropyBaseTwo,
      FirstPassageLinearTransport.logThreeTwo] using hbuffer
  obtain ⟨C, eps, hC, heps, hDense, hShell, _hWitness⟩ :=
    FirstPassageLinearTransport.timeoutEndpointLiteralNaturalDensityDescent
      hAmax hc' hbeta hbuffer' (Eventually.of_forall hUpper)
  have hshortcut : shortcut = FirstPassageLinearTransport.shortcut := by
    funext n
    rfl
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    simp only [orbit, FirstPassageLinearTransport.orbit, hshortcut]
  rw [horbit]
  refine ⟨C, eps, hC, heps, ?_, ?_⟩
  · have hset :
        FirstPassageLinearTransport.assembleDyadic
            (FirstPassageLinearTransport.timeoutEndpointWitnessGood
              A c beta C) =
          {n : ℕ | ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (FirstPassageLinearTransport.orbit k n : ℝ) <
              C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
            ∀ j : ℕ, j ≤ k →
              (FirstPassageLinearTransport.orbit j n : ℝ) ≤
                (n : ℝ) ^ (1 + beta)} := by
        rfl
    rw [hset] at hDense
    simpa only [NaturalDensityOne, badCount,
      FirstPassageLinearTransport.NaturalDensityOne,
      FirstPassageLinearTransport.badCount] using hDense
  · change ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio
        {n : ℕ | ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (FirstPassageLinearTransport.orbit k n : ℝ) <
            C * (Real.log n) ^ (A M) ∧
          ∀ j : ℕ, j ≤ k →
            (FirstPassageLinearTransport.orbit j n : ℝ) ≤
              (n : ℝ) ^ (1 + beta)} M ≤
        C * ((2 : ℝ) ^ (-(kappaStar *
            (⌈A M * Real.logb 2 ((M : ℝ) + 2)⌉₊ : ℝ) -
          (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
          Real.logb 2 (Real.log ((M : ℝ) + 3)))) +
          (((M : ℝ) + 2) ^ (-eps))) at hShell
    exact hShell

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
  have hA' : 1 / (2 *
      (1 - FirstPassageLinearTransport.binaryEntropyBaseTwo
        FirstPassageLinearTransport.logThreeTwo)) < A := by
    simpa only [firstPassageCriticalExponent, kappaStar,
      binaryEntropyBaseTwo, logThreeTwo,
      FirstPassageLinearTransport.binaryEntropyBaseTwo,
      FirstPassageLinearTransport.logThreeTwo] using hA
  have hgamma_lt' : gamma <
      FirstPassageLinearTransport.paperExceptionalExponentCeiling A := by
    rw [FirstPassageLinearTransport.paperExceptionalExponentCeiling,
      FirstPassageLinearTransport.paperKappaStar,
      FirstPassageLinearTransport.timeSupportCriticalExponent_eq_entropy]
    simpa only [firstPassageCriticalExponent, kappaStar,
      binaryEntropyBaseTwo, logThreeTwo,
      FirstPassageLinearTransport.binaryEntropyBaseTwo,
      FirstPassageLinearTransport.logThreeTwo] using hgamma_lt
  have hshortcut : shortcut = FirstPassageLinearTransport.shortcut := by
    funext n
    rfl
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    simp only [orbit, FirstPassageLinearTransport.orbit, hshortcut]
  rw [horbit]
  simpa only [binaryEntropyBaseTwo, logThreeTwo, NaturalDensityOne, badCount,
    FirstPassageLinearTransport.binaryEntropyBaseTwo,
    FirstPassageLinearTransport.logThreeTwo,
    FirstPassageLinearTransport.NaturalDensityOne,
    FirstPassageLinearTransport.badCount] using
    FirstPassageLinearTransport.paper_cor12_item1_fixed_polylog
      hA' hc hbeta hgamma hgamma_lt'

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
  have hshortcut : shortcut = FirstPassageLinearTransport.shortcut := by
    funext n
    rfl
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    simp only [orbit, FirstPassageLinearTransport.orbit, hshortcut]
  rw [horbit]
  simpa only [NaturalDensityOne, badCount,
    FirstPassageLinearTransport.NaturalDensityOne,
    FirstPassageLinearTransport.badCount] using
    FirstPassageLinearTransport.firstPassageLinearTransportOrbitCeiling
      hdelta0 hdelta1 hbeta

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
  have hshortcut : shortcut = FirstPassageLinearTransport.shortcut := by
    funext n
    rfl
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    simp only [orbit, FirstPassageLinearTransport.orbit, hshortcut]
  have hbadCount : badCount = FirstPassageLinearTransport.badCount := by
    funext S X
    rfl
  rw [horbit, hbadCount]
  simpa only [
    FirstPassageLinearTransport.HasStretchedLogDescent,
    FirstPassageLinearTransport.ReachesBelow] using
    FirstPassageLinearTransport.firstPassageLinearTransportQuantitativeStretched
      hdelta0 hdelta1 hsigma0 hsigma

end CollatzFirstPassage
