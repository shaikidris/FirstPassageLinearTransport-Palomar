import FirstPassageLinearTransport.PaperCor12Item1

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

noncomputable def logThreeTwo : ℝ := Real.log 2 / Real.log 3

noncomputable def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

noncomputable def kappaStar : ℝ :=
  1 - binaryEntropyBaseTwo logThreeTwo

noncomputable def firstPassageCriticalExponent : ℝ :=
  1 / (2 * kappaStar)

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

end CollatzFirstPassage
