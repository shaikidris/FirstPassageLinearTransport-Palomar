import FirstPassageLinearTransport.CriticalEndpointConsequences
import FirstPassageLinearTransport.FixedJointExceptionalOrder
import FirstPassageLinearTransport.StretchedRelativeHeight

/-! Proved wrappers for the strengthened Palomar statement surface. -/

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
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    rfl
  have hodd : oddCount = FirstPassageLinearTransport.oddCount := by
    funext n k
    rfl
  have hrawOrbit : rawOrbit = FirstPassageLinearTransport.rawOrbit := by
    funext i n
    rfl
  have hrawTime : rawTime = FirstPassageLinearTransport.rawTime := by
    funext n k
    rfl
  have hbad : badCount = FirstPassageLinearTransport.badCount := by
    funext S X
    rfl
  have hnd : NaturalDensityOne =
      FirstPassageLinearTransport.NaturalDensityOne := by
    funext S
    rfl
  have hgap : driftGap = FirstPassageLinearTransport.driftGap := by rfl
  have hcritical : firstPassageCriticalExponent =
      FirstPassageLinearTransport.timeSupportCriticalExponent := by
    rw [FirstPassageLinearTransport.timeSupportCriticalExponent_eq_entropy]
    rfl
  have hclock : fixedPolylogClockCritical =
      FirstPassageLinearTransport.fixedPolylogClockCritical := by rfl
  have hshortcutDev : shortcutLogDeviation =
      FirstPassageLinearTransport.shortcutLogDeviation := by
    funext n j
    rfl
  have hrawDev : rawLogDeviation =
      FirstPassageLinearTransport.rawLogDeviation := by
    funext n i
    rfl
  have hshortcutFP : shortcutFirstPassageTime =
      FirstPassageLinearTransport.shortcutFirstPassageTime := by
    funext n z
    rfl
  have hrawFP : rawFirstPassageTime =
      FirstPassageLinearTransport.rawFirstPassageTime := by
    funext n z
    rfl
  simpa only [horbit, hodd, hrawOrbit, hrawTime, hnd, hcritical, hgap,
    hclock, hshortcutDev, hrawDev, hshortcutFP, hrawFP] using
    FirstPassageLinearTransport.critical_polylogarithmic_descent_with_arbitrary_multipliers
      hUpos hRpos hU hR

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
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    rfl
  have hodd : oddCount = FirstPassageLinearTransport.oddCount := by
    funext n k
    rfl
  have hrawOrbit : rawOrbit = FirstPassageLinearTransport.rawOrbit := by
    funext i n
    rfl
  have hrawTime : rawTime = FirstPassageLinearTransport.rawTime := by
    funext n k
    rfl
  have hbad : badCount = FirstPassageLinearTransport.badCount := by
    funext S X
    rfl
  have hnd : NaturalDensityOne =
      FirstPassageLinearTransport.NaturalDensityOne := by
    funext S
    rfl
  have hgap : driftGap = FirstPassageLinearTransport.driftGap := by rfl
  have hcritical : firstPassageCriticalExponent =
      FirstPassageLinearTransport.timeSupportCriticalExponent := by
    rw [FirstPassageLinearTransport.timeSupportCriticalExponent_eq_entropy]
    rfl
  have hclock : fixedPolylogClockCritical =
      FirstPassageLinearTransport.fixedPolylogClockCritical := by rfl
  have hmargin : fixedSharpEndpointMargin =
      FirstPassageLinearTransport.fixedSharpEndpointMargin := by
    funext A
    unfold fixedSharpEndpointMargin
    unfold FirstPassageLinearTransport.fixedSharpEndpointMargin
    unfold kappaStar binaryEntropyBaseTwo logThreeTwo
    unfold FirstPassageLinearTransport.firstPassageEntropyGap
    unfold FirstPassageLinearTransport.binaryEntropyBaseTwo
    unfold FirstPassageLinearTransport.logThreeTwo
    rfl
  have hA' : FirstPassageLinearTransport.timeSupportCriticalExponent < A := by
    simpa only [hcritical] using hA
  have hc' : FirstPassageLinearTransport.fixedPolylogClockCritical < c := by
    simpa only [hclock] using hc
  simpa only [horbit, hodd, hrawOrbit, hrawTime, hbad, hnd, hgap,
    hmargin] using
    FirstPassageLinearTransport.fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
      hA' hc' hbeta

theorem eventually_fixedJointPolylogHeightFailureCount_ge_log_order
    {C A q : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hq : 0 < q) :
    ∀ᶠ X : ℕ in atTop,
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by
  have hfailure : variableTargetHeightFailureCount =
      FirstPassageLinearTransport.variableTargetHeightFailureCount := by
    funext f u X
    rfl
  have htarget : fixedJointPolylogTarget =
      FirstPassageLinearTransport.fixedJointPolylogTarget := by
    funext C A n
    rfl
  have hheight : fixedJointPolylogHeight =
      FirstPassageLinearTransport.fixedJointPolylogHeight := by
    funext q n
    rfl
  simpa only [hfailure, htarget, hheight] using
    FirstPassageLinearTransport.eventually_fixedJointPolylogHeightFailureCount_ge_log_order
      hC hA hq

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
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    rfl
  have hrawOrbit : rawOrbit = FirstPassageLinearTransport.rawOrbit := by
    funext i n
    rfl
  have hbad : badCount = FirstPassageLinearTransport.badCount := by
    funext S X
    rfl
  simpa only [horbit, hrawOrbit, hbad] using
    FirstPassageLinearTransport.stretchedLogCommonLandingWithRelativeHeightQuantitative
      hdelta0 hdelta1 hsigma0 hsigma hzeta

end CollatzFirstPassage
