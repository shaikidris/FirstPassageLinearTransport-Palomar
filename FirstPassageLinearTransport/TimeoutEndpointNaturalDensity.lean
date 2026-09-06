/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.MovingEndpointAssembly
import FirstPassageLinearTransport.TimeoutEndpointAsymptotics
import FirstPassageLinearTransport.TimeoutEndpointWitness

/-!
# Natural-density assembly for the timeout endpoint

This module is the capstone for the timeout proof.  Its low phase is
defined by one literal first-timeout event, rather than an all-prefix low-stage
certificate.  The generic dyadic assembly is shared with the established
moving-endpoint route; the shell producer and same-witness theorem are the new
timeout results.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Literal shell witness exposed by the timeout proof. -/
def timeoutEndpointWitnessGood
    (A : ℕ → ℝ) (c beta C : ℝ) (M : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k : ℕ,
    (k : ℝ) < c * Real.log n ∧
    (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
    ∀ j : ℕ, j ≤ k →
      (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)}

/-- Complete timeout-endpoint theorem, retaining its literal shell error. -/
theorem timeoutEndpointNaturalDensityDescent
    {A : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ S : Set ℕ, ∃ C eps : ℝ,
      0 < C ∧ 0 < eps ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps)))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) := by
  let P : MovingEndpointParameterPackage Amax c beta :=
    Classical.choice (exists_movingEndpointParameterPackage hAmax hc hbeta)
  obtain ⟨Cprof, hCprof, hProfile⟩ :=
    exists_eventually_timeoutEndpointGood_shellError P hbuffer hUpper
  let C := max Cprof (fixedPolylogTargetConstant Amax) + 1
  let S : Set ℕ := assembleDyadic (timeoutEndpointGood P A)
  have hCprofC : Cprof ≤ C := by
    dsimp [C]
    linarith [le_max_left Cprof (fixedPolylogTargetConstant Amax)]
  have hTargetC : fixedPolylogTargetConstant Amax ≤ C := by
    dsimp [C]
    linarith [le_max_right Cprof (fixedPolylogTargetConstant Amax)]
  have hC : 0 < C := hCprof.trans_le hCprofC
  have hShellFamily : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (timeoutEndpointGood P A M) M ≤
        C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) := by
    filter_upwards [hProfile] with M hProfile
    have herror0 : 0 ≤
        (2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon)) := by positivity
    exact hProfile.trans (mul_le_mul_of_nonneg_right hCprofC herror0)
  have hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) := by
    filter_upwards [hShellFamily] with M hM
    rw [shellExceptionalRatio, shellBad_assembleDyadic]
    exact hM
  have hWitnessBase := eventually_timeoutEndpointGood_has_shellWitness
    P hbuffer hUpper
  have hc0 : 0 < c := fixedPolylogClockCritical_pos.trans hc
  have hWitness : ∀ᶠ M : ℕ in atTop,
      ∀ n : ℕ, n ∈ dyadicShell M → n ∈ timeoutEndpointGood P A M →
        ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
    filter_upwards [hWitnessBase] with M hWitnessBase
    intro n hnShell hnGood
    obtain ⟨k, hk, hlanding, hceiling⟩ :=
      hWitnessBase n hnShell hnGood
    refine ⟨k, hk.trans_le (shellClock_le_natLog hc0.le hnShell),
      hlanding.trans_le ?_, hceiling⟩
    have hlogPow0 : 0 ≤ (Real.log n) ^ (A M) := by positivity
    exact mul_le_mul_of_nonneg_right hTargetC hlogPow0
  have hAssembly := movingEndpointNaturalDensityAssembly
    (timeoutEndpointGood P A) P.epsilon_pos hbuffer hShellFamily hWitness
  refine ⟨S, C, P.epsilon, hC, P.epsilon_pos, ?_, hShell, ?_⟩
  · simpa [S] using hAssembly.1
  · simpa [S] using hAssembly.2

/-- Referee-facing timeout form: the shell exceptional set is literally the
set of sources without a simultaneous landing/clock/ceiling witness. -/
theorem timeoutEndpointLiteralNaturalDensityDescent
    {A : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C eps : ℝ,
      0 < C ∧ 0 < eps ∧
      NaturalDensityOne
        (assembleDyadic (timeoutEndpointWitnessGood A c beta C)) ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio
            (timeoutEndpointWitnessGood A c beta C M) M ≤
          C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps)))) ∧
      (∀ n : ℕ,
        n ∈ assembleDyadic (timeoutEndpointWitnessGood A c beta C) →
          ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) <
              C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) := by
  obtain ⟨S, C, eps, hC, heps, hSdense, hShellS, hWitnessS⟩ :=
    timeoutEndpointNaturalDensityDescent hAmax hc hbeta hbuffer hUpper
  rw [eventually_atTop] at hWitnessS
  obtain ⟨N, hWitnessN⟩ := hWitnessS
  have hpowT : Tendsto (fun M : ℕ => (2 : ℝ) ^ M) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hPow := (tendsto_atTop.1 hpowT) (N : ℝ)
  have hShellW : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio
          (timeoutEndpointWitnessGood A c beta C M) M ≤
        C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))) := by
    classical
    filter_upwards [hShellS, hPow] with M hShellS hPow
    have hNpow : N ≤ 2 ^ M := by exact_mod_cast hPow
    have hsubset :
        shellBad (timeoutEndpointWitnessGood A c beta C M) M ⊆
          shellBad S M := by
      intro n hn
      rw [shellBad, Finset.mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      intro hnS
      have hnN : N ≤ n := hNpow.trans (mem_dyadicShell.mp hn.1).1
      have hwitness := hWitnessN n hnN hnS
      have hlog : Nat.log 2 n = M := log_two_eq_of_mem_dyadicShell hn.1
      exact hn.2 (by
        simpa [timeoutEndpointWitnessGood, hlog] using hwitness)
    have hcard :
        ((shellBad (timeoutEndpointWitnessGood A c beta C M) M).card : ℝ) ≤
          ((shellBad S M).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    unfold shellExceptionalRatio at hShellS ⊢
    exact (div_le_div_of_nonneg_right hcard (by positivity)).trans hShellS
  have hDense := naturalDensityOne_of_movingShellError
    (timeoutEndpointWitnessGood A c beta C) heps hbuffer hShellW
  refine ⟨C, eps, hC, heps, hDense, hShellW, ?_⟩
  intro n hn
  simpa [assembleDyadic, timeoutEndpointWitnessGood] using hn

/-- Version 4 moving-endpoint assembly with one common shortcut/raw landing
and a prescribed divergent relative-height allowance on both trajectories.
The sharp critical buffer contains no secondary logarithmic debit. -/
theorem timeoutStrengthenedEndpointNaturalDensityDescentOfPackage
    {A R : ℕ → ℝ} {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ C : ℝ,
      0 < C ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) + 4 / R M) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n) / 2) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n))) := by
  have hR4 : ∀ᶠ M : ℕ in atTop, 4 ≤ R M :=
    (tendsto_atTop.1 hR) 4
  obtain ⟨Cprof, hCprof, hProfile⟩ :=
    exists_eventually_timeoutStrengthenedEndpointGood_sharpShellError
      P hbuffer hUpper hR4
  let C := max
    (max
      (max Cprof (fixedPolylogTargetConstant Amax))
      (max
        (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
        (timeoutCompletedRawClockSupportConstant
          P.run.toTimeoutHigh P.Cswitch)))
    (max
      (timeoutCompletedOddTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch)
      (timeoutCompletedRawTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch)) + 1
  let S : Set ℕ := assembleDyadic (timeoutStrengthenedEndpointGood P A R)
  have hCprofC : Cprof ≤ C := by
    have h₁ : Cprof ≤ max Cprof (fixedPolylogTargetConstant Amax) :=
      le_max_left _ _
    have h₂ : max Cprof (fixedPolylogTargetConstant Amax) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) :=
      le_max_left _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hTargetC : fixedPolylogTargetConstant Amax ≤ C := by
    have h₁ : fixedPolylogTargetConstant Amax ≤
        max Cprof (fixedPolylogTargetConstant Amax) := le_max_right _ _
    have h₂ : max Cprof (fixedPolylogTargetConstant Amax) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) :=
      le_max_left _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hClockC :
      2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : 2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch ≤
        max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_left _ _
    have h₂ : max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_right _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hRawClockC :
      timeoutCompletedRawClockSupportConstant
        P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : timeoutCompletedRawClockSupportConstant
          P.run.toTimeoutHigh P.Cswitch ≤
        max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_right _ _
    have h₂ : max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch) ≤
        max (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_right _ _
    have h₃ : max
          (max Cprof (fixedPolylogTargetConstant Amax))
          (max
            (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawClockSupportConstant
              P.run.toTimeoutHigh P.Cswitch)) ≤
        max
          (max
            (max Cprof (fixedPolylogTargetConstant Amax))
            (max
              (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
              (timeoutCompletedRawClockSupportConstant
                P.run.toTimeoutHigh P.Cswitch)))
          (max
            (timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)
            (timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch)) := le_max_left _ _
    dsimp [C]
    linarith
  have hOddTubeC :
      timeoutCompletedOddTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : timeoutCompletedOddTrajectorySupportConstant
          P.run.toTimeoutHigh P.Cswitch ≤
        max
          (timeoutCompletedOddTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_left _ _
    have h₂ := h₁.trans (le_max_right
      (max
        (max Cprof (fixedPolylogTargetConstant Amax))
        (max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch))) _)
    dsimp [C]
    linarith
  have hRawTubeC :
      timeoutCompletedRawTrajectorySupportConstant
        P.run.toTimeoutHigh P.Cswitch ≤ C := by
    have h₁ : timeoutCompletedRawTrajectorySupportConstant
          P.run.toTimeoutHigh P.Cswitch ≤
        max
          (timeoutCompletedOddTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawTrajectorySupportConstant
            P.run.toTimeoutHigh P.Cswitch) := le_max_right _ _
    have h₂ := h₁.trans (le_max_right
      (max
        (max Cprof (fixedPolylogTargetConstant Amax))
        (max
          (2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch)
          (timeoutCompletedRawClockSupportConstant
            P.run.toTimeoutHigh P.Cswitch))) _)
    dsimp [C]
    linarith
  have hC : 0 < C := hCprof.trans_le hCprofC
  have hShellFamily : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (timeoutStrengthenedEndpointGood P A R M) M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) + 4 / R M := by
    filter_upwards [hProfile] with M hProfile
    have herror0 : 0 ≤
        (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon)) := by positivity
    exact hProfile.trans (add_le_add
      (mul_le_mul_of_nonneg_right hCprofC herror0) le_rfl)
  have hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) + 4 / R M := by
    filter_upwards [hShellFamily] with M hM
    rw [shellExceptionalRatio, shellBad_assembleDyadic]
    exact hM
  have hDense : NaturalDensityOne S := by
    simpa [S] using naturalDensityOne_of_sharpMovingShellErrorWithHeight
      (timeoutStrengthenedEndpointGood P A R) P.epsilon_pos hbuffer hR
        hShellFamily
  have hWitnessBase :=
    eventually_timeoutStrengthenedEndpointGood_has_shellWitness
      P hbuffer hUpper hR4
  have hc0 : 0 < c := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hinv : 0 < 1 / driftGap := one_div_pos.mpr driftGap_pos
    by_contra h
    have hcNonpos : c ≤ 0 := le_of_not_gt h
    have : c * Real.log 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcNonpos hlog2.le
    linarith [P.clock_pressure]
  have hWitness : ∀ᶠ M : ℕ in atTop,
      ∀ n : ℕ, n ∈ dyadicShell M →
        n ∈ timeoutStrengthenedEndpointGood P A R M →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (M : ℝ)| ≤
            C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (M : ℝ)| ≤
            C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              C * Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ (A M) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) * R M / 2) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤ (n : ℝ) * R M) := by
    filter_upwards [hWitnessBase] with M hWitnessBase
    intro n hnShell hnGood
    obtain ⟨k, ell, hk, hkCentered, hellCentered, hshortcutTube, hoddTube,
        hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw⟩ :=
      hWitnessBase n hnShell hnGood
    have hroot0 : 0 ≤
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) :=
      Real.sqrt_nonneg _
    refine ⟨k, ell, hk.trans_le (shellClock_le_natLog hc0.le hnShell),
      hkCentered.trans (mul_le_mul_of_nonneg_right hClockC hroot0),
      hellCentered.trans (mul_le_mul_of_nonneg_right hRawClockC hroot0),
      (fun j hj ↦ (hshortcutTube j hj).trans
        (mul_le_mul_of_nonneg_right hClockC hroot0)),
      (fun j hj ↦ (hoddTube j hj).trans
        (mul_le_mul_of_nonneg_right hOddTubeC hroot0)),
      (fun i hi ↦ (hrawTube i hi).trans
        (mul_le_mul_of_nonneg_right hRawTubeC hroot0)),
      hell, hlandingEq, hlanding.trans_le ?_, hshortcut, hraw⟩
    have hlogPow0 : 0 ≤ (Real.log n) ^ (A M) := by positivity
    exact mul_le_mul_of_nonneg_right hTargetC hlogPow0
  have hAtLog := tendsto_natLogTwo_atTop.eventually hWitness
  refine ⟨S, C, hC, hDense, hShell, ?_⟩
  filter_upwards [hAtLog, eventually_ge_atTop (1 : ℕ)] with n hAtLog hn
  intro hnSet
  have hnpos : 0 < n := by omega
  let M := Nat.log 2 n
  have hnShell : n ∈ dyadicShell M := mem_dyadicShell_log hnpos
  have hnGood : n ∈ timeoutStrengthenedEndpointGood P A R M := by
    simpa [S, assembleDyadic, M] using hnSet
  simpa [M] using hAtLog n hnShell hnGood

/-- Version 4 moving-endpoint assembly with parameters constructed from the
paper's admissible exponent bound, shortcut clock, and height slack. -/
theorem timeoutStrengthenedEndpointNaturalDensityDescent
    {A R : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ C eps : ℝ,
      0 < C ∧ 0 < eps ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps))) + 4 / R M) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n) / 2) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n))) := by
  let P : MovingEndpointParameterPackage Amax c beta :=
    Classical.choice (exists_movingEndpointParameterPackage hAmax hc hbeta)
  obtain ⟨S, C, hC, hDense, hShell, hWitness⟩ :=
    timeoutStrengthenedEndpointNaturalDensityDescentOfPackage
      P hbuffer hUpper hR
  exact ⟨S, C, P.epsilon, hC, P.epsilon_pos, hDense, hShell, hWitness⟩

/-- Version 4 moving-endpoint theorem with the uniform trajectory tubes and
the simultaneous actual shortcut/raw first-passage profile exposed in one
public statement. -/
theorem timeoutStrengthenedEndpointNaturalDensityDescentWithFirstPassage
    {A R : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ K eps : ℝ,
      0 < K ∧ 0 < eps ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          K * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps))) + 4 / R M) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
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
            K * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n) / 2) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * R (Nat.log 2 n)) ∧
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
  obtain ⟨S, C₀, eps, hC₀, heps, hDense, hShell, hWitness⟩ :=
    timeoutStrengthenedEndpointNaturalDensityDescent
      hAmax hc hbeta hbuffer hUpper hR
  let Kprofile := (5 / 2) * fixedPolylogClockCritical *
    (C₀ + Real.log 2)
  let K := max C₀ Kprofile + 1
  have hC₀K : C₀ ≤ K := by
    dsimp [K]
    linarith [le_max_left C₀ Kprofile]
  have hProfileK : Kprofile ≤ K := by
    dsimp [K]
    linarith [le_max_right C₀ Kprofile]
  have hK : 0 < K := hC₀.trans_le hC₀K
  have hShell' : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        K * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))) + 4 / R M := by
    filter_upwards [hShell] with M hShell
    have herror0 : 0 ≤
        (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps)) := by positivity
    exact hShell.trans (add_le_add
      (mul_le_mul_of_nonneg_right hC₀K herror0) le_rfl)
  have hLogRank : ∀ᶠ n : ℕ in atTop, 1 ≤ Nat.log 2 n :=
    tendsto_natLogTwo_atTop.eventually (eventually_ge_atTop 1)
  have hWitness' : ∀ᶠ n : ℕ in atTop, n ∈ S →
      ∃ k ell : ℕ,
        (k : ℝ) < c * Real.log n ∧
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
        (orbit k n : ℝ) < K * (Real.log n) ^ (A (Nat.log 2 n)) ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) * R (Nat.log 2 n) / 2) ∧
        (∀ i : ℕ, i ≤ ell →
          (rawOrbit i n : ℝ) ≤ (n : ℝ) * R (Nat.log 2 n)) ∧
        (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
          |(shortcutFirstPassageTime n z : ℝ) -
              fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
            |(rawFirstPassageTime n z : ℝ) -
              (3 / 2) * fixedPolylogClockCritical *
                Real.log ((n : ℝ) / z)| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          rawOrbit (rawFirstPassageTime n z) n =
            orbit (shortcutFirstPassageTime n z) n) := by
    filter_upwards [hWitness, hLogRank, eventually_ge_atTop (1 : ℕ)]
      with n hWitness hM hn
    intro hnS
    obtain ⟨k, ell, hk, hkCentered, hellCentered, hshortcutTube, hoddTube,
        hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw⟩ := hWitness hnS
    let root := Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
      Real.log ((Nat.log 2 n : ℝ) + 2))
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hroot1 : 1 ≤ root := by
      simpa [root] using one_le_timeoutProfileRoot hM
    have hnpos : 0 < n := by omega
    have hpow0 : 0 ≤ (Real.log n) ^ (A (Nat.log 2 n)) := by positivity
    have hactual : ∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
        |(shortcutFirstPassageTime n z : ℝ) -
            fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
          |(rawFirstPassageTime n z : ℝ) -
            (3 / 2) * fixedPolylogClockCritical *
              Real.log ((n : ℝ) / z)| ≤ K * root ∧
        rawOrbit (rawFirstPassageTime n z) n =
          orbit (shortcutFirstPassageTime n z) n := by
      intro z hzLanding hzSource
      have hsim := simultaneousFirstPassageTime_centered_profile
        hnpos hzLanding hzSource hell
        (fun j hj ↦ by simpa [root] using hshortcutTube j hj)
        (fun i hi ↦ by simpa [root] using hrawTube i hi)
      have hlogTwo0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      have hinner : C₀ * root + Real.log 2 ≤
          (C₀ + Real.log 2) * root := by
        nlinarith [mul_nonneg hlogTwo0 (sub_nonneg.mpr hroot1)]
      have hcoef0 : 0 ≤ (5 / 2) * fixedPolylogClockCritical := by
        exact mul_nonneg (by norm_num) fixedPolylogClockCritical_pos.le
      have hprofile :
          fixedPolylogClockCritical * (C₀ * root + Real.log 2) +
              (3 / 2) * fixedPolylogClockCritical *
                (C₀ * root + Real.log 2) ≤ K * root := by
        calc
          _ = (5 / 2) * fixedPolylogClockCritical *
                (C₀ * root + Real.log 2) := by ring
          _ ≤ (5 / 2) * fixedPolylogClockCritical *
                ((C₀ + Real.log 2) * root) :=
            mul_le_mul_of_nonneg_left hinner hcoef0
          _ = Kprofile * root := by simp [Kprofile]; ring
          _ ≤ K * root := mul_le_mul_of_nonneg_right hProfileK hroot0
      exact ⟨hsim.1.trans hprofile, hsim.2⟩
    refine ⟨k, ell, hk,
      hkCentered.trans (mul_le_mul_of_nonneg_right hC₀K hroot0),
      hellCentered.trans (mul_le_mul_of_nonneg_right hC₀K hroot0),
      (fun j hj ↦ (hshortcutTube j hj).trans
        (mul_le_mul_of_nonneg_right hC₀K hroot0)),
      (fun j hj ↦ (hoddTube j hj).trans
        (mul_le_mul_of_nonneg_right hC₀K hroot0)),
      (fun i hi ↦ (hrawTube i hi).trans
        (mul_le_mul_of_nonneg_right hC₀K hroot0)),
      hell, hlandingEq,
      hlanding.trans_le (mul_le_mul_of_nonneg_right hC₀K hpow0),
      hshortcut, hraw, hactual⟩
  exact ⟨S, K, eps, hK, heps, hDense, hShell', hWitness'⟩

end

end FirstPassageLinearTransport
