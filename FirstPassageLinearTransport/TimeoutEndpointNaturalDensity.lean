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

end

end FirstPassageLinearTransport
