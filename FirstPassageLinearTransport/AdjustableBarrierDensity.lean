/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import FirstPassageLinearTransport.AdjustableEnvelope
import FirstPassageLinearTransport.BarrierDensity

/-!
# Entropy-sharp density for the adjustable maximal barrier

This module connects the exact entropy tail to the adjustable deterministic
orbit envelope.  The two finite-startup inequalities are proved eventually
from their positive exponent margins; no finite computation is used.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Boolean-walk displacement corresponding to the adjustable orbit barrier. -/
def adjustableBarrierDisplacement (lambda t : ℝ) : ℝ :=
  lambda * t / logTwoThree

theorem adjustableBarrierHeight_eq_displacement_mul
    (lambda t : ℝ) (M : ℕ) :
    adjustableBarrierHeight lambda t M =
      adjustableBarrierDisplacement lambda t * (M : ℝ) := by
  unfold adjustableBarrierHeight adjustableBarrierDisplacement
  ring

theorem adjustableBarrierDisplacement_nonneg
    {lambda t : ℝ} (hlambda : 0 ≤ lambda) (ht : 0 ≤ t) :
    0 ≤ adjustableBarrierDisplacement lambda t := by
  exact div_nonneg (mul_nonneg hlambda ht) logTwoThree_pos.le

theorem adjustableBarrierDisplacement_lt_half
    {lambda t : ℝ} (hlambda : lambda ≤ 1) (ht0 : 0 ≤ t) (htA : t < a0) :
    adjustableBarrierDisplacement lambda t < 1 / 2 := by
  have hlt : lambda * t < a0 :=
    (mul_le_mul_of_nonneg_right hlambda ht0).trans_lt (by simpa using htA)
  rw [show (1 / 2 : ℝ) = a0 / logTwoThree by
    unfold a0
    field_simp [ne_of_gt logTwoThree_pos]]
  exact (div_lt_div_iff_of_pos_right logTwoThree_pos).2 hlt

/-- Both startup inequalities for the adjustable envelope hold at every
sufficiently large shell rank. -/
theorem eventually_adjustableBarrier_startups
    {lambda t : ℝ} (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ M : ℕ in atTop,
      1 ≤ (1 - lambda) * t * (M : ℝ) ∧
        2 * (2 + Real.sqrt 3) ≤
          (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ)) := by
  have hmainGap : 0 < (1 - lambda) * t :=
    mul_pos (sub_pos.mpr hlambda1) ht0
  have hlambdaMul : lambda * t ≤ t := by
    have := mul_le_mul_of_nonneg_right hlambda1.le ht0.le
    simpa using this
  have hcorrGap : 0 < a0 + t - 2 * lambda * t := by
    nlinarith
  have hmainTendsto :
      Tendsto (fun M : ℕ => (1 - lambda) * t * (M : ℝ)) atTop atTop := by
    simpa [mul_assoc] using
      tendsto_natCast_atTop_atTop.const_mul_atTop hmainGap
  have hcorrExponentTendsto :
      Tendsto (fun M : ℕ =>
        (a0 + t - 2 * lambda * t) * (M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hcorrGap
  have hcorrTendsto :
      Tendsto (fun M : ℕ =>
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) atTop atTop :=
    by
      have hlogTendsto :
          Tendsto (fun M : ℕ =>
            Real.log 2 * ((a0 + t - 2 * lambda * t) * (M : ℝ)))
            atTop atTop :=
        hcorrExponentTendsto.const_mul_atTop
          (Real.log_pos (by norm_num))
      have hexp := Real.tendsto_exp_atTop.comp hlogTendsto
      exact hexp.congr' (Eventually.of_forall fun M => by
        simp [Function.comp_def,
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)])
  obtain ⟨Mmain, hMmain⟩ := tendsto_atTop_atTop.mp hmainTendsto 1
  obtain ⟨Mcorr, hMcorr⟩ := tendsto_atTop_atTop.mp hcorrTendsto
    (2 * (2 + Real.sqrt 3))
  filter_upwards [eventually_ge_atTop (max Mmain Mcorr)] with M hM
  exact ⟨hMmain M (le_trans (Nat.le_max_left _ _) hM),
    hMcorr M (le_trans (Nat.le_max_right _ _) hM)⟩

/-- A failure of the central orbit envelope is contained in the adjustable
maximal-parity exceptional set once the two explicit startups hold. -/
theorem shellInitialWindowBad_subset_adjustable
    {lambda t : ℝ} {M : ℕ}
    (hlambda1 : lambda ≤ 1) (ht : 0 ≤ t)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    shellInitialWindowBad M t ⊆
      shellMaximalParityBad M (adjustableBarrierHeight lambda t M) := by
  classical
  intro n hn
  rw [shellInitialWindowBad, Finset.mem_filter] at hn
  rw [shellMaximalParityBad, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  intro hreg
  rcases hn.2 with ⟨k, hkM, hfail⟩
  have henv := orbit_envelope_of_adjustableBarrier hlambda1 ht
    hmainStartup hcorrectionStartup hkM hn.1 hreg
  rcases hfail with hlower | hupper
  · exact (not_lt_of_ge henv.1) hlower
  · exact (not_lt_of_ge henv.2) hupper

/-- Entropy-sharp count for the adjustable maximal-parity exceptional set. -/
theorem card_shellMaximalParityBad_adjustable_le
    {lambda t : ℝ} (M : ℕ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (ht0 : 0 ≤ t) (htA : t < a0) :
    ((shellMaximalParityBad M
      (adjustableBarrierHeight lambda t M)).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) *
          binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have hnonneg := adjustableBarrierDisplacement_nonneg hlambda0 ht0
  have hhalf := adjustableBarrierDisplacement_lt_half hlambda1 ht0 htA
  have hraw := card_shellMaximalParityBad_le_binaryEntropy
    (adjustableBarrierDisplacement lambda t) M hnonneg hhalf
  simpa [adjustableBarrierHeight_eq_displacement_mul] using hraw

/-- The actual orbit-envelope failures obey the entropy-sharp shell count
whenever the two finite-startup inequalities hold. -/
theorem card_shellInitialWindowBad_adjustable_le
    {lambda t : ℝ} {M : ℕ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (ht0 : 0 ≤ t) (htA : t < a0)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    ((shellInitialWindowBad M t).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) *
          binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have hsubset := shellInitialWindowBad_subset_adjustable
    hlambda1 ht0 hmainStartup hcorrectionStartup
  have hcard :
      (shellInitialWindowBad M t).card ≤
        (shellMaximalParityBad M
          (adjustableBarrierHeight lambda t M)).card :=
    Finset.card_le_card hsubset
  have hcardR :
      ((shellInitialWindowBad M t).card : ℝ) ≤
        ((shellMaximalParityBad M
          (adjustableBarrierHeight lambda t M)).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans
    (card_shellMaximalParityBad_adjustable_le M hlambda0 hlambda1 ht0 htA)

/-- Eventual entropy-sharp shell count, with no startup hypotheses left in the
consumer. -/
theorem eventually_card_shellInitialWindowBad_adjustable_le
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ M : ℕ in atTop,
      ((shellInitialWindowBad M t).card : ℝ) ≤
        (2 : ℝ) ^ (M + 1) *
          Real.exp (-((M : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  filter_upwards [eventually_adjustableBarrier_startups
    hlambda1 ht0 htA] with M hstartup
  exact card_shellInitialWindowBad_adjustable_le
    hlambda0 hlambda1.le ht0.le htA hstartup.1 hstartup.2

end

end FirstPassageLinearTransport
