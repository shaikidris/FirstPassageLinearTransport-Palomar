/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.Calculus.MeanValue
import FirstPassageLinearTransport.FixedPolylogParameters
import FirstPassageLinearTransport.SharpEntropyBarrier

/-!
# Moving low-rank parameters

This module formalizes the shell-dependent low parameters used at the critical
polylogarithmic endpoint.  It records the exact passage margin and the uniform
affine-correction margin before any Collatz-set counting is attempted.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Low-envelope tolerance at terminal rank `L`. -/
def movingLowTolerance (K₀ : ℝ) (L : ℕ) : ℝ :=
  driftGap - K₀ / (L : ℝ)

/-- Low threshold ratio at terminal rank `L`. -/
def movingLowRatio (K₀ : ℝ) (L : ℕ) : ℝ :=
  1 - K₀ / (2 * (L : ℝ))

/-- Fraction of the moving tolerance spent on the Boolean barrier. -/
def movingLowLambda (K₁ : ℝ) (L : ℕ) : ℝ :=
  1 - K₁ / (L : ℝ)

/-- The binary barrier rate is Lipschitz on the compact interval joining half
the endpoint displacement to the endpoint itself.  No numerical derivative
bound is needed; compactness supplies one fixed constant. -/
theorem exists_binaryBarrierRate_endpoint_lipschitz :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement,
        ∀ y ∈ Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement,
          ‖binaryBarrierRate y - binaryBarrierRate x‖ ≤ C * ‖y - x‖ := by
  let pLo := 1 / 2 + firstPassageEndpointDisplacement / 2
  let pHi := 1 / 2 + firstPassageEndpointDisplacement
  let derivWeight : ℝ → ℝ := fun p => ‖Real.log (1 - p) - Real.log p‖
  have hpLo0 : 0 < pLo := by
    dsimp [pLo]
    linarith [firstPassageEndpointDisplacement_pos]
  have hpHi1 : pHi < 1 := by
    dsimp [pHi]
    linarith [firstPassageEndpointDisplacement_lt_half]
  have hcont : ContinuousOn derivWeight (Set.Icc pLo pHi) := by
    intro p hp
    have hp0 : p ≠ 0 := by linarith [hp.1, hpLo0]
    have hp1 : 1 - p ≠ 0 := by linarith [hp.2, hpHi1]
    dsimp [derivWeight]
    have honeSub : ContinuousAt (fun z : ℝ => 1 - z) p :=
      continuousAt_const.sub continuousAt_id
    have hlogOne : ContinuousAt (fun z : ℝ => Real.log (1 - z)) p :=
      by simpa [Function.comp_def] using
        (Real.continuousAt_log hp1).comp honeSub
    have hlog : ContinuousAt (fun z : ℝ => Real.log z) p :=
      Real.continuousAt_log hp0
    exact (hlogOne.sub hlog).norm.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.bddAbove_image hcont
  let C := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hxp : 1 / 2 + x ∈ Set.Icc pLo pHi := by
    dsimp [pLo, pHi]
    constructor <;> linarith [hx.1, hx.2]
  have hyp : 1 / 2 + y ∈ Set.Icc pLo pHi := by
    dsimp [pLo, pHi]
    constructor <;> linarith [hy.1, hy.2]
  have hdiff : ∀ p ∈ Set.Icc pLo pHi,
      DifferentiableAt ℝ Real.binEntropy p := by
    intro p hp
    apply Real.differentiableAt_binEntropy
    · linarith [hp.1, hpLo0]
    · linarith [hp.2, hpHi1]
  have hbound : ∀ p ∈ Set.Icc pLo pHi,
      ‖deriv Real.binEntropy p‖ ≤ C := by
    intro p hp
    have himage : derivWeight p ∈
        derivWeight '' Set.Icc pLo pHi := ⟨p, hp, rfl⟩
    have hpBound : derivWeight p ≤ C₀ := hC₀ himage
    rw [Real.deriv_binEntropy]
    exact hpBound.trans (le_max_left _ _)
  have hmean := (convex_Icc pLo pHi).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound hxp hyp
  unfold binaryBarrierRate
  calc
    ‖(Real.log 2 - Real.binEntropy (1 / 2 + y)) -
        (Real.log 2 - Real.binEntropy (1 / 2 + x))‖ =
      ‖Real.binEntropy (1 / 2 + y) - Real.binEntropy (1 / 2 + x)‖ := by
        rw [show
          (Real.log 2 - Real.binEntropy (1 / 2 + y)) -
              (Real.log 2 - Real.binEntropy (1 / 2 + x)) =
            -(Real.binEntropy (1 / 2 + y) -
              Real.binEntropy (1 / 2 + x)) by ring,
          norm_neg]
    _ ≤ C * ‖(1 / 2 + y) - (1 / 2 + x)‖ := hmean
    _ = C * ‖y - x‖ := by congr 2 <;> ring

private theorem tendsto_const_div_natCast_zero (K : ℝ) :
    Tendsto (fun L : ℕ => K / (L : ℝ)) atTop (nhds 0) := by
  have hcast : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun L : ℕ => K * ((L : ℝ))⁻¹) atTop (nhds (K * 0)))

theorem tendsto_movingLowTolerance (K₀ : ℝ) :
    Tendsto (movingLowTolerance K₀) atTop (nhds driftGap) := by
  change Tendsto (fun L : ℕ => driftGap - K₀ / (L : ℝ))
    atTop (nhds driftGap)
  simpa [movingLowTolerance] using
    (tendsto_const_nhds.sub (tendsto_const_div_natCast_zero K₀) :
      Tendsto (fun L : ℕ => driftGap - K₀ / (L : ℝ))
        atTop (nhds (driftGap - 0)))

theorem tendsto_movingLowRatio (K₀ : ℝ) :
    Tendsto (movingLowRatio K₀) atTop (nhds 1) := by
  change Tendsto (fun L : ℕ => 1 - K₀ / (2 * (L : ℝ)))
    atTop (nhds 1)
  have hzero := tendsto_const_div_natCast_zero (K₀ / 2)
  simpa [movingLowRatio, div_div] using
    (tendsto_const_nhds.sub hzero :
      Tendsto (fun L : ℕ => 1 - (K₀ / 2) / (L : ℝ))
        atTop (nhds (1 - 0)))

theorem tendsto_movingLowLambda (K₁ : ℝ) :
    Tendsto (movingLowLambda K₁) atTop (nhds 1) := by
  change Tendsto (fun L : ℕ => 1 - K₁ / (L : ℝ)) atTop (nhds 1)
  simpa [movingLowLambda] using
    (tendsto_const_nhds.sub (tendsto_const_div_natCast_zero K₁) :
      Tendsto (fun L : ℕ => 1 - K₁ / (L : ℝ)) atTop (nhds (1 - 0)))

/-- The additive-correction exponent has the strictly positive endpoint
limit `2*a₀-1`. -/
theorem tendsto_movingLowCorrectionGap (K₀ K₁ : ℝ) :
    Tendsto
      (fun L : ℕ =>
        a0 + movingLowTolerance K₀ L -
          2 * movingLowLambda K₁ L * movingLowTolerance K₀ L)
      atTop (nhds (2 * a0 - 1)) := by
  have htol := tendsto_movingLowTolerance K₀
  have hlam := tendsto_movingLowLambda K₁
  have hprod := hlam.mul htol
  have ha0 : Tendsto (fun _ : ℕ => a0) atTop (nhds a0) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hlim := (ha0.add htol).sub (htwo.mul hprod)
  have hlimitEq :
      a0 + driftGap - 2 * (1 * driftGap) = 2 * a0 - 1 := by
    unfold driftGap
    ring
  rw [hlimitEq] at hlim
  simpa [mul_assoc] using hlim

theorem two_mul_a0_sub_one_pos : 0 < 2 * a0 - 1 := by
  unfold a0
  linarith [logTwoThree_one_lt]

/-- A convenient rational separation from the central quarter-window.  This
is proved from `8 < 9`, so the later lattice argument does not depend on a
decimal approximation to `log₂ 3`. -/
theorem three_halves_lt_logTwoThree : (3 / 2 : ℝ) < logTwoThree := by
  have hlog : Real.log (8 : ℝ) < Real.log (9 : ℝ) :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hlog8, hlog9] at hlog
  unfold logTwoThree
  exact (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 (by
    linarith)

/-- The endpoint Boolean displacement lies strictly inside the central
quarter-window used by the sharp Stirling estimate. -/
theorem firstPassageEndpointDisplacement_lt_quarter :
    firstPassageEndpointDisplacement < 1 / 4 := by
  have ha0 : (3 / 4 : ℝ) < a0 := by
    unfold a0
    linarith [three_halves_lt_logTwoThree]
  have hgap : driftGap < 1 / 4 := by
    unfold driftGap
    linarith
  unfold firstPassageEndpointDisplacement
  have hlogOne : 1 < logTwoThree := logTwoThree_one_lt
  calc
    driftGap / logTwoThree < driftGap :=
      (div_lt_self driftGap_pos hlogOne)
    _ < 1 / 4 := hgap

/-- After one finite startup, all three moving low parameters lie in their
required open ranges and the affine-correction exponent is positive. -/
theorem eventually_movingLow_admissible
    {K₀ K₁ : ℝ} (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) :
    ∀ᶠ L : ℕ in atTop,
      0 < movingLowTolerance K₀ L ∧
      movingLowTolerance K₀ L < driftGap ∧
      0 < movingLowRatio K₀ L ∧ movingLowRatio K₀ L < 1 ∧
      0 < movingLowLambda K₁ L ∧ movingLowLambda K₁ L < 1 ∧
      0 < a0 + movingLowTolerance K₀ L -
        2 * movingLowLambda K₁ L * movingLowTolerance K₀ L := by
  have htolPos := (tendsto_movingLowTolerance K₀).eventually
    (Ioi_mem_nhds driftGap_pos)
  have hratioPos := (tendsto_movingLowRatio K₀).eventually
    (Ioi_mem_nhds zero_lt_one)
  have hlamPos := (tendsto_movingLowLambda K₁).eventually
    (Ioi_mem_nhds zero_lt_one)
  have hcorrPos := (tendsto_movingLowCorrectionGap K₀ K₁).eventually
    (Ioi_mem_nhds two_mul_a0_sub_one_pos)
  filter_upwards [htolPos, hratioPos, hlamPos, hcorrPos,
      eventually_ge_atTop (1 : ℕ)] with L htol hratio hlam hcorr hL
  have hLR : 0 < (L : ℝ) := by positivity
  have htolLt : movingLowTolerance K₀ L < driftGap := by
    unfold movingLowTolerance
    have : 0 < K₀ / (L : ℝ) := div_pos hK₀ hLR
    linarith
  have hratioLt : movingLowRatio K₀ L < 1 := by
    unfold movingLowRatio
    have : 0 < K₀ / (2 * (L : ℝ)) := div_pos hK₀ (by positivity)
    linarith
  have hlamLt : movingLowLambda K₁ L < 1 := by
    unfold movingLowLambda
    have : 0 < K₁ / (L : ℝ) := div_pos hK₁ hLR
    linarith
  exact ⟨htol, htolLt, hratio, hratioLt, hlam, hlamLt, hcorr⟩

end

end FirstPassageLinearTransport
