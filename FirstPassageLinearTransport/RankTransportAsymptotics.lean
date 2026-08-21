/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import FirstPassageLinearTransport.TerminalProfile

/-!
# Rank-transport startup

The exponentially rescaled first-passage distortion is eventually small.
This scalar fact is shared by the canonical timeout proof and retained
historical profiles.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- The rescaled first-passage distortion startup is automatic beyond one
rank depending only on the positive common contraction budget. -/
theorem eventually_rankTransport_small
    {r : ℚ} (hr : 0 < r) :
    ∀ᶠ q : ℕ in atTop,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3 := by
  let rR : ℝ := (r : ℝ)
  have hrR : 0 < rR := by
    dsimp [rR]
    exact_mod_cast hr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htReal :
      Tendsto
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(Real.log 2) * x))
        atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log 2) hlog2
  have htNat :
      Tendsto
        (fun q : ℕ => (q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ)))
        atTop (nhds 0) := by
    simpa [Real.rpow_one] using
      htReal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ q : ℕ in atTop,
      (q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ)) < rR / 9 :=
    htNat.eventually (Iio_mem_nhds (div_pos hrR (by norm_num)))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with q hq hq1
  have hqBound : ((q + 2 : ℕ) : ℝ) ≤ 3 * (q : ℝ) := by
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    push_cast
    nlinarith
  have hreal :
      (((q + 2 : ℕ) : ℝ) / rR) / (2 : ℝ) ^ q ≤ 1 / 3 := by
    rw [show (((q + 2 : ℕ) : ℝ) / rR) / (2 : ℝ) ^ q =
        (((q + 2 : ℕ) : ℝ) / rR) * (1 / (2 : ℝ) ^ q) by ring,
      one_div_two_pow_eq_exp]
    have hscale :
        (((q + 2 : ℕ) : ℝ) / rR) *
            Real.exp (-(Real.log 2 * (q : ℝ))) ≤
          (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) := by
      have hexp0 : 0 ≤ Real.exp (-(Real.log 2 * (q : ℝ))) :=
        (Real.exp_pos _).le
      calc
        (((q + 2 : ℕ) : ℝ) / rR) *
            Real.exp (-(Real.log 2 * (q : ℝ))) ≤
          ((3 * (q : ℝ)) / rR) *
            Real.exp (-(Real.log 2 * (q : ℝ))) :=
              mul_le_mul_of_nonneg_right
                ((div_le_div_iff_of_pos_right hrR).2 hqBound) hexp0
        _ = (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) := by
              ring
    have hfinal :
        (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) < 1 / 3 := by
      calc
        (3 / rR) *
            ((q : ℝ) * Real.exp (-(Real.log 2) * (q : ℝ))) <
          (3 / rR) * (rR / 9) :=
            mul_lt_mul_of_pos_left hq (div_pos (by norm_num) hrR)
        _ = 1 / 3 := by
          field_simp [ne_of_gt hrR]
          norm_num
    exact hscale.trans hfinal.le
  have hcast :
      ((((((q + 2 : ℕ) : ℚ) / r) /
          ((2 ^ q : ℕ) : ℚ) : ℚ) : ℝ)) ≤
        (((1 / 3 : ℚ) : ℝ)) := by
    norm_num at hreal ⊢
    exact hreal
  exact Rat.cast_le.1 hcast

/-- Interval form consumed by finite terminal profiles. -/
theorem eventually_interval_rankTransport_small
    {r : ℚ} (hr : 0 < r) :
    ∀ᶠ L : ℕ in atTop, ∀ U q : ℕ, q ∈ Finset.Icc L U →
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3 := by
  have hbase := eventually_rankTransport_small hr
  rw [eventually_atTop] at hbase ⊢
  obtain ⟨q₀, hq₀⟩ := hbase
  refine ⟨q₀, ?_⟩
  intro L hL U q hq
  exact hq₀ q (hL.trans (Finset.mem_Icc.mp hq).1)

end

end FirstPassageLinearTransport
