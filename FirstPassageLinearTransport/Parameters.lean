/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import FirstPassageLinearTransport.Pullback

/-!
# Stage parameter construction

The strict paper parameters `a₀ < r < 1` and `0 < eta < r-a₀`
eventually satisfy every scalar hypothesis recorded by `StageSetup`.
-/

namespace FirstPassageLinearTransport

open scoped Real Topology

noncomputable section

theorem central_terminal_identity (eta : ℝ) (M : ℕ) :
    centralOrbitScale M * ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) =
      (2 : ℝ) ^ ((a0 + eta) * M + 1 + eta) := by
  rw [centralOrbitScale_eq_two_rpow_neg_gap,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1
  unfold driftGap
  push_cast
  ring

theorem eventually_horizon_small {r : ℝ} (hr : 0 < r) :
    ∀ᶠ M : ℕ in Filter.atTop,
      (M : ℝ) / (2 * (targetScale r M : ℝ)) ≤ 1 / 3 := by
  let b := r * Real.log 2
  have hb : 0 < b := mul_pos hr (Real.log_pos (by norm_num))
  have htReal :
      Filter.Tendsto
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-b * x))
        Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
  have htNat :
      Filter.Tendsto
        (fun M : ℕ => (M : ℝ) * Real.exp (-b * M))
        Filter.atTop (nhds 0) := by
    simpa [Real.rpow_one] using
      htReal.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ M : ℕ in Filter.atTop,
      (M : ℝ) * Real.exp (-b * M) < 1 / 3 :=
    htNat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  filter_upwards [hevent] with M hM
  have hfloor := targetScale_rpow_neg_le hr.le
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)
    (M := M)
  have hY : (0 : ℝ) < targetScale r M := by
    exact_mod_cast targetScale_pos r M
  have hrewrite :
      (targetScale r M : ℝ) ^ (-(1 : ℝ)) =
        1 / (targetScale r M : ℝ) := by
    rw [Real.rpow_neg_one]
    simp [one_div]
  rw [hrewrite] at hfloor
  have hcalc :
      (M : ℝ) / (2 * (targetScale r M : ℝ)) ≤
        (M : ℝ) * Real.exp (-(b * M)) := by
    calc
      (M : ℝ) / (2 * (targetScale r M : ℝ)) =
          (M : ℝ) / 2 * (1 / (targetScale r M : ℝ)) := by ring
      _ ≤ (M : ℝ) / 2 *
          (2 * Real.exp (-(r * 1 * M * Real.log 2))) :=
        mul_le_mul_of_nonneg_left hfloor (by positivity)
      _ = (M : ℝ) * Real.exp (-(b * M)) := by
        dsimp [b]
        ring_nf
  have hM' : (M : ℝ) * Real.exp (-(b * M)) ≤ 1 / 3 := by
    convert hM.le using 1
    all_goals ring
  exact hcalc.trans hM'

/-- Existence of the exact one-stage parameter package used by the pullback
and bootstrap. -/
theorem exists_stageSetup {r eta : ℝ}
    (ha0r : a0 < r) (hr1 : r < 1)
    (heta0 : 0 < eta) (hetaGap : eta < r - a0) :
    Nonempty (StageSetup r eta) := by
  have hr0 : 0 < r := a0_pos.trans ha0r
  have heta1 : eta ≤ 1 := by linarith [a0_pos]
  let g := r - a0 - eta
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨Mlin : ℕ, hMlin⟩ := exists_nat_gt ((2 + eta) / g)
  obtain ⟨Mone : ℕ, hMone⟩ := exists_nat_gt (2 / r)
  obtain ⟨Mhor : ℕ, hMhor⟩ :=
    (Filter.eventually_atTop.1 (eventually_horizon_small hr0))
  let M0 := max 1 (max Mlin (max Mone Mhor))
  have hM0one : 1 ≤ M0 := le_max_left _ _
  have hM0lin : Mlin ≤ M0 :=
    (le_max_left Mlin (max Mone Mhor)).trans (le_max_right 1 _)
  have hM0oneScale : Mone ≤ M0 :=
    (le_max_left Mone Mhor).trans
      ((le_max_right Mlin _).trans (le_max_right 1 _))
  have hM0hor : Mhor ≤ M0 :=
    (le_max_right Mone Mhor).trans
      ((le_max_right Mlin _).trans (le_max_right 1 _))
  refine ⟨{
    M0 := M0
    r_pos := hr0
    r_lt_one := hr1
    eta_pos := heta0
    eta_le_one := heta1
    target_one_lt := ?_
    target_lt_shell := ?_
    horizon_small := ?_
    terminal_budget := ?_ }⟩
  · intro M hM
    have hMoneLe : Mone ≤ M := hM0oneScale.trans hM
    have hMR : (Mone : ℝ) ≤ M := by exact_mod_cast hMoneLe
    have hlarge : 2 < r * (M : ℝ) := by
      have hbase : 2 / r < Mone := hMone
      have := hbase.trans_le hMR
      rw [div_lt_iff₀ hr0] at hbase
      nlinarith
    have hfloor : r * (M : ℝ) - 1 < (⌊r * (M : ℝ)⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor _
    have hfloorR : (1 : ℝ) < (⌊r * (M : ℝ)⌋₊ : ℝ) := by
      linarith
    have hfloorNat : 1 < ⌊r * (M : ℝ)⌋₊ := by exact_mod_cast hfloorR
    unfold targetScale
    exact Nat.one_lt_pow (by omega) (by omega)
  · intro M hM
    have hMpos : 0 < M := lt_of_lt_of_le (by omega) (hM0one.trans hM)
    have hx0 : 0 ≤ r * (M : ℝ) := by positivity
    have hfloorLe : (⌊r * (M : ℝ)⌋₊ : ℝ) ≤ r * M := Nat.floor_le hx0
    have hlt : (⌊r * (M : ℝ)⌋₊ : ℝ) < M := by
      have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
      nlinarith
    have hfloorNat : ⌊r * (M : ℝ)⌋₊ < M := by exact_mod_cast hlt
    unfold targetScale
    exact Nat.pow_lt_pow_right (by norm_num) hfloorNat
  · intro M hM
    have hreal := hMhor M (hM0hor.trans hM)
    have hcast :
        (((M : ℚ) / (2 * (targetScale r M : ℚ)) : ℚ) : ℝ) ≤
          (((1 / 3 : ℚ) : ℚ) : ℝ) := by
      norm_num
      exact hreal
    exact Rat.cast_le.1 hcast
  · intro M hM
    have hMlinLe : Mlin ≤ M := hM0lin.trans hM
    have hMR : (Mlin : ℝ) ≤ M := by exact_mod_cast hMlinLe
    have hbase : (2 + eta) / g < Mlin := hMlin
    have hgapM : 2 + eta < g * (M : ℝ) := by
      have h := hbase.trans_le hMR
      rw [div_lt_iff₀ hg] at hbase
      nlinarith
    have hfloor : r * (M : ℝ) - 1 < (⌊r * (M : ℝ)⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor _
    have hExp :
        (a0 + eta) * M + 1 + eta ≤ (⌊r * (M : ℝ)⌋₊ : ℝ) := by
      dsimp [g] at hgapM
      linarith
    rw [central_terminal_identity eta M]
    unfold targetScale
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp

end

end FirstPassageLinearTransport
