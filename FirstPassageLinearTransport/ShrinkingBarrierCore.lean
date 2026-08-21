/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Parameters
import FirstPassageLinearTransport.TimeSupportTransport

/-!
# Deterministic core of the shrinking-barrier schedule

This module contains the three exact facts on which feasible-time compression
rests: a fixed stage package may be restricted to a smaller tolerance, powers
of two are not certified, and a certified first-passage block has a narrow
duration corridor.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- Reuse the startup data of a stage package at a smaller positive envelope
tolerance.  Only the terminal upper-envelope budget changes, and monotonicity
of real powers supplies it. -/
def StageSetup.lowerTolerance
    {r eta : ℝ} (p : StageSetup r eta) (t : ℝ)
    (ht0 : 0 < t) (hteta : t ≤ eta) : StageSetup r t where
  M0 := p.M0
  r_pos := p.r_pos
  r_lt_one := p.r_lt_one
  eta_pos := ht0
  eta_le_one := hteta.trans p.eta_le_one
  target_one_lt := p.target_one_lt
  target_lt_shell := p.target_lt_shell
  horizon_small := p.horizon_small
  terminal_budget := by
    intro M hM
    have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ (M + 1) :=
      one_le_pow₀ (by norm_num)
    have hpow :
        ((2 : ℝ) ^ (M + 1)) ^ (1 + t) ≤
          ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    exact (mul_le_mul_of_nonneg_left hpow (centralOrbitScale_pos M).le).trans
      (p.terminal_budget M hM)

@[simp] theorem StageSetup.lowerTolerance_M0
    {r eta : ℝ} (p : StageSetup r eta) (t : ℝ)
    (ht0 : 0 < t) (hteta : t ≤ eta) :
    (p.lowerTolerance t ht0 hteta).M0 = p.M0 := rfl

/-- Every usable stage package starts at a positive shell rank. -/
theorem StageSetup.M0_pos {r eta : ℝ} (p : StageSetup r eta) :
    1 ≤ p.M0 := by
  by_contra h
  have hzero : p.M0 = 0 := by omega
  have ht := p.target_one_lt p.M0 le_rfl
  rw [hzero] at ht
  norm_num [targetScale] at ht

/-- Shortcut iteration removes exactly one factor of two per step. -/
theorem orbit_two_pow (q : ℕ) : orbit q (2 ^ q) = 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show q + 1 = q + 1 by rfl, orbit_add]
      have heven : (2 ^ (q + 1)) % 2 = 0 := by
        rw [pow_succ]
        omega
      have hstep : orbit 1 (2 ^ (q + 1)) = 2 ^ q := by
        rw [show (1 : ℕ) = 0 + 1 by omega, orbit_succ, orbit_zero,
          shortcut_of_even heven, pow_succ]
        omega
      rw [hstep, ih]

/-- The central scale at a power-of-two source is the exact exponent used in
the power-of-two exclusion argument. -/
theorem centralScale_mul_twoPow_eq
    (q : ℕ) (t : ℝ) :
    centralOrbitScale q * (((2 ^ q : ℕ) : ℝ) ^ (1 - t)) =
      (2 : ℝ) ^ ((a0 - t) * (q : ℝ)) := by
  rw [centralOrbitScale_eq_two_rpow_neg_gap, Nat.cast_pow,
    show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  unfold driftGap
  congr 1
  ring

/-- A positive power of two violates the lower central envelope at its own
halving time. -/
theorem two_pow_not_mem_initialWindowGood
    {q : ℕ} (hq : 1 ≤ q) {t : ℝ} (htA : t < a0) :
    2 ^ q ∉ initialWindowGood t := by
  intro hgood
  have hlog : Nat.log 2 (2 ^ q) = q := Nat.log_pow (by norm_num) q
  have henv := hgood q (by simp [hlog])
  have hlower :
      centralOrbitScale q * (((2 ^ q : ℕ) : ℝ) ^ (1 - t)) ≤ 1 := by
    simpa [orbit_two_pow] using henv.1
  rw [centralScale_mul_twoPow_eq] at hlower
  have hexp : 0 < (a0 - t) * (q : ℝ) := by
    exact mul_pos (sub_pos.mpr htA) (by exact_mod_cast hq)
  exact (not_lt_of_ge hlower) (Real.one_lt_rpow (by norm_num) hexp)

/-- A certified point in the first-passage band is in the lower ordinary
dyadic shell, never at the upper power-of-two endpoint. -/
theorem certified_landing_mem_lower_shell
    {q y : ℕ} (hq : 1 ≤ q) {t : ℝ} (htA : t < a0)
    (hband : 2 ^ (q - 1) < y ∧ y ≤ 2 ^ q)
    (hgood : y ∈ initialWindowGood t) :
    y ∈ dyadicShell (q - 1) := by
  rw [mem_dyadicShell]
  refine ⟨hband.1.le, ?_⟩
  have hne : y ≠ 2 ^ q := by
    intro hy
    subst y
    exact two_pow_not_mem_initialWindowGood hq htA hgood
  have hylt : y < 2 ^ q := lt_of_le_of_ne hband.2 hne
  simpa [Nat.sub_add_cancel hq] using hylt

/-- Linear form of the paper's one-block duration corridor.  Division by
`driftGap` is intentionally postponed; this form is more convenient for
integer time supports. -/
theorem certified_firstPassage_duration_corridor
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    (1 - t) * (m : ℝ) - (q : ℝ) ≤ driftGap * (h : ℝ) ∧
      driftGap * (h : ℝ) <
        (1 + t) * ((m : ℝ) + 1) - (q : ℝ) + 1 := by
  have hlog := log_two_eq_of_mem_dyadicShell hxShell
  have henv := hxGood h (by simpa [hlog] using hhm)
  have hband := firstPassage_band hh hfp
  have hxLowerNat := (mem_dyadicShell.mp hxShell).1
  have hxUpperNat := (mem_dyadicShell.mp hxShell).2
  have hxLower : (2 : ℝ) ^ m ≤ (x : ℝ) := by exact_mod_cast hxLowerNat
  have hxUpper : (x : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
    exact_mod_cast hxUpperNat.le
  have hexpLower : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hexpUpper : 0 ≤ 1 + t := by linarith
  have hsourceLower :
      ((2 : ℝ) ^ m) ^ (1 - t) ≤ (x : ℝ) ^ (1 - t) :=
    Real.rpow_le_rpow (by positivity) hxLower hexpLower
  have hsourceUpper :
      (x : ℝ) ^ (1 + t) ≤ ((2 : ℝ) ^ (m + 1)) ^ (1 + t) :=
    Real.rpow_le_rpow (by positivity) hxUpper hexpUpper
  have hlandingUpper : (orbit h x : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hfp.1
  have hlandingLower : (2 : ℝ) ^ ((q : ℝ) - 1) < (orbit h x : ℝ) := by
    have hcast : (2 : ℝ) ^ q < 2 * (orbit h x : ℝ) := by
      exact_mod_cast hband.1
    have hcast' : (2 : ℝ) ^ (q : ℝ) < 2 * (orbit h x : ℝ) := by
      simpa [Real.rpow_natCast] using hcast
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    nlinarith [hcast']
  have hpowLower :
      (2 : ℝ) ^ (-driftGap * (h : ℝ) + (m : ℝ) * (1 - t)) ≤
        (2 : ℝ) ^ (q : ℝ) := by
    calc
      (2 : ℝ) ^ (-driftGap * (h : ℝ) + (m : ℝ) * (1 - t)) =
          centralOrbitScale h * (((2 : ℝ) ^ m) ^ (1 - t)) := by
        rw [centralOrbitScale_eq_two_rpow_neg_gap,
          ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      _ ≤ centralOrbitScale h * (x : ℝ) ^ (1 - t) :=
        mul_le_mul_of_nonneg_left hsourceLower (centralOrbitScale_pos h).le
      _ ≤ (orbit h x : ℝ) := henv.1
      _ ≤ (2 : ℝ) ^ q := hlandingUpper
      _ = (2 : ℝ) ^ (q : ℝ) := by rw [Real.rpow_natCast]
  have hpowUpper :
      (2 : ℝ) ^ ((q : ℝ) - 1) <
        (2 : ℝ) ^ (-driftGap * (h : ℝ) +
          ((m : ℝ) + 1) * (1 + t)) := by
    calc
      (2 : ℝ) ^ (q - 1 : ℝ) < (orbit h x : ℝ) := hlandingLower
      _ ≤ centralOrbitScale h * (x : ℝ) ^ (1 + t) := henv.2
      _ ≤ centralOrbitScale h * (((2 : ℝ) ^ (m + 1)) ^ (1 + t)) :=
        mul_le_mul_of_nonneg_left hsourceUpper (centralOrbitScale_pos h).le
      _ = (2 : ℝ) ^ (-driftGap * (h : ℝ) +
          ((m : ℝ) + 1) * (1 + t)) := by
        rw [centralOrbitScale_eq_two_rpow_neg_gap,
          ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        norm_num
  have hmono := Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)
  have hlowerExp :
      -driftGap * (h : ℝ) + (m : ℝ) * (1 - t) ≤ (q : ℝ) :=
    hmono.le_iff_le.mp hpowLower
  have hupperExp :
      (q : ℝ) - 1 < -driftGap * (h : ℝ) +
        ((m : ℝ) + 1) * (1 + t) :=
    hmono.lt_iff_lt.mp hpowUpper
  constructor <;> nlinarith


end

end FirstPassageLinearTransport
