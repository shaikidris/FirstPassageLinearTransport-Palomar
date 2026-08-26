/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import FirstPassageLinearTransport.TerminalTail

/-!
# Sharp square-root terminal tails

The critical moving producer supplies a density of shape

```text
d_q ≪ 2^{-q} + q^{-1/2} exp(-b (q-1)).
```

Multiplying by the reverse-loss factor `(q+1)` and summing over
`q ∈ [L, S]` retains the original exponential rate:

```text
O((L+1) 2^{-L} + √L exp(-b (L-1))).
```

The constant is uniform for `b` bounded below by one fixed positive rate.
No replacement `b ↦ b' < b` is made.  After the `O(√(M log M))`
time-support factor this is the endpoint-sensitive input for the critical
buffer

```text
Δ_M = κ_* L - ½ log₂ M - log₂ log M.
```

The coarser `terminalTailBound` route replaces `q^{-1/2}` by `1` and therefore
spends an extra polynomial rank factor.  This module exposes only the
exact-rate endpoint-sensitive consumer.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped BigOperators Real Topology

noncomputable section

/-- Shifted linear exponential tails retain the original rate.  The rate
`c₀` is used only to control the translated geometric series; the leading
factor keeps the actual rate `c`. -/
theorem shifted_linear_exp_Icc_le
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc₀c : c₀ ≤ c)
    {L U : ℕ} (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ))) *
        weightedTailConstant c₀ (c₀ / 2) := by
  have hc₀half : 0 < c₀ / 2 := by positivity
  have hhalf : c₀ / 2 < c₀ := by linarith
  let pref : ℝ :=
    ((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ)))
  have hterm : ∀ q ∈ Finset.Icc L U,
      ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
        pref * (((q - L + 1 : ℕ) : ℝ) *
          Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by
    intro q hq
    have hLq : L ≤ q := (Finset.mem_Icc.mp hq).1
    have hqSplit : q = L + (q - L) := by omega
    have hlinNat : q + 1 ≤ (L + 1) * (q - L + 1) := by
      rw [hqSplit]
      simp only [Nat.add_sub_cancel_left]
      nlinarith [Nat.zero_le (L * (q - L))]
    have hlin : ((q + 1 : ℕ) : ℝ) ≤
        ((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ) := by
      exact_mod_cast hlinNat
    have hexpSplit :
        Real.exp (-(c * (q : ℝ))) =
          Real.exp (-(c * (L : ℝ))) *
            Real.exp (-(c * ((q - L : ℕ) : ℝ))) := by
      have hqCast : (q : ℝ) = (L : ℝ) + ((q - L : ℕ) : ℝ) := by
        exact_mod_cast hqSplit
      rw [hqCast]
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpMono :
        Real.exp (-(c * ((q - L : ℕ) : ℝ))) ≤
          Real.exp (-(c₀ * ((q - L : ℕ) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hj0 : (0 : ℝ) ≤ (q - L : ℕ) := by positivity
      nlinarith
    rw [hexpSplit]
    dsimp [pref]
    calc
      ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(c * (L : ℝ))) *
            Real.exp (-(c * ((q - L : ℕ) : ℝ)))) ≤
        (((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ)) *
          (Real.exp (-(c * (L : ℝ))) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by
          gcongr
      _ = (((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by ring
  have hshift :
      ∑ q ∈ Finset.Icc L U,
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) =
        ∑ j ∈ Finset.Icc 0 (U - L),
          ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ))) := by
    have hfin : Finset.range (U + 1 - L) = Finset.Icc 0 (U - L) := by
      ext j
      simp
      omega
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    change
      (∑ j ∈ Finset.range (U + 1 - L),
        ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ)))) = _
    rw [hfin]
  have htail := weighted_exp_Icc_le hc₀half hhalf 0 (U - L)
  have hpref0 : 0 ≤ pref := by
    dsimp [pref]
    positivity
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      ∑ q ∈ Finset.Icc L U,
        pref * (((q - L + 1 : ℕ) : ℝ) *
          Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) :=
        Finset.sum_le_sum hterm
    _ = pref *
        ∑ q ∈ Finset.Icc L U,
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c₀ * ((q - L : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ = pref *
        ∑ j ∈ Finset.Icc 0 (U - L),
          ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ))) := by
      rw [hshift]
    _ ≤ pref * weightedTailConstant c₀ (c₀ / 2) := by
      have htail' :
          ∑ j ∈ Finset.Icc 0 (U - L),
              ((j + 1 : ℕ) : ℝ) * Real.exp (-(c₀ * (j : ℝ))) ≤
            weightedTailConstant c₀ (c₀ / 2) := by
        simpa using htail
      exact mul_le_mul_of_nonneg_left htail' hpref0
    _ = ((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ))) *
        weightedTailConstant c₀ (c₀ / 2) := rfl

/-- After the translation `q = L + j`, the offset-weighted exponential tail
is uniformly bounded.  As in `shifted_linear_exp_Icc_le`, `c₀` controls
only the translated tail; no loss is made in the actual rate `c`. -/
theorem offset_exp_Icc_le
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc₀c : c₀ ≤ c)
    {L U : ℕ} (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q - L + 1 : ℕ) : ℝ) *
          Real.exp (-(c * ((q - L : ℕ) : ℝ))) ≤
      weightedTailConstant c₀ (c₀ / 2) := by
  have hshift :
      ∑ q ∈ Finset.Icc L U,
          ((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(c * ((q - L : ℕ) : ℝ))) =
        ∑ j ∈ Finset.Icc 0 (U - L),
          ((j + 1 : ℕ) : ℝ) * Real.exp (-(c * (j : ℝ))) := by
    have hfin : Finset.range (U + 1 - L) = Finset.Icc 0 (U - L) := by
      ext j
      simp
      omega
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    change
      (∑ j ∈ Finset.range (U + 1 - L),
        ((j + 1 : ℕ) : ℝ) * Real.exp (-(c * (j : ℝ)))) = _
    rw [hfin]
  rw [hshift]
  have htail := shifted_linear_exp_Icc_le hc₀ hc₀c
    (L := 0) (U := U - L) (Nat.zero_le _)
  simpa using htail

/-- The rank factor produced by reverse loss retains only a square-root
terminal prefactor after translation to `j = q-L`. -/
theorem rank_over_sqrt_shift_le
    {L q : ℕ} (hL : 2 ≤ L) (hLq : L ≤ q) :
    ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) ≤
      3 * Real.sqrt L * ((q - L + 1 : ℕ) : ℝ) := by
  have hLm1posNat : 0 < L - 1 := by omega
  have hqm1posNat : 0 < q - 1 := by omega
  have hsL0 : 0 ≤ Real.sqrt (L : ℝ) := Real.sqrt_nonneg _
  have hsLm10 : 0 ≤ Real.sqrt ((L - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsLm1pos : 0 < Real.sqrt ((L - 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hLm1posNat)
  have hsQm1pos : 0 < Real.sqrt ((q - 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hqm1posNat)
  have hsDen : Real.sqrt ((L - 1 : ℕ) : ℝ) ≤
      Real.sqrt ((q - 1 : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le_sub_right hLq 1
  have hqSplit : q = L + (q - L) := by omega
  have hlinNat : q + 1 ≤ (L + 1) * (q - L + 1) := by
    rw [hqSplit]
    simp only [Nat.add_sub_cancel_left]
    nlinarith [Nat.zero_le (L * (q - L))]
  have hlin : ((q + 1 : ℕ) : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlinNat
  have hbase : ((L + 1 : ℕ) : ℝ) /
      Real.sqrt ((L - 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt L := by
    apply (div_le_iff₀ hsLm1pos).2
    have hsLm1sq := Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ ((L - 1 : ℕ) : ℝ))
    have hlinL : ((L + 1 : ℕ) : ℝ) ≤
        3 * ((L - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show L + 1 ≤ 3 * (L - 1) by omega)
    have hsLm1L : Real.sqrt ((L - 1 : ℕ) : ℝ) ≤ Real.sqrt L := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Nat.sub_le L 1)
    calc
      ((L + 1 : ℕ) : ℝ) ≤ 3 * ((L - 1 : ℕ) : ℝ) := hlinL
      _ = 3 * (Real.sqrt ((L - 1 : ℕ) : ℝ)) ^ 2 := by
        congr 1
        exact hsLm1sq.symm
      _ = 3 * Real.sqrt ((L - 1 : ℕ) : ℝ) *
          Real.sqrt ((L - 1 : ℕ) : ℝ) := by ring
      _ ≤ 3 * Real.sqrt L * Real.sqrt ((L - 1 : ℕ) : ℝ) := by
        gcongr
  have hrecip : 1 / Real.sqrt ((q - 1 : ℕ) : ℝ) ≤
      1 / Real.sqrt ((L - 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hsLm1pos hsDen
  calc
    ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) =
        ((q + 1 : ℕ) : ℝ) *
          (1 / Real.sqrt ((q - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (((L + 1 : ℕ) : ℝ) * ((q - L + 1 : ℕ) : ℝ)) *
          (1 / Real.sqrt ((L - 1 : ℕ) : ℝ)) := by
      gcongr
    _ = (((L + 1 : ℕ) : ℝ) /
          Real.sqrt ((L - 1 : ℕ) : ℝ)) *
        ((q - L + 1 : ℕ) : ℝ) := by ring
    _ ≤ 3 * Real.sqrt L * ((q - L + 1 : ℕ) : ℝ) := by
      gcongr

/-- Exact-rate entropy tail.  The terminal factor retains the actual rate
`b`; the lower rate `b₀` is used only in the translated geometric series. -/
theorem sharp_entropy_tail_exact_rate_Icc_le
    {b₀ b : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
      3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
        weightedTailConstant b₀ (b₀ / 2) := by
  have hterm : ∀ q ∈ Finset.Icc L U,
      ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
        (3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by
    intro q hq
    have hLq : L ≤ q := (Finset.mem_Icc.mp hq).1
    have hq1 : 1 ≤ q := le_trans (by norm_num) (hL.trans hLq)
    have hL1 : 1 ≤ L := le_trans (by norm_num) hL
    have hexpSplit :
        Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) =
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ))) := by
      rw [Nat.cast_sub hq1, Nat.cast_sub hL1]
      have hcastSub : ((q - L : ℕ) : ℝ) = (q : ℝ) - (L : ℝ) := by
        rw [Nat.cast_sub hLq]
      rw [hcastSub, ← Real.exp_add]
      congr 1
      ring
    rw [hexpSplit]
    have hrank := rank_over_sqrt_shift_le hL hLq
    calc
      ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          (Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) ≤
        (3 * Real.sqrt L * ((q - L + 1 : ℕ) : ℝ)) *
          (Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by
          gcongr
      _ = (3 * Real.sqrt L *
            Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by ring
  have hcoef0 : 0 ≤
      3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    positivity
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
      ∑ q ∈ Finset.Icc L U,
        (3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) :=
        Finset.sum_le_sum hterm
    _ = (3 * Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
        ∑ q ∈ Finset.Icc L U,
          (((q - L + 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - L : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ (3 * Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) *
        weightedTailConstant b₀ (b₀ / 2) := by
      exact mul_le_mul_of_nonneg_left
        (offset_exp_Icc_le hb₀ hb₀b hLU) hcoef0

/-- Combined dyadic and entropy tails at their exact leading rates. -/
theorem exact_sharp_critical_low_series_Icc_le
    {b₀ b Cpref : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    (hCpref : 0 ≤ Cpref) {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
      weightedTailConstant (Real.log 2) (Real.log 2 / 2) *
          ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
        3 * Cpref * weightedTailConstant b₀ (b₀ / 2) *
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
  have hsplit :
      ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
                Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) =
        ∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (q : ℝ))) +
          Cpref * ∑ q ∈ Finset.Icc L U,
            ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hsplit]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdy := shifted_linear_exp_Icc_le hlog2 le_rfl hLU
  have hent := sharp_entropy_tail_exact_rate_Icc_le hb₀ hb₀b hL hLU
  calc
    ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (q : ℝ))) +
        Cpref * ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
      (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) *
          weightedTailConstant (Real.log 2) (Real.log 2 / 2)) +
        Cpref * (3 * Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
            weightedTailConstant b₀ (b₀ / 2)) := by
        exact add_le_add hdy (mul_le_mul_of_nonneg_left hent hCpref)
    _ = weightedTailConstant (Real.log 2) (Real.log 2 / 2) *
          ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
        3 * Cpref * weightedTailConstant b₀ (b₀ / 2) *
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by ring

/-- Canonical uniform constant for the exact-rate critical tail. -/
def exactSharpCriticalLowSeriesConstant (b₀ Cpref : ℝ) : ℝ :=
  max
    (weightedTailConstant (Real.log 2) (Real.log 2 / 2))
    (3 * Cpref * weightedTailConstant b₀ (b₀ / 2)) + 1

/-- Uniform exact-rate critical-tail estimate for the canonical constant.
The terminal exponential retains every actual `b ≥ b₀`. -/
theorem exactSharpCriticalLowSeriesConstant_spec
    {b₀ Cpref : ℝ} (hb₀ : 0 < b₀) (hCpref : 0 ≤ Cpref) :
    0 < exactSharpCriticalLowSeriesConstant b₀ Cpref ∧
      ∀ {b : ℝ}, b₀ ≤ b → ∀ {L U : ℕ},
      2 ≤ L → L ≤ U →
      ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
                Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
        exactSharpCriticalLowSeriesConstant b₀ Cpref *
          (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
  let Kdy := weightedTailConstant (Real.log 2) (Real.log 2 / 2)
  let Kent := 3 * Cpref * weightedTailConstant b₀ (b₀ / 2)
  have hKdy0 : 0 ≤ Kdy := by
    dsimp [Kdy, weightedTailConstant]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hgap : 0 < Real.log 2 - Real.log 2 / 2 := by linarith
    have hden : 0 < 1 - Real.exp (-(Real.log 2 / 2)) := by
      have : Real.exp (-(Real.log 2 / 2)) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    exact div_nonneg (by positivity) hden.le
  have hKent0 : 0 ≤ Kent := by
    dsimp [Kent, weightedTailConstant]
    have hgap : 0 < b₀ - b₀ / 2 := by linarith
    have hden : 0 < 1 - Real.exp (-(b₀ / 2)) := by
      have : Real.exp (-(b₀ / 2)) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hCpref)
      (div_nonneg (by positivity) hden.le)
  let K := exactSharpCriticalLowSeriesConstant b₀ Cpref
  have hK : 0 < K := by
    dsimp [K, exactSharpCriticalLowSeriesConstant, Kdy, Kent]
    exact add_pos_of_nonneg_of_pos
      (le_max_of_le_left hKdy0) zero_lt_one
  refine ⟨hK, ?_⟩
  intro b hb₀b L U hL hLU
  have htail := exact_sharp_critical_low_series_Icc_le
    hb₀ hb₀b hCpref hL hLU
  have hdyK : Kdy ≤ K := by
    dsimp [K, exactSharpCriticalLowSeriesConstant, Kdy, Kent]
    exact (le_max_left Kdy Kent).trans (by linarith)
  have hentK : Kent ≤ K := by
    dsimp [K, exactSharpCriticalLowSeriesConstant, Kdy, Kent]
    exact (le_max_right Kdy Kent).trans (by linarith)
  have hbase0 : 0 ≤
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) := by
    positivity
  have hentbase0 : 0 ≤
      Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    positivity
  calc
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
      Kdy * (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ)))) +
        Kent * (Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
        simpa [Kdy, Kent, mul_assoc] using htail
    _ ≤ K * (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ)))) +
        K * (Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hdyK hbase0)
        (mul_le_mul_of_nonneg_right hentK hentbase0)
    _ = K * (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by ring

end

end FirstPassageLinearTransport
