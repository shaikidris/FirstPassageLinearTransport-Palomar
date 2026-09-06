/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.RawDynamics
import FirstPassageLinearTransport.ClockBudget

/-!
# Raw Collatz clock budget

The two-sided orbit envelope itself controls the number of odd shortcut
states.  Combined with the exact raw/shortcut identity, this yields the
asymptotic factor `3/2` without an independence assumption.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- The upper orbit envelope bounds the odd-count excess of every retained
shortcut prefix. -/
theorem oddCount_upper_of_initialWindowGood
    {eta : ℝ} {n k : ℕ}
    (hn : 0 < n) (hnGood : n ∈ initialWindowGood eta)
    (hk : k ≤ Nat.log 2 n) :
    (oddCount n k : ℝ) ≤
      (k : ℝ) / 2 + eta * Real.log n / Real.log 3 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper := (hnGood k hk).2
  have hmain :
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k ≤
        (orbit k n : ℝ) := by
    rw [orbit_eq_normalizedCorrection]
    have hcorr := normalizedCorrection_nonneg k n
    have hthree : 0 ≤ (3 : ℝ) ^ oddCount n k := by positivity
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hcorr) hthree
  have hLU := hmain.trans hupper
  have hleftPos :
      0 < (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k := by
    positivity
  have hlogs := Real.log_le_log hleftPos hLU
  rw [Real.log_mul (div_ne_zero hnR.ne' (by positivity)) (by positivity),
    Real.log_div hnR.ne' (by positivity), Real.log_pow,
    Real.log_pow, centralOrbitScale_eq_two_rpow_neg_gap,
    Real.log_mul (Real.rpow_pos_of_pos (by norm_num) _).ne'
      (Real.rpow_pos_of_pos hnR _).ne',
    Real.log_rpow (by norm_num), Real.log_rpow hnR] at hlogs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0log : a0 * Real.log 2 = Real.log 3 / 2 := by
    unfold a0 logTwoThree
    field_simp [hlog2.ne']
  unfold driftGap at hlogs
  have hscaled :
      ((oddCount n k : ℝ) - (k : ℝ) / 2) * Real.log 3 ≤
        eta * Real.log n := by
    nlinarith
  have hdiff :
      (oddCount n k : ℝ) - (k : ℝ) / 2 ≤
        eta * Real.log n / Real.log 3 :=
    (le_div_iff₀ hlog3).2 hscaled
  linarith

/-- Odd counts across a fixed stopped bootstrap obey the same finite
geometric logarithmic profile as the shortcut clock. -/
theorem oddCount_stageClock_le
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (oddCount n (stageClock p R n) : ℝ) ≤
      (stageClock p R n : ℝ) / 2 +
        eta / Real.log 3 *
          (clockGeom r R * Real.log n +
            (R : ℝ) ^ 2 * Real.log (stageK p)) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  induction R generalizing n with
  | zero => simp [clockGeom]
  | succ R ih =>
      rw [bootstrapSet_succ] at hnSet
      have hnW := hnSet.1
      have hchildSet := hnSet.2
      have hchildPos : 0 < stageMap p n := by
        rw [stageMap_is_actual]
        exact orbit_pos hn _
      have hlenNat := stageLength_le_log p hn hnW
      have hblock :
          (oddCount n (stageLength p n) : ℝ) ≤
            (stageLength p n : ℝ) / 2 +
              eta * Real.log n / Real.log 3 := by
        by_cases hlarge : p.M0 ≤ Nat.log 2 n
        · have hgood := mem_initialWindowGood_of_mem_extended_of_large
            p hnW hlarge
          exact oddCount_upper_of_initialWindowGood hn hgood hlenNat
        · have hlen0 : stageLength p n = 0 := by
            simp [stageLength, hlarge]
          rw [hlen0]
          simp only [oddCount_zero, Nat.cast_zero, zero_div, zero_add]
          have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (show 1 ≤ n by omega)
          exact div_nonneg
            (mul_nonneg p.eta_pos.le
              (Real.log_nonneg hn1R))
            hlog3.le
      have hIH := ih hchildPos hchildSet
      have hclockAdd : stageClock p (R + 1) n =
          stageLength p n + stageClock p R (stageMap p n) :=
        stageClock_succ p R n
      have hoddAdd :
          oddCount n (stageClock p (R + 1) n) =
            oddCount n (stageLength p n) +
              oddCount (stageMap p n) (stageClock p R (stageMap p n)) := by
        rw [hclockAdd, oddCount_add, stageMap_is_actual]
      have hlogMap : Real.log (stageMap p n) ≤
          Real.log (stageK p) + r * Real.log n := by
        have hstage := stageMap_le_power p hn hnW
        have hmono := Real.log_le_log (by exact_mod_cast hchildPos)
          hstage
        calc
          Real.log (stageMap p n) ≤
              Real.log (stageK p * (n : ℝ) ^ r) := hmono
          _ = Real.log (stageK p) + r * Real.log n := by
            rw [Real.log_mul (stageK_pos p).ne'
              (Real.rpow_pos_of_pos (by exact_mod_cast hn) r).ne',
              Real.log_rpow (by exact_mod_cast hn)]
      rw [hoddAdd, hclockAdd]
      push_cast
      have hgeom0 := clockGeom_nonneg p.r_pos.le R
      have hgeomR := clockGeom_le_nat p.r_pos.le p.r_lt_one.le R
      have heta0 := p.eta_pos.le
      have hlogK0 : 0 ≤ Real.log (stageK p) :=
        Real.log_nonneg (stageK_one_le p)
      rw [clockGeom]
      have hweightedLog := mul_le_mul_of_nonneg_left hlogMap hgeom0
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show 1 ≤ n by omega)
      have hprofile :
          Real.log n +
              (clockGeom r R * Real.log (stageMap p n) +
                (R : ℝ) ^ 2 * Real.log (stageK p)) ≤
            (1 + r * clockGeom r R) * Real.log n +
              ((R : ℝ) + 1) ^ 2 * Real.log (stageK p) := by
        have hgeomLogK := mul_le_mul_of_nonneg_right hgeomR hlogK0
        calc
          Real.log n +
                (clockGeom r R * Real.log (stageMap p n) +
                  (R : ℝ) ^ 2 * Real.log (stageK p)) ≤
              Real.log n +
                (clockGeom r R *
                    (Real.log (stageK p) + r * Real.log n) +
                  (R : ℝ) ^ 2 * Real.log (stageK p)) := by
            linarith
          _ ≤ (1 + r * clockGeom r R) * Real.log n +
                ((R : ℝ) + 1) ^ 2 * Real.log (stageK p) := by
            nlinarith
      have hq0 : 0 ≤ eta / Real.log 3 := div_nonneg heta0 hlog3.le
      have hweightedProfile := mul_le_mul_of_nonneg_left hprofile hq0
      have hblock' :
          (oddCount n (stageLength p n) : ℝ) ≤
            (stageLength p n : ℝ) / 2 +
              eta / Real.log 3 * Real.log n := by
        convert hblock using 1
        ring
      nlinarith

/-- Leading raw-step coefficient for a stopped bootstrap. -/
def rawClockLeading (r eta : ℝ) : ℝ :=
  (3 / (2 * Real.log 2) + eta / Real.log 3) / (1 - r)

/-- Exact fixed-depth raw-time estimate obtained by combining the shortcut
clock with the generated odd-count bound. -/
theorem stageRawClock_le
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (rawTime n (stageClock p R n) : ℝ) ≤
      clockGeom r R *
          (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n +
        (R : ℝ) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) := by
  have hclock := stageClock_le_logb p hn hnSet
  have hodd := oddCount_stageClock_le p hn hnSet
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgeom0 := clockGeom_nonneg p.r_pos.le R
  have hlogn0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hlogK0 : 0 ≤ Real.log (stageK p) :=
    Real.log_nonneg (stageK_one_le p)
  have hlogbK0 : 0 ≤ Real.logb 2 (stageK p) :=
    Real.logb_nonneg (by norm_num) (stageK_one_le p)
  have hclockScaled := mul_le_mul_of_nonneg_left hclock (by norm_num :
    (0 : ℝ) ≤ 3 / 2)
  have hrawFirst :
      (rawTime n (stageClock p R n) : ℝ) ≤
        3 / 2 * (stageClock p R n : ℝ) +
          eta / Real.log 3 *
            (clockGeom r R * Real.log n +
              (R : ℝ) ^ 2 * Real.log (stageK p)) := by
    unfold rawTime
    push_cast
    linarith
  calc
    (rawTime n (stageClock p R n) : ℝ) ≤
        3 / 2 * (stageClock p R n : ℝ) +
          eta / Real.log 3 *
            (clockGeom r R * Real.log n +
              (R : ℝ) ^ 2 * Real.log (stageK p)) := hrawFirst
    _ ≤ 3 / 2 *
          (clockGeom r R * Real.logb 2 n +
            (R : ℝ) ^ 2 * Real.logb 2 (stageK p)) +
          eta / Real.log 3 *
            (clockGeom r R * Real.log n +
              (R : ℝ) ^ 2 * Real.log (stageK p)) := by
      gcongr
    _ = clockGeom r R *
          (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n +
        (R : ℝ) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) := by
      rw [Real.logb]
      ring

/-- Uniform shellwise raw clock below any strict budget exceeding the leading
coefficient.  The logarithmic-stage error is swallowed by `log n`. -/
theorem eventuallyShellRawClockLt
    {r eta omega rawClock : ℝ} (p : StageSetup r eta)
    (homega0 : 0 < omega)
    (hleading : rawClockLeading r eta < rawClock) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      (rawTime n (stageClock p (stageCount omega M) n) : ℝ) <
        rawClock * Real.log n := by
  let gap := rawClock - rawClockLeading r eta
  let A := omega ^ 2 *
    (3 / 2 * Real.logb 2 (stageK p) +
      eta / Real.log 3 * Real.log (stageK p))
  let c := gap * (Real.log 2 / 5)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlogbK0 : 0 ≤ Real.logb 2 (stageK p) :=
      Real.logb_nonneg (by norm_num) (stageK_one_le p)
    have hlogK0 := Real.log_nonneg (stageK_one_le p)
    have hetaRatio0 : 0 ≤ eta / Real.log 3 :=
      div_nonneg p.eta_pos.le hlog3.le
    exact mul_nonneg (sq_nonneg omega)
      (add_nonneg (mul_nonneg (by norm_num) hlogbK0)
        (mul_nonneg hetaRatio0 hlogK0))
  have hc : 0 < c := by dsimp [c]; positivity
  let q := c / (2 * (A + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hsmallReal := (isLittleO_log_rpow_rpow_atTop
    (s := (1 : ℝ)) 2 (by norm_num)).bound hq
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop (4 : ℝ)
      tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with M hsm hM
  intro n hn hnshell hnboot
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxpow0 : 0 ≤ x ^ (1 : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans hx) _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogx0 2),
    Real.norm_eq_abs, abs_of_nonneg hxpow0, Real.rpow_one] at hsm
  have herrorScalar : A * (Real.log x) ^ 2 < c * x := by
    have hmul := mul_le_mul_of_nonneg_left hsm (by linarith : 0 ≤ A + 1)
    dsimp [q] at hmul
    have hcoef : A ≤ A + 1 := by linarith
    have hnonneg : 0 ≤ Real.log x ^ (2 : ℕ) := sq_nonneg _
    have hleft : A * Real.log x ^ (2 : ℕ) ≤
        (A + 1) * Real.log x ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hcoef hnonneg
    have hA1ne : A + 1 ≠ 0 := ne_of_gt (by linarith)
    have hhalf : (A + 1) * (c / (2 * (A + 1)) * x) = c / 2 * x := by
      field_simp [hA1ne]
    rw [hhalf] at hmul
    have hmid : A * Real.log x ^ (2 : ℕ) ≤ c / 2 * x :=
      hleft.trans (by simpa [mul_assoc] using hmul)
    have hcx : 0 < c * x := mul_pos hc (zero_lt_one.trans_le hx)
    exact hmid.trans_lt (by
      calc
        c / 2 * x = (c * x) / 2 := by ring
        _ < c * x := div_lt_self hcx (by norm_num))
  have hRle := stageCount_le homega0.le M
  have hR2 : (R : ℝ) ^ 2 ≤ (omega * Real.log x) ^ 2 := by
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith
  have hcoef0 : 0 ≤
      3 / 2 * Real.logb 2 (stageK p) +
        eta / Real.log 3 * Real.log (stageK p) := by
    have hlogbK0 : 0 ≤ Real.logb 2 (stageK p) :=
      Real.logb_nonneg (by norm_num) (stageK_one_le p)
    have hlogK0 := Real.log_nonneg (stageK_one_le p)
    have hetaRatio0 : 0 ≤ eta / Real.log 3 :=
      div_nonneg p.eta_pos.le hlog3.le
    exact add_nonneg (mul_nonneg (by norm_num) hlogbK0)
      (mul_nonneg hetaRatio0 hlogK0)
  have herror :
      (R : ℝ) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) <
        gap * (Real.log 2 / 5 * x) := by
    have hmul := mul_le_mul_of_nonneg_right hR2 hcoef0
    have hform : (omega * Real.log x) ^ 2 *
          (3 / 2 * Real.logb 2 (stageK p) +
            eta / Real.log 3 * Real.log (stageK p)) =
        A * (Real.log x) ^ 2 := by
      dsimp [A]
      ring
    rw [hform] at hmul
    exact hmul.trans_lt (by dsimp [c] at herrorScalar; nlinarith)
  have hlogLower : Real.log 2 / 5 * x ≤ Real.log n := by
    have hfrac : x / 5 ≤ (M : ℝ) := by
      dsimp [x]
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hlowerNat : (2 : ℕ) ^ M ≤ n :=
      (mem_dyadicShell.mp hnshell).1
    have hlower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
      have hlowerCast : (2 : ℝ) ^ M ≤ (n : ℝ) := by
        exact_mod_cast hlowerNat
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
        hlowerCast
      rw [Real.log_pow] at h
      exact h
    nlinarith [mul_le_mul_of_nonneg_right hfrac
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  have hraw := stageRawClock_le p hn hnboot
  have hgeom := clockGeomLeInvOneSub p.r_pos.le p.r_lt_one R
  have hfactor0 : 0 ≤
      3 / (2 * Real.log 2) + eta / Real.log 3 := by
    exact add_nonneg (div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le))
      (div_nonneg p.eta_pos.le hlog3.le)
  have hlogn0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hlead :
      clockGeom r R *
          (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n ≤
        rawClockLeading r eta * Real.log n := by
    unfold rawClockLeading
    have hm := mul_le_mul_of_nonneg_right hgeom hfactor0
    calc
      clockGeom r R *
            (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n ≤
          ((1 - r)⁻¹ *
            (3 / (2 * Real.log 2) + eta / Real.log 3)) * Real.log n :=
        mul_le_mul_of_nonneg_right hm hlogn0
      _ = (3 / (2 * Real.log 2) + eta / Real.log 3) /
            (1 - r) * Real.log n := by
        rw [div_eq_mul_inv]
        ring
  calc
    (rawTime n (stageClock p R n) : ℝ) ≤
        clockGeom r R *
            (3 / (2 * Real.log 2) + eta / Real.log 3) * Real.log n +
          (R : ℝ) ^ 2 *
            (3 / 2 * Real.logb 2 (stageK p) +
              eta / Real.log 3 * Real.log (stageK p)) := hraw
    _ < rawClockLeading r eta * Real.log n + gap * Real.log n := by
      apply add_lt_add_of_le_of_lt hlead
      exact herror.trans_le (mul_le_mul_of_nonneg_left hlogLower hgap.le)
    _ = rawClock * Real.log n := by dsimp [gap]; ring

end

end FirstPassageLinearTransport
