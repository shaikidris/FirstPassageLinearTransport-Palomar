/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutOrbitCeiling

/-!
# Centered raw clock for the timeout route

The shortcut time corridor and the rank-scaled reverse-product bound together
control the odd-state count.  This module turns those two deterministic facts
into the centered raw clock used by the version-4 theorem.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Taking logarithms in the exact reverse-product identity converts a
positive lower bound for the reverse product into a two-sided odd-count
estimate.  The constant two accounts for the widths of the source and landing
dyadic shells and for `log P ∈ [-log 2,0]`. -/
theorem oddCount_centered_of_firstPassage_reverseProduct_half
    {n k M q : ℕ} {E : ℝ}
    (hn : 0 < n) (hnShell : n ∈ dyadicShell M)
    (hk : 0 < k) (hfp : IsFirstPassage (2 ^ q) n k)
    (hP : (1 / 2 : ℚ) ≤ reverseProduct n k)
    (hE : |driftGap * (k : ℝ) -
      (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤ E) :
    |(oddCount n k : ℝ) - (k : ℝ) / 2| ≤
      (E + 2) * Real.log 2 / Real.log 3 := by
  let y := orbit k n
  have hy : 0 < y := orbit_pos hn k
  have hPposQ : (0 : ℚ) < reverseProduct n k :=
    (by norm_num : (0 : ℚ) < 1 / 2).trans_le hP
  have hPpos : (0 : ℝ) < (reverseProduct n k : ℝ) := by
    exact_mod_cast hPposQ
  have hPupQ := reverseProduct_le_one hn k
  have hPup : (reverseProduct n k : ℝ) ≤ 1 := by exact_mod_cast hPupQ
  have hidQ := reverse_product_identity hn k
  have hidR : (n : ℝ) =
      (((2 : ℝ) ^ k * (y : ℝ)) / (3 : ℝ) ^ oddCount n k) *
        (reverseProduct n k : ℝ) := by
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hidQ
    norm_num only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow] at hcast
    simpa [y] using hcast
  have hlogId := congrArg Real.log hidR
  rw [Real.log_mul (by positivity) hPpos.ne',
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlogId
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hnBounds := mem_dyadicShell.mp hnShell
  have hnLoR : ((2 ^ M : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnBounds.1
  have hnHiR : (n : ℝ) < ((2 ^ (M + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnBounds.2
  have hlognLo := Real.log_le_log (by positivity) hnLoR
  have hlognHi := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by exact_mod_cast hn : (0 : ℝ) < n))
    (Set.mem_Ioi.mpr
      (by positivity : (0 : ℝ) < ((2 ^ (M + 1) : ℕ) : ℝ))) hnHiR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlognLo hlognHi
  simp only [Real.log_pow] at hlognLo hlognHi
  have hyUpperNat : y ≤ 2 ^ q := hfp.1
  have hyUpperR : (y : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast hyUpperNat
  have hlogyUpper := Real.log_le_log (by positivity) hyUpperR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlogyUpper
  simp only [Real.log_pow] at hlogyUpper
  have hyLowerNat : 2 ^ q < 2 * y := (firstPassage_band hk hfp).1
  have hyLowerR : ((2 ^ q : ℕ) : ℝ) < 2 * (y : ℝ) := by
    exact_mod_cast hyLowerNat
  have hlogyLower := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < ((2 ^ q : ℕ) : ℝ)))
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < 2 * (y : ℝ))) hyLowerR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlogyLower
  rw [Real.log_pow,
    Real.log_mul (by norm_num)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hy))] at hlogyLower
  have hPcast : (((1 / 2 : ℚ) : ℝ)) ≤ (reverseProduct n k : ℝ) :=
    Rat.cast_le.2 hP
  norm_num at hPcast
  have hlogPLo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hPcast
  have hlogPUp := Real.log_nonpos hPpos.le hPup
  rw [show (1 / 2 : ℝ) = 1 / 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_one] at hlogPLo
  have hgaplog : driftGap * Real.log 2 = Real.log 2 - Real.log 3 / 2 := by
    unfold driftGap a0 logTwoThree
    field_simp [hlog2.ne']
  have hgapk :
      driftGap * (k : ℝ) * Real.log 2 =
        (k : ℝ) * Real.log 2 - (k : ℝ) / 2 * Real.log 3 := by
    calc
      driftGap * (k : ℝ) * Real.log 2 =
          (driftGap * Real.log 2) * (k : ℝ) := by ring
      _ = (Real.log 2 - Real.log 3 / 2) * (k : ℝ) := by rw [hgaplog]
      _ = (k : ℝ) * Real.log 2 - (k : ℝ) / 2 * Real.log 3 := by ring
  have hElo := (abs_le.mp hE).1
  have hEhi := (abs_le.mp hE).2
  push_cast at hElo hEhi hlognHi
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hlog3]
    nlinarith
  · rw [le_div_iff₀ hlog3]
    nlinarith

/-- Eventually every timeout run in the moving endpoint construction has a
reverse product bounded below by one half. -/
theorem eventually_timeoutRun_reverseProduct_half
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      (1 / 2 : ℚ) ≤ reverseProduct n elapsed := by
  have hTerminalT := tendsto_movingTerminalRank_atTop_of_sharp hbuffer
  have hSwitchT := tendsto_shrinkingSwitchRank_atTop P.Cswitch_pos
  have hSmallBase := eventually_rankTransport_small P.run.rStar_pos
  rw [eventually_atTop] at hSmallBase
  obtain ⟨Q, hQ⟩ := hSmallBase
  have hSwitchCast : Tendsto
      (fun M : ℕ => (shrinkingSwitchRank P.Cswitch M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hSwitchT
  have hrHiR : (0 : ℝ) < (P.run.rHi : ℝ) := by
    exact_mod_cast P.run.pHi.r_pos
  have hHighT : Tendsto
      (fun M : ℕ => (P.run.rHi : ℝ) *
        (shrinkingSwitchRank P.Cswitch M : ℝ)) atTop atTop :=
    hSwitchCast.const_mul_atTop hrHiR
  have hHigh := (tendsto_atTop.1 hHighT) (Q : ℝ)
  have hQL := (tendsto_atTop.1 hTerminalT) (2 * Q)
  have hLowRatioBase : ∀ᶠ L : ℕ in atTop,
      (1 / 2 : ℝ) ≤ movingLowRatio P.K₀ L :=
    (tendsto_movingLowRatio P.K₀).eventually
      (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hLowRatio := hTerminalT.eventually hLowRatioBase
  have hStarHi : P.run.rStar ≤ P.run.rHi := by
    rw [P.run.rStar_eq]
    exact min_le_left _ _
  have hStarLoBase : ∀ᶠ L : ℕ in atTop,
      (P.run.rStar : ℝ) ≤ movingLowRatio P.K₀ L := by
    have hrStarOne : (P.run.rStar : ℝ) < 1 := by
      have hStarHiR : (P.run.rStar : ℝ) ≤ (P.run.rHi : ℝ) := by
        exact_mod_cast hStarHi
      exact hStarHiR.trans_lt P.run.pHi.r_lt_one
    exact (tendsto_movingLowRatio P.K₀).eventually
      (Ici_mem_nhds hrStarOne)
  have hStarLo := hTerminalT.eventually hStarLoBase
  filter_upwards [hHigh, hQL, hLowRatio, hStarLo] with M hHigh hQL
      hLowRatio hStarLo
  intro n elapsed q hrun
  have hqQ := hrun.currentRank_ge hHigh hLowRatio hQL
  have hsmall := hQ q hqQ
  have hnShell := hrun.source_mem_dyadicShell
  have hn : 0 < n := (by
    have hlo := (mem_dyadicShell.mp hnShell).1
    have hpow : 0 < 2 ^ M := by positivity
    omega)
  have hY : 0 < 2 ^ q := by positivity
  have hloss := hrun.scaledReverseLoss_le P.run.rStar_pos hStarHi hStarLo
  have hPlow := one_sub_div_le_reverseProduct_of_scaledLoss hn hY hloss
  have htwoThird : (2 / 3 : ℚ) ≤
      1 - ((((q + 2 : ℕ) : ℚ) / P.run.rStar) /
        ((2 ^ q : ℕ) : ℚ)) := by linarith
  exact (by norm_num : (1 / 2 : ℚ) ≤ 2 / 3).trans
    (htwoThird.trans hPlow)

/-- A power of two contributes no odd shortcut steps before it has been
halved through its exponent. -/
theorem oddCount_two_pow_eq_zero {q v : ℕ} (hv : v ≤ q) :
    oddCount (2 ^ q) v = 0 := by
  induction v generalizing q with
  | zero => simp
  | succ v ih =>
      have hvq : v ≤ q := by omega
      have hpos : 0 < q - v := by omega
      have heven : orbit v (2 ^ q) % 2 = 0 := by
        rw [timeout_orbit_two_pow hvq]
        obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hpos)
        rw [hd, pow_succ]
        omega
      have hbit : (parityBit (2 ^ q) v : ℕ) = 0 := by
        simpa [parityBit] using heven
      rw [oddCount_succ, ih hvq, hbit]

/-- Exact halving after a shortcut prefix adds one raw step per halving and
no extra odd raw step. -/
theorem rawTime_add_exact_halving
    {n elapsed q v : ℕ} (heq : orbit elapsed n = 2 ^ q) (hv : v ≤ q) :
    rawTime n (elapsed + v) = rawTime n elapsed + v := by
  unfold rawTime
  rw [oddCount_add, heq, oddCount_two_pow_eq_zero hv]
  omega

/-- Explicit coefficient for the normalized centered raw clock. -/
def timeoutRawClockSupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  let T := timeoutTimeSupportConstant P C
  T + (2 * driftGap / 3) *
    (driftGap / 2 * T + 2) * Real.log 2 / Real.log 3

/-- Explicit coefficient after adding an exact-halving terminal tail to the
centered raw clock. -/
def timeoutCompletedRawClockSupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  timeoutRawClockSupportConstant P C + timeoutTimeSupportConstant P C

/-- The exact raw time associated with every terminal-scale timeout run has
the centered drift `2*driftGap/3`.  The estimate uses the same good sources
and introduces no additional exceptional set. -/
theorem eventually_timeoutRun_rawTime_centered
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      q ≤ shrinkingSwitchRank P.Cswitch M →
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| ≤
        timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  let T := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch
  have hReverse := eventually_timeoutRun_reverseProduct_half P hbuffer
  have hElapsed := eventually_timeoutRun_elapsed_centered
    (K₀ := P.K₀) P.run.toTimeoutHigh P.Cswitch_pos.le
  have hPotential := eventually_timeoutTimePotential_source_le_sqrt
    P.run.toTimeoutHigh P.Cswitch_pos.le
  filter_upwards [hReverse, hElapsed, hPotential,
      eventually_ge_atTop (1 : ℕ)]
    with M hReverse hElapsed hPotential hM
  intro n elapsed q hqS hrun
  let S := shrinkingSwitchRank P.Cswitch M
  let sourcePotential := timeoutTimePotential P.run.toTimeoutHigh M S (M + 1)
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hnShell := hrun.source_mem_dyadicShell
  have hn : 0 < n := by
    have hlo := (mem_dyadicShell.mp hnShell).1
    have hpow : 0 < 2 ^ M := by positivity
    omega
  have hP := hReverse hrun
  have hdev := hrun.deviation_add_potential_le hM
  have hpotq0 := timeoutTimePotential_nonneg P.run.toTimeoutHigh M S q
  have hlocal :
      |driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    linarith
  have hodd := oddCount_centered_of_firstPassage_reverseProduct_half
    hn hnShell hrun.elapsed_pos hrun.directFirstPassage hP hlocal
  have hElapsed' := hElapsed hqS hrun
  have hpot0 : 0 ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    exact timeoutTimePotential_nonneg P.run.toTimeoutHigh M
      (shrinkingSwitchRank P.Cswitch M) (M + 1)
  have hlog1 : 1 ≤ Real.log ((M : ℝ) + 2) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hroot1 : 1 ≤ root := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hdivBound : 2 * sourcePotential / driftGap ≤ T * root := by
    dsimp [T, root, sourcePotential, S] at hPotential ⊢
    linarith
  have hpotBound :
      sourcePotential ≤ driftGap / 2 * T * root := by
    rw [div_le_iff₀ driftGap_pos] at hdivBound
    nlinarith
  have hTpos : 0 < T := by
    by_contra hT
    have hTnonpos : T ≤ 0 := le_of_not_gt hT
    have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
    have hright : T * root ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hTnonpos hroot0
    have hleft : 0 ≤ 2 * sourcePotential / driftGap :=
      div_nonneg (mul_nonneg (by norm_num) hpot0) driftGap_pos.le
    linarith
  have hoddScale :
      |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| ≤
        (driftGap / 2 * T + 2) * root * Real.log 2 / Real.log 3 := by
    have hbase : sourcePotential + 2 ≤
        (driftGap / 2 * T + 2) * root := by
      have htwo : (2 : ℝ) ≤ 2 * root := by linarith
      have hcoef0 : 0 ≤ driftGap / 2 * T :=
        mul_nonneg (div_nonneg driftGap_pos.le (by norm_num)) hTpos.le
      calc
        sourcePotential + 2 ≤ driftGap / 2 * T * root + 2 * root :=
          add_le_add hpotBound htwo
        _ = (driftGap / 2 * T + 2) * root := by ring
    exact hodd.trans (by
      apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).2
      exact mul_le_mul_of_nonneg_right hbase
        (Real.log_nonneg (by norm_num)))
  have hrawCast : (rawTime n elapsed : ℝ) =
      (elapsed : ℝ) + (oddCount n elapsed : ℝ) := by
    simp [rawTime]
  have hcoef0 : 0 ≤ 2 * driftGap / 3 :=
    div_nonneg (mul_nonneg (by norm_num) driftGap_pos.le) (by norm_num)
  calc
    |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| =
        |(driftGap * (elapsed : ℝ) - (M : ℝ)) +
          (2 * driftGap / 3) *
            ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2)| := by
      rw [hrawCast]
      ring_nf
    _ ≤ |driftGap * (elapsed : ℝ) - (M : ℝ)| +
          |(2 * driftGap / 3) *
            ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2)| := abs_add_le _ _
    _ = |driftGap * (elapsed : ℝ) - (M : ℝ)| +
          (2 * driftGap / 3) *
            |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| := by
      rw [abs_mul, abs_of_nonneg hcoef0]
    _ ≤ T * root + (2 * driftGap / 3) *
          ((driftGap / 2 * T + 2) * root * Real.log 2 / Real.log 3) :=
      add_le_add hElapsed' (mul_le_mul_of_nonneg_left hoddScale hcoef0)
    _ = timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
      dsimp [timeoutRawClockSupportConstant, T]
      ring

/-- The centered raw clock remains valid after an exact-halving completion
from a dyadic upper endpoint to the terminal rank. -/
theorem eventually_timeoutRun_completed_rawTime_centered
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      L = movingTerminalRank A M →
      q ≤ shrinkingSwitchRank P.Cswitch M →
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀ L M
        (shrinkingSwitchRank P.Cswitch M) n elapsed q →
      orbit elapsed n = 2 ^ q →
      |(2 * driftGap / 3) *
          (rawTime n (elapsed + (q - L)) : ℝ) - (M : ℝ)| ≤
        timeoutCompletedRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hRaw := eventually_timeoutRun_rawTime_centered P hbuffer
  have hPotential := eventually_timeoutTimePotential_source_le_sqrt
    P.run.toTimeoutHigh P.Cswitch_pos.le
  have hSwitch := eventually_shrinkingSwitchRank_lt_source P.Cswitch_pos.le
  filter_upwards [hRaw, hPotential, hSwitch, eventually_ge_atTop (1 : ℕ)]
    with M hRaw hPotential hSwitch hM
  intro L n elapsed q hL hqS hrun heq
  let S := shrinkingSwitchRank P.Cswitch M
  let sourcePotential := timeoutTimePotential P.run.toTimeoutHigh M S (M + 1)
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hrun' : TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
      (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
      n elapsed q := by
    simpa [hL] using hrun
  have hRaw' := hRaw hqS hrun'
  have hvq : q - L ≤ q := Nat.sub_le q L
  have htime : rawTime n (elapsed + (q - L)) =
      rawTime n elapsed + (q - L) :=
    rawTime_add_exact_halving heq hvq
  have hSsq : (S : ℝ) ≤ (S : ℝ) ^ 2 := by
    by_cases hS0 : S = 0
    · simp [hS0]
    · have hS1 : (1 : ℝ) ≤ (S : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hS0)
      nlinarith [sq_nonneg ((S : ℝ) - 1)]
  have hreserve : (S : ℝ) ^ 2 ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    exact timeout_switch_sq_le_source_potential P.run.toTimeoutHigh (by omega)
  have hvS : q - L ≤ S := (Nat.sub_le q L).trans hqS
  have hvR : ((q - L : ℕ) : ℝ) ≤ sourcePotential := by
    have hvSR : ((q - L : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hvS
    exact hvSR.trans (hSsq.trans hreserve)
  have hcoef0 : 0 ≤ 2 * driftGap / 3 :=
    div_nonneg (mul_nonneg (by norm_num) driftGap_pos.le) (by norm_num)
  have hcoefGap : 2 * driftGap / 3 ≤ driftGap := by
    nlinarith [driftGap_pos]
  have hextra : (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤
      timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
    have hfirst : (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤
        sourcePotential := by
      calc
        (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤
            driftGap * ((q - L : ℕ) : ℝ) := by gcongr
        _ ≤ 1 * ((q - L : ℕ) : ℝ) := by
          have hgap_le_one : driftGap ≤ 1 := by
            linarith [driftGap_lt_a0, a0_lt_one]
          gcongr
        _ ≤ sourcePotential := by simpa using hvR
    have hpot0 : 0 ≤ sourcePotential := by
      dsimp [sourcePotential, S]
      exact timeoutTimePotential_nonneg P.run.toTimeoutHigh M
        (shrinkingSwitchRank P.Cswitch M) (M + 1)
    have hscaled : sourcePotential ≤ 2 * sourcePotential / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      have hgap_le_one : driftGap ≤ 1 := by
        linarith [driftGap_lt_a0, a0_lt_one]
      nlinarith
    calc
      (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤ sourcePotential := hfirst
      _ ≤ 1 + 2 * sourcePotential / driftGap := by linarith
      _ ≤ timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
        simpa [sourcePotential, S, root, div_eq_mul_inv, mul_assoc] using hPotential
  calc
    |(2 * driftGap / 3) *
          (rawTime n (elapsed + (q - L)) : ℝ) - (M : ℝ)| =
        |((2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)) +
          (2 * driftGap / 3) * ((q - L : ℕ) : ℝ)| := by
      rw [htime]
      push_cast
      ring
    _ ≤ |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| +
          |(2 * driftGap / 3) * ((q - L : ℕ) : ℝ)| := abs_add_le _ _
    _ = |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| +
          (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg hcoef0 (Nat.cast_nonneg _))]
    _ ≤ timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch * root +
          timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root :=
      add_le_add hRaw' hextra
    _ = timeoutCompletedRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          root := by
      unfold timeoutCompletedRawClockSupportConstant
      ring

end

end FirstPassageLinearTransport
