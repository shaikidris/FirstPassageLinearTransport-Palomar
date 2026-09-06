/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutRawClock

/-!
# Uniform trajectory profiles for timeout runs

The endpoint clock estimate controls completed passages.  This module keeps
the same deterministic bookkeeping at every intermediate shortcut time.  A
certified high block inherits its logarithmic tube directly from
`initialWindowGood`; an uncertified low timeout block is paid for by the
existing low-rank reserve.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-- Natural-log deviation of a shortcut prefix from the central drift line. -/
def shortcutLogDeviation (n j : ℕ) : ℝ :=
  Real.log (orbit j n) - Real.log n +
    driftGap * (j : ℝ) * Real.log 2

/-- Natural-log deviation of a raw Collatz prefix from its central drift
line. -/
def rawLogDeviation (n i : ℕ) : ℝ :=
  Real.log (rawOrbit i n) - Real.log n +
    (2 * driftGap / 3) * (i : ℝ) * Real.log 2

/-- Coefficient converting an odd-count error into raw-time drift error. -/
def rawOddDeviationCoefficient : ℝ :=
  (2 * driftGap / 3) * Real.log 2

theorem rawOddDeviationCoefficient_nonneg :
    0 ≤ rawOddDeviationCoefficient := by
  unfold rawOddDeviationCoefficient
  exact mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) driftGap_pos.le) (by norm_num))
    (Real.log_pos (by norm_num)).le

/-- Logarithmic deviations split exactly when shortcut segments are
concatenated. -/
theorem shortcutLogDeviation_add (n k j : ℕ) :
    shortcutLogDeviation n (j + k) =
      shortcutLogDeviation n k + shortcutLogDeviation (orbit k n) j := by
  rw [shortcutLogDeviation, shortcutLogDeviation, shortcutLogDeviation,
    orbit_add]
  push_cast
  ring

/-- At a raw time corresponding exactly to a shortcut prefix, raw deviation
is shortcut deviation plus the centered odd-count correction. -/
theorem rawLogDeviation_rawTime (n j : ℕ) :
    rawLogDeviation n (rawTime n j) =
      shortcutLogDeviation n j + rawOddDeviationCoefficient *
        ((oddCount n j : ℝ) - (j : ℝ) / 2) := by
  rw [rawLogDeviation, rawOrbit_rawTime_eq_orbit, rawTime,
    shortcutLogDeviation, rawOddDeviationCoefficient]
  push_cast
  ring

/-- Every raw prefix is either a shortcut state or the unique intermediate
odd image immediately preceding the next shortcut state. -/
theorem rawTime_prefix_cases {n k i : ℕ} (hi : i ≤ rawTime n k) :
    ∃ j : ℕ, j ≤ k ∧
      (i = rawTime n j ∨
        (j < k ∧ orbit j n % 2 = 1 ∧ i = rawTime n j + 1)) := by
  induction k with
  | zero =>
      have hi0 : i = 0 := by simpa [rawTime] using hi
      exact ⟨0, le_rfl, Or.inl (by simpa [rawTime] using hi0)⟩
  | succ k ih =>
      by_cases hiprev : i ≤ rawTime n k
      · rcases ih hiprev with ⟨j, hjk, hj⟩
        refine ⟨j, hjk.trans (Nat.le_succ k), ?_⟩
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr ⟨hj.1.trans_le (Nat.le_succ k), hj.2.1, hj.2.2⟩
      · rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
        · have hbit : (parityBit n k : ℕ) = 0 := by
            simpa [parityBit] using heven
          have htime : rawTime n (k + 1) = rawTime n k + 1 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hiNext : i = rawTime n (k + 1) := by
            rw [htime] at hi
            omega
          exact ⟨k + 1, le_rfl, Or.inl hiNext⟩
        · have hbit : (parityBit n k : ℕ) = 1 := by
            simpa [parityBit] using hodd
          have htime : rawTime n (k + 1) = rawTime n k + 2 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hiCases : i = rawTime n k + 1 ∨
              i = rawTime n (k + 1) := by
            rw [htime] at hi
            omega
          rcases hiCases with hintermediate | hnext
          · exact ⟨k, Nat.le_succ k,
              Or.inr ⟨Nat.lt_succ_self k, hodd, hintermediate⟩⟩
          · exact ⟨k + 1, le_rfl, Or.inl hnext⟩

/-- Corresponding raw times are strictly increasing with shortcut time. -/
theorem rawTime_strictMono (n : ℕ) : StrictMono (rawTime n) := by
  intro a b hab
  have hodd := oddCount_mono (n := n) hab.le
  unfold rawTime
  omega

/-- The only non-shortcut raw state is twice the following shortcut state. -/
theorem rawOrbit_rawTime_add_one_eq_two_mul
    {n j : ℕ} (hodd : orbit j n % 2 = 1) :
    rawOrbit (rawTime n j + 1) n = 2 * orbit (j + 1) n := by
  rw [show rawTime n j + 1 = 1 + rawTime n j by omega,
    rawOrbit_add, rawOrbit_rawTime_eq_orbit,
    rawOrbit_succ, rawOrbit_zero, rawCollatz_of_odd hodd,
    orbit_succ]
  exact (two_mul_shortcut_of_odd hodd).symm

/-- The intermediate raw odd image differs from the following corresponding
raw-time deviation by one bounded raw step. -/
theorem rawLogDeviation_intermediate
    {n j : ℕ} (hn : 0 < n) (hodd : orbit j n % 2 = 1) :
    rawLogDeviation n (rawTime n j + 1) =
      rawLogDeviation n (rawTime n (j + 1)) +
        (1 - 2 * driftGap / 3) * Real.log 2 := by
  have hbit : (parityBit n j : ℕ) = 1 := by
    simpa [parityBit] using hodd
  have htime : rawTime n (j + 1) = rawTime n j + 2 := by
    simp [rawTime, oddCount_succ, hbit]
    omega
  have hnext : 0 < orbit (j + 1) n := orbit_pos hn (j + 1)
  rw [rawLogDeviation, rawLogDeviation,
    rawOrbit_rawTime_add_one_eq_two_mul hodd,
    rawOrbit_rawTime_eq_orbit]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnext))]
  push_cast at htime ⊢
  rw [htime]
  push_cast
  ring

/-- Corresponding raw times inherit the shortcut and odd-count tubes. -/
theorem abs_rawLogDeviation_rawTime_le
    {n j : ℕ} {E F : ℝ}
    (hshortcut : |shortcutLogDeviation n j| ≤ E)
    (hodd : |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    |rawLogDeviation n (rawTime n j)| ≤
      E + rawOddDeviationCoefficient * F := by
  rw [rawLogDeviation_rawTime]
  have habs := abs_add_le (shortcutLogDeviation n j)
    (rawOddDeviationCoefficient *
      ((oddCount n j : ℝ) - (j : ℝ) / 2))
  have hcoef0 := rawOddDeviationCoefficient_nonneg
  rw [abs_mul, abs_of_nonneg hcoef0] at habs
  nlinarith [mul_le_mul_of_nonneg_left hodd hcoef0]

/-- Uniform shortcut and odd-count tubes control every raw prefix; the final
`log 2` pays the unique intermediate odd image. -/
theorem rawPrefix_log_deviation_le
    {n k : ℕ} {E F : ℝ}
    (hn : 0 < n)
    (hshortcut : ∀ j : ℕ, j ≤ k → |shortcutLogDeviation n j| ≤ E)
    (hodd : ∀ j : ℕ, j ≤ k →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    ∀ i : ℕ, i ≤ rawTime n k →
      |rawLogDeviation n i| ≤
        E + rawOddDeviationCoefficient * F + Real.log 2 := by
  intro i hi
  rcases rawTime_prefix_cases hi with ⟨j, hjk, hj⟩
  have hcorresponding (j : ℕ) (hjk : j ≤ k) :
      |rawLogDeviation n (rawTime n j)| ≤
        E + rawOddDeviationCoefficient * F :=
    abs_rawLogDeviation_rawTime_le (hshortcut j hjk) (hodd j hjk)
  rcases hj with htime | hintermediate
  · subst i
    have hlogTwo0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    linarith [hcorresponding j hjk]
  · rcases hintermediate with ⟨hjkStrict, hoddState, htime⟩
    subst i
    have hjNext : j + 1 ≤ k := by omega
    have hnext := hcorresponding (j + 1) hjNext
    have hinter := rawLogDeviation_intermediate hn hoddState
    have hgap0 := driftGap_pos
    have hgap1 : driftGap < 1 := by
      unfold driftGap
      linarith [a0_pos]
    have hlogTwo0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcorr0 : 0 ≤ (1 - 2 * driftGap / 3) * Real.log 2 := by
      exact mul_nonneg (by nlinarith) hlogTwo0.le
    have hcorrLe : (1 - 2 * driftGap / 3) * Real.log 2 ≤
        Real.log 2 := by
      nlinarith
    have habs := abs_add_le (rawLogDeviation n (rawTime n (j + 1)))
      ((1 - 2 * driftGap / 3) * Real.log 2)
    rw [← hinter, abs_of_nonneg hcorr0] at habs
    nlinarith

/-- An exact-halving completion adds no odd shortcut states.  Its centered
odd-count error therefore grows by at most half the completion length. -/
theorem completed_oddCount_centered_le
    {n elapsed q v S : ℕ} {F : ℝ}
    (heq : orbit elapsed n = 2 ^ q)
    (hvq : v ≤ q) (hvS : v ≤ S)
    (hbase : ∀ j : ℕ, j ≤ elapsed →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    ∀ j : ℕ, j ≤ elapsed + v →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F + (S : ℝ) / 2 := by
  intro j hj
  have hF0 : 0 ≤ F := by
    have hzero := hbase 0 (Nat.zero_le elapsed)
    simpa using hzero
  by_cases hjOld : j ≤ elapsed
  · have h := hbase j hjOld
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
    nlinarith
  · let u := j - elapsed
    have hjForm : j = elapsed + u := by
      dsimp [u]
      omega
    have huV : u ≤ v := by
      dsimp [u]
      omega
    have huq := huV.trans hvq
    have huS : (u : ℝ) ≤ S := by exact_mod_cast huV.trans hvS
    have hoddZero := oddCount_two_pow_eq_zero huq
    have hsplit : oddCount n (elapsed + u) = oddCount n elapsed := by
      rw [oddCount_add, heq, hoddZero, add_zero]
    have hbaseElapsed := hbase elapsed le_rfl
    have habs := abs_sub
      ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2) ((u : ℝ) / 2)
    rw [hjForm, hsplit]
    push_cast
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
    rw [show (oddCount n elapsed : ℝ) -
        ((elapsed : ℝ) + (u : ℝ)) / 2 =
          ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2) -
            (u : ℝ) / 2 by ring]
    calc
      _ ≤ |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| +
          |(u : ℝ) / 2| := habs
      _ = |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| +
          (u : ℝ) / 2 := by rw [abs_of_nonneg (div_nonneg hu0 (by norm_num))]
      _ ≤ F + (S : ℝ) / 2 := by linarith

/-- One explicit constant for the complete raw trajectory tube. -/
def timeoutRawTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  timeoutTimeSupportConstant P C +
    rawOddDeviationCoefficient *
      ((timeoutTimeSupportConstant P C + 1) / Real.log 3) + 1

theorem timeoutRawTrajectorySupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutRawTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hcoef := rawOddDeviationCoefficient_nonneg
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold timeoutRawTrajectorySupportConstant
  positivity

theorem one_le_timeoutProfileRoot {M : ℕ} (hM : 1 ≤ M) :
    1 ≤ Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hx : (3 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 3 ≤ M + 2)
  have hlog : 1 ≤ Real.log ((M : ℝ) + 2) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  rw [← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  nlinarith

/-- Actual first shortcut time at which the orbit reaches a real level.  The
value is zero when the defining set is empty; all uses below provide a
witness. -/
noncomputable def shortcutFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {j : ℕ | (orbit j n : ℝ) ≤ z}

/-- Actual first raw time at which the unaccelerated orbit reaches a real
level.  As for `shortcutFirstPassageTime`, all uses provide a witness. -/
noncomputable def rawFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {i : ℕ | (rawOrbit i n : ℝ) ≤ z}

theorem shortcutFirstPassageTime_mem
    {n k : ℕ} {z : ℝ} (hk : (orbit k n : ℝ) ≤ z) :
    (orbit (shortcutFirstPassageTime n z) n : ℝ) ≤ z := by
  unfold shortcutFirstPassageTime
  exact Nat.sInf_mem
    (show {j : ℕ | (orbit j n : ℝ) ≤ z}.Nonempty from ⟨k, hk⟩)

theorem shortcutFirstPassageTime_le
    {n k : ℕ} {z : ℝ} (hk : (orbit k n : ℝ) ≤ z) :
    shortcutFirstPassageTime n z ≤ k :=
  Nat.sInf_le hk

theorem rawFirstPassageTime_mem
    {n i : ℕ} {z : ℝ} (hi : (rawOrbit i n : ℝ) ≤ z) :
    (rawOrbit (rawFirstPassageTime n z) n : ℝ) ≤ z := by
  unfold rawFirstPassageTime
  exact Nat.sInf_mem
    (show {i : ℕ | (rawOrbit i n : ℝ) ≤ z}.Nonempty from ⟨i, hi⟩)

theorem rawFirstPassageTime_le
    {n i : ℕ} {z : ℝ} (hi : (rawOrbit i n : ℝ) ≤ z) :
    rawFirstPassageTime n z ≤ i :=
  Nat.sInf_le hi

@[simp] theorem shortcutFirstPassageTime_self {n : ℕ} :
    shortcutFirstPassageTime n (n : ℝ) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply shortcutFirstPassageTime_le
  simp

@[simp] theorem rawFirstPassageTime_self {n : ℕ} :
    rawFirstPassageTime n (n : ℝ) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply rawFirstPassageTime_le
  simp [rawOrbit_zero]

/-- A nontrivial first downward crossing lands within a factor two of the
crossed real level. -/
theorem shortcutFirstPassageTime_landingBand
    {n k : ℕ} {z : ℝ}
    (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z) :
    z < 2 * (orbit (shortcutFirstPassageTime n z) n : ℝ) ∧
      (orbit (shortcutFirstPassageTime n z) n : ℝ) ≤ z := by
  let tau := shortcutFirstPassageTime n z
  have htauMem := shortcutFirstPassageTime_mem hk
  change (orbit tau n : ℝ) ≤ z at htauMem
  have htauPos : 0 < tau := by
    by_contra hzero
    have htau0 : tau = 0 := Nat.eq_zero_of_not_pos hzero
    rw [htau0, orbit_zero] at htauMem
    exact (not_le_of_gt hzStart) htauMem
  let prev := tau - 1
  have htauEq : tau = prev + 1 := by
    dsimp [prev]
    omega
  have hprevAbove : z < (orbit prev n : ℝ) := by
    by_contra hnot
    have hprevMem : (orbit prev n : ℝ) ≤ z := le_of_not_gt hnot
    have htauLe0 : shortcutFirstPassageTime n z ≤ prev :=
      shortcutFirstPassageTime_le hprevMem
    have htauLe : tau ≤ prev := by simpa [tau] using htauLe0
    omega
  have hstepNat : orbit prev n ≤ 2 * orbit tau n := by
    rw [htauEq, orbit_succ]
    rcases Nat.mod_two_eq_zero_or_one (orbit prev n) with heven | hodd
    · rw [two_mul_shortcut_of_even heven]
    · rw [two_mul_shortcut_of_odd hodd]
      omega
  have hstep : (orbit prev n : ℝ) ≤
      2 * (orbit tau n : ℝ) := by exact_mod_cast hstepNat
  exact ⟨hprevAbove.trans_le hstep, htauMem⟩

/-- Raw and shortcut first passages to an intervening level reach the same
state.  The raw clock is the exact raw time corresponding to the shortcut
first passage. -/
theorem rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
    {n k : ℕ} {z : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z) :
    rawFirstPassageTime n z =
        rawTime n (shortcutFirstPassageTime n z) ∧
      rawOrbit (rawFirstPassageTime n z) n =
        orbit (shortcutFirstPassageTime n z) n := by
  let tau := shortcutFirstPassageTime n z
  let ell := rawTime n tau
  have htauMem0 := shortcutFirstPassageTime_mem hk
  have htauMem : (orbit tau n : ℝ) ≤ z := by simpa [tau] using htauMem0
  have hellMem : (rawOrbit ell n : ℝ) ≤ z := by
    simpa [ell, rawOrbit_rawTime_eq_orbit] using htauMem
  have hrawLe : rawFirstPassageTime n z ≤ ell :=
    rawFirstPassageTime_le hellMem
  have hband0 := shortcutFirstPassageTime_landingBand hzStart hk
  have hband : z < 2 * (orbit tau n : ℝ) ∧
      (orbit tau n : ℝ) ≤ z := by simpa [tau] using hband0
  have hnoEarlier : ∀ i : ℕ, i < ell → z < (rawOrbit i n : ℝ) := by
    intro i hi
    have hiLe : i ≤ rawTime n tau := by simpa [ell] using hi.le
    rcases rawTime_prefix_cases hiLe with ⟨j, hjtau, hcase⟩
    rcases hcase with hcorresponding | hintermediate
    · have hjlt : j < tau := by
        by_contra hnot
        have hjEq : j = tau := Nat.le_antisymm hjtau (le_of_not_gt hnot)
        subst j
        subst i
        simpa [ell] using hi
      have habove : z < (orbit j n : ℝ) := by
        by_contra hnot
        have hle : (orbit j n : ℝ) ≤ z := le_of_not_gt hnot
        have htauLe0 := shortcutFirstPassageTime_le hle
        have htauLe : tau ≤ j := by simpa [tau] using htauLe0
        omega
      subst i
      simpa [rawOrbit_rawTime_eq_orbit] using habove
    · rcases hintermediate with ⟨hjlt, hodd, hiEq⟩
      have hjNext : j + 1 ≤ tau := by omega
      have habove : z < 2 * (orbit (j + 1) n : ℝ) := by
        rcases lt_or_eq_of_le hjNext with hjNextLt | hjNextEq
        · have hnextAbove : z < (orbit (j + 1) n : ℝ) := by
            by_contra hnot
            have hle : (orbit (j + 1) n : ℝ) ≤ z := le_of_not_gt hnot
            have htauLe0 := shortcutFirstPassageTime_le hle
            have htauLe : tau ≤ j + 1 := by simpa [tau] using htauLe0
            omega
          have hnextPos : 0 < orbit (j + 1) n := orbit_pos hn _
          have hnextPosR : (0 : ℝ) < orbit (j + 1) n := by exact_mod_cast hnextPos
          nlinarith
        · simpa [hjNextEq] using hband.1
      subst i
      rw [rawOrbit_rawTime_add_one_eq_two_mul hodd]
      exact_mod_cast habove
  have hellLe : ell ≤ rawFirstPassageTime n z := by
    by_contra hnot
    have hlt : rawFirstPassageTime n z < ell := lt_of_not_ge hnot
    have habove := hnoEarlier _ hlt
    have hmem := rawFirstPassageTime_mem hellMem
    exact (not_le_of_gt habove) hmem
  have heq : rawFirstPassageTime n z = ell :=
    Nat.le_antisymm hrawLe hellLe
  constructor
  · simpa [ell] using heq
  · rw [heq]
    simpa [ell] using rawOrbit_rawTime_eq_orbit n tau

/-- A uniform shortcut trajectory tube gives the actual first-passage clock
to every intervening real level. -/
theorem shortcutFirstPassageTime_drift_profile
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ j : ℕ, j ≤ k → |shortcutLogDeviation n j| ≤ E) :
    |driftGap * (shortcutFirstPassageTime n z : ℝ) * Real.log 2 -
        Real.log ((n : ℝ) / z)| ≤ E + Real.log 2 := by
  let tau := shortcutFirstPassageTime n z
  have htauLe0 := shortcutFirstPassageTime_le hk
  have htauLe : tau ≤ k := by simpa [tau] using htauLe0
  have hband0 := shortcutFirstPassageTime_landingBand hzStart hk
  have hband : z < 2 * (orbit tau n : ℝ) ∧
      (orbit tau n : ℝ) ≤ z := by simpa [tau] using hband0
  have hlandNat : 0 < orbit tau n := orbit_pos hn tau
  have hland : (0 : ℝ) < orbit tau n := by exact_mod_cast hlandNat
  have hz : 0 < z := hland.trans_le hband.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogUpper := Real.log_le_log hland hband.2
  have hlogLower := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr hz)
    (Set.mem_Ioi.mpr (mul_pos (by norm_num) hland)) hband.1
  rw [Real.log_mul (by norm_num)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hlandNat))] at hlogLower
  have hdev := htube tau htauLe
  rw [shortcutLogDeviation] at hdev
  rw [Real.log_div hnR.ne' hz.ne', abs_le]
  have hdevBounds := abs_le.mp hdev
  constructor <;> nlinarith

/-- The same profile in the paper's clock normalization
`c_* = 1 / (driftGap * log 2)`. -/
theorem shortcutFirstPassageTime_centered_profile
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ j : ℕ, j ≤ k → |shortcutLogDeviation n j| ≤ E) :
    |(shortcutFirstPassageTime n z : ℝ) -
        fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
      fixedPolylogClockCritical * (E + Real.log 2) := by
  have hprofile := shortcutFirstPassageTime_drift_profile
    hn hzStart hk htube
  have hgapLog : 0 < driftGap * Real.log 2 :=
    mul_pos driftGap_pos (Real.log_pos (by norm_num))
  have hscale :
      (shortcutFirstPassageTime n z : ℝ) -
          fixedPolylogClockCritical * Real.log ((n : ℝ) / z) =
        fixedPolylogClockCritical *
          (driftGap * (shortcutFirstPassageTime n z : ℝ) * Real.log 2 -
            Real.log ((n : ℝ) / z)) := by
    unfold fixedPolylogClockCritical
    field_simp [hgapLog.ne', driftGap_pos.ne']
  rw [hscale, abs_mul,
    abs_of_pos fixedPolylogClockCritical_pos]
  exact mul_le_mul_of_nonneg_left hprofile fixedPolylogClockCritical_pos.le

/-- A uniform raw trajectory tube gives the actual raw first-passage clock.
The first raw and shortcut passages reach the same landing. -/
theorem rawFirstPassageTime_drift_profile
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ i : ℕ, i ≤ rawTime n k → |rawLogDeviation n i| ≤ E) :
    |(2 * driftGap / 3) * (rawFirstPassageTime n z : ℝ) * Real.log 2 -
        Real.log ((n : ℝ) / z)| ≤ E + Real.log 2 := by
  let tau := shortcutFirstPassageTime n z
  let ell := rawFirstPassageTime n z
  have hidentity :=
    rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime hn hzStart hk
  have hellEq : ell = rawTime n tau := by simpa [ell, tau] using hidentity.1
  have htauLe0 := shortcutFirstPassageTime_le hk
  have htauLe : tau ≤ k := by simpa [tau] using htauLe0
  have hellLe : ell ≤ rawTime n k := by
    rw [hellEq]
    exact (rawTime_strictMono n).monotone htauLe
  have hband0 := shortcutFirstPassageTime_landingBand hzStart hk
  have hband : z < 2 * (rawOrbit ell n : ℝ) ∧
      (rawOrbit ell n : ℝ) ≤ z := by
    have hlandingEq : rawOrbit ell n = orbit tau n := by
      simpa [ell, tau] using hidentity.2
    simpa [hlandingEq, tau] using hband0
  have hlandNat : 0 < rawOrbit ell n := by
    have horbitPos := orbit_pos hn tau
    have hlandingEq : rawOrbit ell n = orbit tau n := by
      simpa [ell, tau] using hidentity.2
    simpa [hlandingEq] using horbitPos
  have hland : (0 : ℝ) < rawOrbit ell n := by exact_mod_cast hlandNat
  have hz : 0 < z := hland.trans_le hband.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogUpper := Real.log_le_log hland hband.2
  have hlogLower := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr hz)
    (Set.mem_Ioi.mpr (mul_pos (by norm_num) hland)) hband.1
  rw [Real.log_mul (by norm_num)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hlandNat))] at hlogLower
  have hdev := htube ell hellLe
  rw [rawLogDeviation] at hdev
  rw [Real.log_div hnR.ne' hz.ne', abs_le]
  have hdevBounds := abs_le.mp hdev
  constructor <;> nlinarith

/-- Raw first-passage time in the paper's normalization
`(3/2) c_* log(n/z)`. -/
theorem rawFirstPassageTime_centered_profile
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ i : ℕ, i ≤ rawTime n k → |rawLogDeviation n i| ≤ E) :
    |(rawFirstPassageTime n z : ℝ) -
        (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
      (3 / 2) * fixedPolylogClockCritical * (E + Real.log 2) := by
  have hprofile := rawFirstPassageTime_drift_profile
    hn hzStart hk htube
  have hgapLog : 0 < driftGap * Real.log 2 :=
    mul_pos driftGap_pos (Real.log_pos (by norm_num))
  have hscale :
      (rawFirstPassageTime n z : ℝ) -
          (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z) =
        (3 / 2) * fixedPolylogClockCritical *
          ((2 * driftGap / 3) * (rawFirstPassageTime n z : ℝ) *
            Real.log 2 - Real.log ((n : ℝ) / z)) := by
    unfold fixedPolylogClockCritical
    field_simp [hgapLog.ne', driftGap_pos.ne']
  rw [hscale, abs_mul,
    abs_of_pos (mul_pos (by norm_num) fixedPolylogClockCritical_pos)]
  exact mul_le_mul_of_nonneg_left hprofile
    (mul_nonneg (by norm_num) fixedPolylogClockCritical_pos.le)

/-- Uniform shortcut and raw tubes give simultaneous actual first-passage
profiles to every level between the selected landing and the source. -/
theorem simultaneousFirstPassageTime_centered_profile
    {n k ell : ℕ} {z Eshort Eraw : ℝ}
    (hn : 0 < n)
    (hzLanding : (orbit k n : ℝ) ≤ z)
    (hzSource : z ≤ (n : ℝ))
    (hell : ell = rawTime n k)
    (hshortcut : ∀ j : ℕ, j ≤ k →
      |shortcutLogDeviation n j| ≤ Eshort)
    (hraw : ∀ i : ℕ, i ≤ ell →
      |rawLogDeviation n i| ≤ Eraw) :
    |(shortcutFirstPassageTime n z : ℝ) -
        fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
      |(rawFirstPassageTime n z : ℝ) -
        (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
        fixedPolylogClockCritical * (Eshort + Real.log 2) +
          (3 / 2) * fixedPolylogClockCritical * (Eraw + Real.log 2) ∧
      rawOrbit (rawFirstPassageTime n z) n =
        orbit (shortcutFirstPassageTime n z) n := by
  rcases hzSource.lt_or_eq with hzStart | hzEq
  · have hshort := shortcutFirstPassageTime_centered_profile
      hn hzStart hzLanding hshortcut
    have hrawTube : ∀ i : ℕ, i ≤ rawTime n k →
        |rawLogDeviation n i| ≤ Eraw := by
      intro i hi
      exact hraw i (by simpa [hell] using hi)
    have hrawProfile := rawFirstPassageTime_centered_profile
      hn hzStart hzLanding hrawTube
    have hid := rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
      hn hzStart hzLanding
    exact ⟨add_le_add hshort hrawProfile, hid.2⟩
  · subst z
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hshort0 := shortcutFirstPassageTime_self (n := n)
    have hraw0 := rawFirstPassageTime_self (n := n)
    have hlog0 : Real.log ((n : ℝ) / (n : ℝ)) = 0 := by
      rw [div_self hnR, Real.log_one]
    constructor
    · rw [hshort0, hraw0, hlog0]
      norm_num
      have hlogTwo0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      have hc0 : 0 ≤ fixedPolylogClockCritical :=
        fixedPolylogClockCritical_pos.le
      have hEshort0 : 0 ≤ Eshort := by
        have hzero := hshortcut 0 (Nat.zero_le k)
        simpa [shortcutLogDeviation] using (abs_nonneg (shortcutLogDeviation n 0)).trans hzero
      have hEraw0 : 0 ≤ Eraw := by
        have hzero := hraw 0 (Nat.zero_le ell)
        exact (abs_nonneg (rawLogDeviation n 0)).trans hzero
      positivity
    · simp [hshort0, hraw0, rawOrbit_zero]

/-- Every prefix of one certified high block lies in its deterministic
logarithmic tube. -/
theorem abs_shortcutLogDeviation_le_of_initialWindowGood
    {t : ℝ} {n j : ℕ}
    (hn : 0 < n)
    (hnGood : n ∈ initialWindowGood t)
    (hj : j ≤ Nat.log 2 n) :
    |shortcutLogDeviation n j| ≤ t * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have horbit : 0 < orbit j n := orbit_pos hn j
  have horbitR : (0 : ℝ) < orbit j n := by exact_mod_cast horbit
  have henv := hnGood j hj
  have hlowerLog := Real.log_le_log
    (mul_pos (centralOrbitScale_pos j)
      (Real.rpow_pos_of_pos hnR (1 - t))) henv.1
  have hupperLog := Real.log_le_log horbitR henv.2
  rw [Real.log_mul (centralOrbitScale_pos j).ne'
      (Real.rpow_pos_of_pos hnR (1 - t)).ne',
    centralOrbitScale_eq_two_rpow_neg_gap,
    Real.log_rpow (by norm_num), Real.log_rpow hnR] at hlowerLog
  rw [Real.log_mul (centralOrbitScale_pos j).ne'
      (Real.rpow_pos_of_pos hnR (1 + t)).ne',
    centralOrbitScale_eq_two_rpow_neg_gap,
    Real.log_rpow (by norm_num), Real.log_rpow hnR] at hupperLog
  rw [shortcutLogDeviation, abs_le]
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  constructor <;> nlinarith [Real.log_nonneg hn1]

/-- The elementary one-step bounds give a coarse logarithmic tube without
any parity certificate.  This is used only inside the short low-rank tail. -/
theorem abs_shortcutLogDeviation_le_two_mul
    {n j : ℕ} (hn : 0 < n) :
    |shortcutLogDeviation n j| ≤ 2 * (j : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have horbit : 0 < orbit j n := orbit_pos hn j
  have horbitR : (0 : ℝ) < orbit j n := by exact_mod_cast horbit
  have hcorr := normalizedCorrection_nonneg j n
  have hthree : (1 : ℝ) ≤ (3 : ℝ) ^ oddCount n j := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hlower : (n : ℝ) / (2 : ℝ) ^ j ≤ (orbit j n : ℝ) := by
    rw [orbit_eq_normalizedCorrection]
    have hbase : (n : ℝ) / (2 : ℝ) ^ j ≤
        (n : ℝ) / (2 : ℝ) ^ j + normalizedCorrection j n :=
      le_add_of_nonneg_right hcorr
    exact hbase.trans (le_mul_of_one_le_right (by positivity) hthree)
  have hlowerPos : 0 < (n : ℝ) / (2 : ℝ) ^ j := by positivity
  have hlowerLog := Real.log_le_log hlowerPos hlower
  have hupperNat := orbit_le_two_pow_mul j n
  have hupper : (orbit j n : ℝ) ≤ (2 : ℝ) ^ j * (n : ℝ) := by
    exact_mod_cast hupperNat
  have hupperLog := Real.log_le_log horbitR hupper
  rw [Real.log_div hnR.ne' (by positivity), Real.log_pow] at hlowerLog
  rw [Real.log_mul (by positivity : (0 : ℝ) < (2 : ℝ) ^ j).ne' hnR.ne',
    Real.log_pow] at hupperLog
  have hlogTwo0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwo1 : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hgap0 := driftGap_pos
  have hgap1 : driftGap < 1 := by
    unfold driftGap
    linarith [a0_pos]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [shortcutLogDeviation, abs_le]
  constructor <;> nlinarith

/-- Every exact reverse step factor lies in the unit interval. -/
theorem reverseStepFactor_mem_unitInterval
    {n i : ℕ} (hn : 0 < n) :
    0 ≤ reverseStepFactor n i ∧ reverseStepFactor n i ≤ 1 := by
  rw [reverseStepFactor_eq_one_sub_reverseLoss]
  constructor
  · linarith [reverseLoss_le_one hn i]
  · linarith [reverseLoss_nonneg n i]

/-- Reverse products can only decrease when a shortcut prefix is extended. -/
theorem reverseProduct_antitone
    {n a b : ℕ} (hn : 0 < n) (hab : a ≤ b) :
    reverseProduct n b ≤ reverseProduct n a := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      simp [ha]
  | succ b ih =>
      by_cases hab' : a ≤ b
      · have hfactor := reverseStepFactor_mem_unitInterval (n := n) (i := b) hn
        have hprod0 : 0 ≤ reverseProduct n b := by
          rw [reverseProduct_eq_prod_loss]
          apply Finset.prod_nonneg
          intro i hi
          linarith [reverseLoss_le_one hn i]
        rw [show b + 1 = Nat.succ b by omega, reverseProduct_succ]
        exact (mul_le_of_le_one_right hprod0 hfactor.2).trans (ih hab')
      · have ha : a = b + 1 := by omega
        simpa [ha]

/-- The exact reverse identity converts a prefix lower bound for the reverse
product and a shortcut logarithmic tube into a centered odd-count tube. -/
theorem oddCount_centered_of_reverseProduct_half
    {n j : ℕ} {E : ℝ}
    (hn : 0 < n)
    (hP : (1 / 2 : ℚ) ≤ reverseProduct n j)
    (hdev : |shortcutLogDeviation n j| ≤ E) :
    |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
      (E + Real.log 2) / Real.log 3 := by
  have horbit : 0 < orbit j n := orbit_pos hn j
  have hPposQ : (0 : ℚ) < reverseProduct n j :=
    (by norm_num : (0 : ℚ) < 1 / 2).trans_le hP
  have hPpos : (0 : ℝ) < (reverseProduct n j : ℝ) := by
    exact_mod_cast hPposQ
  have hPupQ := reverseProduct_le_one hn j
  have hPup : (reverseProduct n j : ℝ) ≤ 1 := by exact_mod_cast hPupQ
  have hidQ := reverse_product_identity hn j
  have hidR : (n : ℝ) =
      (((2 : ℝ) ^ j * (orbit j n : ℝ)) /
        (3 : ℝ) ^ oddCount n j) * (reverseProduct n j : ℝ) := by
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hidQ
    norm_num only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow] at hcast
    exact hcast
  have hlogId := congrArg Real.log hidR
  rw [Real.log_mul (by positivity) hPpos.ne',
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt horbit)),
    Real.log_pow, Real.log_pow] at hlogId
  have hPcast : (((1 / 2 : ℚ) : ℝ)) ≤ (reverseProduct n j : ℝ) :=
    Rat.cast_le.2 hP
  norm_num at hPcast
  have hlogPLo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hPcast
  have hlogPUp := Real.log_nonpos hPpos.le hPup
  rw [show (1 / 2 : ℝ) = 1 / 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_one] at hlogPLo
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgaplog : driftGap * Real.log 2 =
      Real.log 2 - Real.log 3 / 2 := by
    unfold driftGap a0 logTwoThree
    field_simp [hlog2.ne']
  have hidentity :
      ((oddCount n j : ℝ) - (j : ℝ) / 2) * Real.log 3 =
        shortcutLogDeviation n j + Real.log (reverseProduct n j : ℝ) := by
    rw [shortcutLogDeviation]
    nlinarith
  have hdevBounds := abs_le.mp hdev
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hlog3]
    rw [hidentity]
    nlinarith
  · rw [le_div_iff₀ hlog3]
    rw [hidentity]
    nlinarith

/-- The local tube of a certified high stage is no wider than the duration
error charged by the existing time-support potential. -/
theorem abs_shortcutLogDeviation_highStage_le_durationError
    (P : TimeoutHighRunData) {M m x j : ℕ}
    (hm0 : P.pHi.M0 ≤ m)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood (timeoutHighTolerance P M m))
    (hj : j ≤ stageLength (timeoutHighSetup P M m) x) :
    |shortcutLogDeviation x j| ≤
      timeoutDurationError (timeoutHighTolerance P M m) m := by
  have hx : 0 < x := by
    have hxLower := (mem_dyadicShell.mp hxShell).1
    have hpow : 0 < 2 ^ m := by positivity
    omega
  have hjm := hj.trans
    (stageLength_le_shell (timeoutHighSetup P M m) hm0 hxShell hxGood)
  have hjlog : j ≤ Nat.log 2 x := by
    simpa [log_two_eq_of_mem_dyadicShell hxShell] using hjm
  have hlocal := abs_shortcutLogDeviation_le_of_initialWindowGood
    hx hxGood hjlog
  have hxUpperNat := (mem_dyadicShell.mp hxShell).2
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxUpperR : (x : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast hxUpperNat
  have hlogUpper := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr hxR)
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ)))
    hxUpperR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlogUpper
  rw [Real.log_pow] at hlogUpper
  have ht0 := (timeoutHighTolerance_pos P M m).le
  have hlogTwo0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwo1 : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hm0R : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have htlog := mul_le_mul_of_nonneg_left hlogUpper.le ht0
  have hprod0 : 0 ≤ timeoutHighTolerance P M m * ((m : ℝ) + 1) :=
    mul_nonneg ht0 (by linarith)
  have hscaled :
      timeoutHighTolerance P M m * (((m : ℝ) + 1) * Real.log 2) ≤
        timeoutHighTolerance P M m * ((m : ℝ) + 1) := by
    calc
      _ = (timeoutHighTolerance P M m * ((m : ℝ) + 1)) * Real.log 2 := by ring
      _ ≤ (timeoutHighTolerance P M m * ((m : ℝ) + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hlogTwo1.le hprod0
      _ = _ := by ring
  rw [timeoutDurationError]
  push_cast at hlogUpper htlog
  nlinarith

/-- Every shortcut prefix of a mixed timeout run stays in one common
square-root-logarithmic tube.  The factor two lets the same potential pay the
coarse low-block estimate `|deviation| ≤ 2 duration`. -/
theorem TimeoutRecertificationRun.prefix_log_deviation_add_potential_le
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    ∀ j : ℕ, j ≤ elapsed →
      |shortcutLogDeviation n j| + 2 * timeoutTimePotential P M S q ≤
        2 * timeoutTimePotential P M S (M + 1) := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      intro j hj
      have hlocal := abs_shortcutLogDeviation_highStage_le_durationError
        P hM0 hnShell hnGood hj
      have hq : (rationalTargetRank P.rHi M : ℝ) ≤
          (P.rHi : ℝ) * (M : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (M : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg M)
        exact Nat.floor_le hnonneg
      have hstep := timeoutTimePotential_high_step P
        (S := S) (m := M) (q := rationalTargetRank P.rHi M)
        hM hM hSM hq
      have hcost0 : 0 ≤
          timeoutDurationError (timeoutHighTolerance P M M) M := by
        have ht0 := (timeoutHighTolerance_pos P M M).le
        have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        unfold timeoutDurationError
        nlinarith [mul_nonneg ht0 hM0]
      nlinarith
  | @nextHi elapsed qPrev m hrun hSm hm0 hmPrev hsourceShell hsourceGood
      hgap ih =>
      intro j hj
      have hq : (rationalTargetRank P.rHi m : ℝ) ≤
          (P.rHi : ℝ) * (m : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (m : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg m)
        exact Nat.floor_le hnonneg
      have hm1 : 1 ≤ m := P.pHi.M0_pos.trans hm0
      have hstep0 := timeoutTimePotential_high_step P
        (M := M) (S := S) (m := m) (q := rationalTargetRank P.rHi m)
        hM hm1 hSm hq
      have hstep :
          timeoutDurationError (timeoutHighTolerance P M m) m +
              timeoutTimePotential P M S (rationalTargetRank P.rHi m) ≤
            timeoutTimePotential P M S qPrev := by
        simpa [hmPrev] using hstep0
      have hcost0 : 0 ≤
          timeoutDurationError (timeoutHighTolerance P M m) m := by
        have ht0 := (timeoutHighTolerance_pos P M m).le
        have hm0R : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        unfold timeoutDurationError
        nlinarith [mul_nonneg ht0 hm0R]
      by_cases hjOld : j ≤ elapsed
      · have hIH := ih j hjOld
        nlinarith
      · let u := j - elapsed
        have hjForm : j = u + elapsed := by
          dsimp [u]
          omega
        have huStage : u ≤
            stageLength (timeoutHighSetup P M m) (orbit elapsed n) := by
          dsimp [u]
          omega
        have hlocal := abs_shortcutLogDeviation_highStage_le_durationError
          P hm0 hsourceShell hsourceGood huStage
        have hIH := ih elapsed le_rfl
        have hadd := shortcutLogDeviation_add n elapsed u
        have habs := abs_add_le (shortcutLogDeviation n elapsed)
          (shortcutLogDeviation (orbit elapsed n) u)
        rw [← hadd, ← hjForm] at habs
        nlinarith

  | @nextLo elapsed qPrev m hrun hmS hLm hmPrevLo hmPrevHi hsourceShell
      hpass hqpos hqparent hgap ih =>
      intro j hj
      let qNext := timeoutTargetRank K₀ L m
      have hqLow : ¬S < qNext := by
        dsimp [qNext]
        omega
      have hprevLow : ¬S < qPrev := by omega
      have hmR : (m : ℝ) ≤ qPrev := by exact_mod_cast hmPrevLo
      have hqR : (qNext : ℝ) + 1 ≤ m := by
        dsimp [qNext]
        exact_mod_cast hqparent
      have hSR : (m : ℝ) + 1 ≤ S := by exact_mod_cast hmS
      have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
      have hpay : (m : ℝ) + timeoutTimePotential P M S qNext ≤
          timeoutTimePotential P M S qPrev := by
        simp only [timeoutTimePotential, if_neg hqLow, if_neg hprevLow]
        nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hqR)]
      by_cases hjOld : j ≤ elapsed
      · have hIH := ih j hjOld
        have hm0Real : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      · let u := j - elapsed
        have hjForm : j = u + elapsed := by
          dsimp [u]
          omega
        have huDuration : u ≤ hpass.duration := by
          dsimp [u]
          omega
        have hsourcePos : 0 < orbit elapsed n := by
          have hsourceLower := (mem_dyadicShell.mp hsourceShell).1
          have hpow : 0 < 2 ^ m := by positivity
          omega
        have hlocal := abs_shortcutLogDeviation_le_two_mul
          (n := orbit elapsed n) (j := u) hsourcePos
        have huM : (u : ℝ) ≤ m := by
          exact_mod_cast huDuration.trans hpass.duration_le
        have hIH := ih elapsed le_rfl
        have hadd := shortcutLogDeviation_add n elapsed u
        have habs := abs_add_le (shortcutLogDeviation n elapsed)
          (shortcutLogDeviation (orbit elapsed n) u)
        rw [← hadd, ← hjForm] at habs
        nlinarith

/-- The run-wide shortcut tube has the same
`sqrt(M log M)` scale as the feasible-time support. -/
theorem eventually_timeoutRun_prefix_log_deviation_le_sqrt
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      ∀ j : ℕ, j ≤ elapsed →
        |shortcutLogDeviation n j| ≤
          timeoutTimeSupportConstant P C *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutTimePotential_source_le_sqrt P hC,
      eventually_ge_atTop (1 : ℕ)] with M hsupport hM
  intro L n elapsed q hrun j hj
  have htube := hrun.prefix_log_deviation_add_potential_le hM j hj
  have hqPot0 := timeoutTimePotential_nonneg P M
    (shrinkingSwitchRank C M) q
  have hsourcePot0 := timeoutTimePotential_nonneg P M
    (shrinkingSwitchRank C M) (M + 1)
  have hgap1 : driftGap ≤ 1 := by
    unfold driftGap
    linarith [a0_pos]
  have hdiv :
      2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := by
    rw [le_div_iff₀ driftGap_pos]
    nlinarith [mul_nonneg hsourcePot0 driftGap_pos.le]
  have hsourceBound :
      2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
    calc
      _ ≤ 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := hdiv
      _ ≤ 1 + 2 * timeoutTimePotential P M
          (shrinkingSwitchRank C M) (M + 1) / driftGap := by linarith
      _ ≤ _ := hsupport
  linarith

/-- Adding at most the switch rank of final shortcut steps preserves the
trajectory-tube scale.  This covers the exact-halving completion used when a
timeout run lands at a dyadic upper endpoint. -/
theorem eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q v : ℕ},
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      v ≤ shrinkingSwitchRank C M →
      ∀ j : ℕ, j ≤ elapsed + v →
        |shortcutLogDeviation n j| ≤
          2 * timeoutTimeSupportConstant P C *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutRun_prefix_log_deviation_le_sqrt P hC,
      eventually_timeoutTimePotential_source_le_sqrt P hC,
      eventually_shrinkingSwitchRank_lt_source hC,
      eventually_ge_atTop (1 : ℕ)]
    with M htube hsupport hswitch hM
  intro L n elapsed q v hrun hv j hj
  let S := shrinkingSwitchRank C M
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
  have htime0 : 0 < timeoutTimeSupportConstant P C :=
    timeoutTimeSupportConstant_pos P C
  have hsourcePot0 := timeoutTimePotential_nonneg P M S (M + 1)
  have hgap1 : driftGap ≤ 1 := by
    unfold driftGap
    linarith [a0_pos]
  have hdiv : 2 * timeoutTimePotential P M S (M + 1) ≤
      2 * timeoutTimePotential P M S (M + 1) / driftGap := by
    rw [le_div_iff₀ driftGap_pos]
    nlinarith [mul_nonneg hsourcePot0 driftGap_pos.le]
  have hpotBound : 2 * timeoutTimePotential P M S (M + 1) ≤
      timeoutTimeSupportConstant P C * root := by
    calc
      _ ≤ 2 * timeoutTimePotential P M S (M + 1) / driftGap := hdiv
      _ ≤ 1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap := by
        linarith
      _ ≤ _ := by simpa [S, root] using hsupport
  have hswitchSq : (S : ℝ) ^ 2 ≤
      timeoutTimePotential P M S (M + 1) := by
    apply timeout_switch_sq_le_source_potential
    dsimp [S]
    exact hswitch.trans (Nat.lt_succ_self M)
  have hSbound : 2 * (S : ℝ) ≤
      timeoutTimeSupportConstant P C * root := by
    have htwoS : 2 * (S : ℝ) ≤ 1 + (S : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((S : ℝ) - 1)]
    have honePot : 1 + (S : ℝ) ^ 2 ≤
        1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap := by
      have hpotDiv : timeoutTimePotential P M S (M + 1) ≤
          2 * timeoutTimePotential P M S (M + 1) / driftGap := by
        rw [le_div_iff₀ driftGap_pos]
        nlinarith [mul_nonneg hsourcePot0 driftGap_pos.le]
      linarith
    exact htwoS.trans (honePot.trans (by simpa [S, root] using hsupport))
  by_cases hjOld : j ≤ elapsed
  · have h := htube hrun j hjOld
    nlinarith [mul_nonneg htime0.le hroot0]
  · let u := j - elapsed
    have hjForm : j = u + elapsed := by
      dsimp [u]
      omega
    have huV : u ≤ v := by
      dsimp [u]
      omega
    have huS : (u : ℝ) ≤ S := by
      exact_mod_cast huV.trans hv
    have hn : 0 < n := by
      have hnShell := hrun.source_mem_dyadicShell
      have hnLower := (mem_dyadicShell.mp hnShell).1
      have hpow : 0 < 2 ^ M := by positivity
      omega
    have hlocal := abs_shortcutLogDeviation_le_two_mul
      (n := orbit elapsed n) (j := u) (orbit_pos hn elapsed)
    have hbase := htube hrun elapsed le_rfl
    have hadd := shortcutLogDeviation_add n elapsed u
    have habs := abs_add_le (shortcutLogDeviation n elapsed)
      (shortcutLogDeviation (orbit elapsed n) u)
    rw [← hadd, ← hjForm] at habs
    nlinarith

/-- The switch rank itself is negligible on the trajectory-tube scale. -/
theorem eventually_two_shrinkingSwitchRank_le_timeoutSupportRoot
    (P : TimeoutHighRunData) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      2 * (shrinkingSwitchRank C M : ℝ) ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutTimePotential_source_le_sqrt P hC,
      eventually_shrinkingSwitchRank_lt_source hC]
    with M hsupport hswitch
  let S := shrinkingSwitchRank C M
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hsourcePot0 := timeoutTimePotential_nonneg P M S (M + 1)
  have hswitchSq : (S : ℝ) ^ 2 ≤
      timeoutTimePotential P M S (M + 1) := by
    apply timeout_switch_sq_le_source_potential
    dsimp [S]
    exact hswitch.trans (Nat.lt_succ_self M)
  have htwoS : 2 * (S : ℝ) ≤ 1 + (S : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((S : ℝ) - 1)]
  have hpotDiv : timeoutTimePotential P M S (M + 1) ≤
      2 * timeoutTimePotential P M S (M + 1) / driftGap := by
    rw [le_div_iff₀ driftGap_pos]
    have hgap1 : driftGap ≤ 1 := by
      unfold driftGap
      linarith [a0_pos]
    nlinarith [mul_nonneg hsourcePot0 driftGap_pos.le]
  calc
    2 * (S : ℝ) ≤ 1 + (S : ℝ) ^ 2 := htwoS
    _ ≤ 1 + 2 * timeoutTimePotential P M S (M + 1) / driftGap := by
      linarith
    _ ≤ _ := by simpa [S, root] using hsupport

/-- On the moving-endpoint good route, the same prefix set also has a
centered odd-count profile.  No additional exceptional event is introduced:
the final reverse-product lower bound propagates backwards to every prefix. -/
theorem eventually_timeoutRun_prefix_oddCount_centered
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      ∀ j : ℕ, j ≤ elapsed →
        |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
          (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) +
            Real.log 2) / Real.log 3 := by
  filter_upwards [eventually_timeoutRun_reverseProduct_half P hbuffer,
      eventually_timeoutRun_prefix_log_deviation_le_sqrt
        P.run.toTimeoutHigh P.Cswitch_pos.le]
    with M hreverse htube
  intro n elapsed q hrun j hj
  have hnShell := hrun.source_mem_dyadicShell
  have hn : 0 < n := by
    have hnLower := (mem_dyadicShell.mp hnShell).1
    have hpow : 0 < 2 ^ M := by positivity
    omega
  have hfinal := hreverse hrun
  have hprefixMono := reverseProduct_antitone hn hj
  have hprefix : (1 / 2 : ℚ) ≤ reverseProduct n j :=
    hfinal.trans hprefixMono
  exact oddCount_centered_of_reverseProduct_half hn hprefix
    (htube hrun j hj)

/-- Explicit square-root-logarithmic support constant for the run-wide
centered odd-count tube. -/
def timeoutOddTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  (timeoutTimeSupportConstant P C + 1) / Real.log 3

theorem timeoutOddTrajectorySupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutOddTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hlog3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  unfold timeoutOddTrajectorySupportConstant
  positivity

/-- Constant-times-root form of the run-wide odd-count profile. -/
theorem eventually_timeoutRun_prefix_oddCount_centered_le_sqrt
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      ∀ j : ℕ, j ≤ elapsed →
        |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
          timeoutOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutRun_prefix_oddCount_centered P hbuffer,
      eventually_ge_atTop (1 : ℕ)] with M hodd hM
  intro n elapsed q hrun j hj
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have h := hodd hrun j hj
  have hroot1 : 1 ≤ root := by
    simpa [root] using one_le_timeoutProfileRoot hM
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hnum : timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
        root + Real.log 2 ≤
      (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
        root := by
    nlinarith
  unfold timeoutOddTrajectorySupportConstant
  calc
    _ ≤ (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root +
        Real.log 2) / Real.log 3 := h
    _ ≤ ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
        root) / Real.log 3 :=
      (div_le_div_iff_of_pos_right hlog3).2 hnum
    _ = (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) /
        Real.log 3 * root := by ring

/-- Explicit support constant for the centered odd-count profile after the
optional exact-halving completion. -/
def timeoutCompletedOddTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  timeoutOddTrajectorySupportConstant P C +
    timeoutTimeSupportConstant P C

theorem timeoutCompletedOddTrajectorySupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutCompletedOddTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hlog3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  unfold timeoutCompletedOddTrajectorySupportConstant
  exact add_pos (timeoutOddTrajectorySupportConstant_pos P C) htime

theorem timeoutOddTrajectorySupportConstant_le_completed
    (P : TimeoutHighRunData) (C : ℝ) :
    timeoutOddTrajectorySupportConstant P C ≤
      timeoutCompletedOddTrajectorySupportConstant P C := by
  rw [timeoutCompletedOddTrajectorySupportConstant]
  linarith [timeoutTimeSupportConstant_pos P C]

/-- The odd-count tube persists through the exact-halving completion used by
the selected endpoint witness. -/
theorem eventually_timeoutRun_completed_oddCount_centered_le_sqrt
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q v : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      orbit elapsed n = 2 ^ q →
      v ≤ q → v ≤ shrinkingSwitchRank P.Cswitch M →
      ∀ j : ℕ, j ≤ elapsed + v →
        |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
          timeoutCompletedOddTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutRun_prefix_oddCount_centered P hbuffer,
      eventually_two_shrinkingSwitchRank_le_timeoutSupportRoot
        P.run.toTimeoutHigh P.Cswitch_pos.le,
      eventually_ge_atTop (1 : ℕ)]
    with M hbase hswitch hM
  intro n elapsed q v hrun heq hvq hvS j hj
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let E := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root
  let F := (E + Real.log 2) / Real.log 3
  have hcompleted := completed_oddCount_centered_le
    (S := shrinkingSwitchRank P.Cswitch M) (F := F)
    heq hvq hvS (fun u hu => by simpa [F, E, root] using hbase hrun u hu)
    j hj
  have hroot1 : 1 ≤ root := by
    simpa [root] using one_le_timeoutProfileRoot hM
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have htime0 := timeoutTimeSupportConstant_pos
    P.run.toTimeoutHigh P.Cswitch
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hFscale : F ≤
      ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) /
        Real.log 3) * root := by
    have hnum : E + Real.log 2 ≤
        (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          root := by
      dsimp [E]
      nlinarith
    calc
      F = (E + Real.log 2) / Real.log 3 := rfl
      _ ≤ ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          root) / Real.log 3 :=
        (div_le_div_iff_of_pos_right hlog3).2 hnum
      _ = ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) /
          Real.log 3) * root := by ring
  have hSscale : (shrinkingSwitchRank P.Cswitch M : ℝ) / 2 ≤
      timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
    nlinarith
  have hFscale' : F ≤
      timeoutOddTrajectorySupportConstant P.run.toTimeoutHigh P.Cswitch *
        root := by
    simpa [timeoutOddTrajectorySupportConstant] using hFscale
  calc
    |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
        F + (shrinkingSwitchRank P.Cswitch M : ℝ) / 2 := hcompleted
    _ ≤ timeoutOddTrajectorySupportConstant P.run.toTimeoutHigh P.Cswitch *
          root + timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
            root := add_le_add hFscale' hSscale
    _ = timeoutCompletedOddTrajectorySupportConstant
          P.run.toTimeoutHigh P.Cswitch * root := by
      rw [timeoutCompletedOddTrajectorySupportConstant]
      ring

/-- Explicit support constant for the complete raw trajectory tube after an
optional exact-halving completion. -/
def timeoutCompletedRawTrajectorySupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  2 * timeoutTimeSupportConstant P C +
    rawOddDeviationCoefficient *
      timeoutCompletedOddTrajectorySupportConstant P C + 1

theorem timeoutCompletedRawTrajectorySupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutCompletedRawTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hcoef := rawOddDeviationCoefficient_nonneg
  have hodd := timeoutCompletedOddTrajectorySupportConstant_pos P C
  unfold timeoutCompletedRawTrajectorySupportConstant
  positivity

theorem timeoutRawTrajectorySupportConstant_le_completed
    (P : TimeoutHighRunData) (C : ℝ) :
    timeoutRawTrajectorySupportConstant P C ≤
      timeoutCompletedRawTrajectorySupportConstant P C := by
  have htime := timeoutTimeSupportConstant_pos P C
  have hcoef := rawOddDeviationCoefficient_nonneg
  have hoddLe := timeoutOddTrajectorySupportConstant_le_completed P C
  have hoddLe' : (timeoutTimeSupportConstant P C + 1) / Real.log 3 ≤
      timeoutCompletedOddTrajectorySupportConstant P C := by
    simpa [timeoutOddTrajectorySupportConstant] using hoddLe
  rw [timeoutRawTrajectorySupportConstant,
    timeoutCompletedRawTrajectorySupportConstant]
  nlinarith [mul_le_mul_of_nonneg_left hoddLe' hcoef]

/-- Every raw state through the selected completion witness lies in the raw
trajectory tube on the same timeout-good set. -/
theorem eventually_timeoutRun_completed_raw_log_deviation_le_sqrt
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q v : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      orbit elapsed n = 2 ^ q →
      v ≤ q → v ≤ shrinkingSwitchRank P.Cswitch M →
      ∀ i : ℕ, i ≤ rawTime n (elapsed + v) →
        |rawLogDeviation n i| ≤
          timeoutCompletedRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutRun_completed_prefix_log_deviation_le_sqrt
        P.run.toTimeoutHigh P.Cswitch_pos.le,
      eventually_timeoutRun_completed_oddCount_centered_le_sqrt P hbuffer,
      eventually_ge_atTop (1 : ℕ)]
    with M hshortcut hodd hM
  intro n elapsed q v hrun heq hvq hvS i hi
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let E := 2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root
  let F := timeoutCompletedOddTrajectorySupportConstant
    P.run.toTimeoutHigh P.Cswitch * root
  have hn : 0 < n := by
    have hnShell := hrun.source_mem_dyadicShell
    have hnLower := (mem_dyadicShell.mp hnShell).1
    have hpow : 0 < 2 ^ M := by positivity
    omega
  have hraw := rawPrefix_log_deviation_le
    (n := n) (k := elapsed + v) (E := E) (F := F) hn
    (fun j hj => by simpa [E, root] using hshortcut hrun hvS j hj)
    (fun j hj => by simpa [F, root] using hodd hrun heq hvq hvS j hj)
    i hi
  have hroot1 : 1 ≤ root := by
    simpa [root] using one_le_timeoutProfileRoot hM
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hcoef0 := rawOddDeviationCoefficient_nonneg
  have htime0 := timeoutTimeSupportConstant_pos
    P.run.toTimeoutHigh P.Cswitch
  have hodd0 := timeoutCompletedOddTrajectorySupportConstant_pos
    P.run.toTimeoutHigh P.Cswitch
  dsimp [timeoutCompletedRawTrajectorySupportConstant]
  dsimp [E, F, root] at hraw ⊢
  nlinarith [mul_nonneg hcoef0 hodd0.le]

/-- Every raw prefix of a moving-endpoint timeout run lies in a uniform
`sqrt(M log M)` tube on exactly the same good set. -/
theorem eventually_timeoutRun_prefix_raw_log_deviation_le_sqrt
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      ∀ i : ℕ, i ≤ rawTime n elapsed →
        |rawLogDeviation n i| ≤
          timeoutRawTrajectorySupportConstant
              P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutRun_prefix_log_deviation_le_sqrt
        P.run.toTimeoutHigh P.Cswitch_pos.le,
      eventually_timeoutRun_prefix_oddCount_centered P hbuffer,
      eventually_ge_atTop (1 : ℕ)]
    with M hshortcut hodd hM
  intro n elapsed q hrun i hi
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let E := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root
  let F := (E + Real.log 2) / Real.log 3
  have hraw := rawPrefix_log_deviation_le
    (n := n) (k := elapsed) (E := E) (F := F)
    (by
      have hnShell := hrun.source_mem_dyadicShell
      have hnLower := (mem_dyadicShell.mp hnShell).1
      have hpow : 0 < 2 ^ M := by positivity
      omega)
    (fun j hj => by simpa [E, root] using hshortcut hrun j hj)
    (fun j hj => by simpa [F, E, root] using hodd hrun j hj)
    i hi
  have hroot1 : 1 ≤ root := by
    simpa [root] using one_le_timeoutProfileRoot hM
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    (Real.log_two_lt_d9.trans (by norm_num)).le
  have hcoef0 := rawOddDeviationCoefficient_nonneg
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htime0 : 0 < timeoutTimeSupportConstant
      P.run.toTimeoutHigh P.Cswitch :=
    timeoutTimeSupportConstant_pos _ _
  have hroot0 : 0 ≤ root := by linarith
  have hnum : E + Real.log 2 ≤
      (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
        root := by
    dsimp [E]
    nlinarith
  have hFscale : F ≤
      ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) /
          Real.log 3) * root := by
    calc
      F = (E + Real.log 2) / Real.log 3 := rfl
      _ ≤ ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          root) / Real.log 3 :=
        (div_le_div_iff_of_pos_right hlog3).2 hnum
      _ = ((timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) /
          Real.log 3) * root := by ring
  have hcoefF := mul_le_mul_of_nonneg_left hFscale hcoef0
  dsimp [timeoutRawTrajectorySupportConstant]
  dsimp [E, F, root] at hraw ⊢
  nlinarith [mul_nonneg htime0.le hroot0]

end

end FirstPassageLinearTransport
