/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutCore

/-!
# Exact timeout target counting

The timeout implication from `TimeoutCore` is converted here into an exact
upper binomial tail on every complete dyadic shell.  This module contains no
generated-run or transport argument.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

noncomputable section

/-- The Boolean support of the actual parity word has cardinality equal to
the number of odd shortcut states. -/
theorem card_boolSupport_boolParityWord (m n : ℕ) :
    (boolSupport (boolParityWord m n)).card = oddCount n m := by
  have hfin : ∀ b : Fin 2,
      (if finTwoEquiv b = true then 1 else 0) = (b : ℕ) := by
    intro b
    fin_cases b <;> rfl
  unfold boolSupport boolParityWord oddCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ i : Fin m,
        if finTwoEquiv (parityBit n i) = true then 1 else 0) =
        ∑ i : Fin m, (parityBit n i : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hfin (parityBit n i)
    _ = ∑ i ∈ Finset.range m, (parityBit n i : ℕ) := by
      simpa using
        (Fin.sum_univ_eq_sum_range (fun i => (parityBit n i : ℕ)) m)

/-- Odd count depends only on the first `m` residue bits. -/
theorem oddCount_eq_of_modEq {m n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ m]) :
    oddCount n m = oddCount n' m := by
  have hp := parityPrefix_congr h
  unfold oddCount
  apply Finset.sum_congr rfl
  intro i hi
  have hii : i < m := Finset.mem_range.mp hi
  have hbit := congrFun hp ⟨i, hii⟩
  exact congrArg Fin.val hbit

/-- Residues whose terminal parity word contains at least `k` odd states. -/
noncomputable def terminalOddUpperResidues (m k : ℕ) :
    Finset (Fin (2 ^ m)) := by
  classical
  exact Finset.univ.filter fun x => k ≤ oddCount x m

/-- Shell sources whose terminal parity word contains at least `k` odd
states. -/
noncomputable def terminalOddUpperShell (m k : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell m).filter fun x => k ≤ oddCount x m

/-- Exact binomial law for the terminal odd count on a complete residue
block. -/
theorem card_terminalOddUpperResidues {m k : ℕ} (hk : k ≤ m) :
    (terminalOddUpperResidues m k).card = binomialUpperTail m k := by
  classical
  let e₁ :
      {x : Fin (2 ^ m) // k ≤ oddCount x m} ≃
        {v : Fin m → Bool // k ≤ (boolSupport v).card} :=
    (boolParityEquiv m).subtypeEquiv fun x => by
      rw [boolParityEquiv_apply, boolParityCode_eq_word,
        card_boolSupport_boolParityWord]
  let e₂ :
      {v : Fin m → Bool // k ≤ (boolSupport v).card} ≃
        {s : Finset (Fin m) // k ≤ s.card} :=
    (boolWordFinsetEquiv m).subtypeEquiv fun _v => Iff.rfl
  have hc := Fintype.card_congr (e₁.trans e₂)
  rw [card_finsets_card_ge m k hk] at hc
  simpa [terminalOddUpperResidues, Fintype.card_subtype] using hc

/-- Exact binomial law for the terminal odd count on a complete dyadic
shell. -/
theorem card_terminalOddUpperShell {m k : ℕ} (hk : k ≤ m) :
    (terminalOddUpperShell m k).card = binomialUpperTail m k := by
  classical
  have heq :
      terminalOddUpperShell m k =
        (dyadicShell m).filter
          (fun n =>
            (⟨n % (2 ^ m), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
              Fin (2 ^ m)) ∈ terminalOddUpperResidues m k) := by
    ext n
    simp only [terminalOddUpperShell, terminalOddUpperResidues,
      Finset.mem_filter, Finset.mem_univ, true_and]
    apply and_congr_right
    intro _hn
    have hmod : n % 2 ^ m ≡ n [MOD 2 ^ m] := by
      show n % 2 ^ m % 2 ^ m = n % 2 ^ m
      exact Nat.mod_mod _ _
    rw [oddCount_eq_of_modEq hmod]
  rw [heq, card_dyadicShell_filter_mod_mem,
    card_terminalOddUpperResidues hk]

/-- The least odd-count threshold whose pure multiplicative term can exceed
`2^q`. -/
theorem exists_two_pow_lt_three_pow_succ (q : ℕ) :
    ∃ s : ℕ, 2 ^ q < 3 ^ (s + 1) := by
  refine ⟨q, ?_⟩
  calc
    2 ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by omega) q
    _ < 3 ^ (q + 1) := by
      rw [pow_succ]
      have hpos : 0 < 3 ^ q := pow_pos (by omega) _
      nlinarith

noncomputable def timeoutOddThreshold (q : ℕ) : ℕ :=
  Nat.find (exists_two_pow_lt_three_pow_succ q)

theorem two_pow_lt_three_pow_timeoutOddThreshold_succ (q : ℕ) :
    2 ^ q < 3 ^ (timeoutOddThreshold q + 1) := by
  exact Nat.find_spec (exists_two_pow_lt_three_pow_succ q)

theorem timeoutOddThreshold_le_of_two_pow_lt_three_pow_succ
    {q s : ℕ} (h : 2 ^ q < 3 ^ (s + 1)) :
    timeoutOddThreshold q ≤ s := by
  exact Nat.find_min' (exists_two_pow_lt_three_pow_succ q) h

/-- The least integral timeout threshold differs from `q log₃ 2` by less
than one on the lower side. -/
theorem timeoutOddThreshold_real_lower (q : ℕ) :
    (q : ℝ) * logThreeTwo - 1 < (timeoutOddThreshold q : ℝ) := by
  have hpowNat := two_pow_lt_three_pow_timeoutOddThreshold_succ q
  have hpow :
      (2 : ℝ) ^ q < (3 : ℝ) ^ (timeoutOddThreshold q + 1) := by
    exact_mod_cast hpowNat
  have hlog := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (show (0 : ℝ) < (2 : ℝ) ^ q by positivity))
    (Set.mem_Ioi.mpr
      (show (0 : ℝ) < (3 : ℝ) ^ (timeoutOddThreshold q + 1) by positivity))
    hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold logThreeTwo
  have hratio :
      (q : ℝ) * (Real.log 2 / Real.log 3) <
        (timeoutOddThreshold q : ℝ) + 1 := by
    rw [div_eq_mul_inv]
    rw [show (q : ℝ) * (Real.log 2 * (Real.log 3)⁻¹) =
        ((q : ℝ) * Real.log 2) / Real.log 3 by ring]
    rw [div_lt_iff₀ hlog3]
    push_cast at hlog ⊢
    simpa [Nat.cast_add, Nat.cast_one] using hlog
  linarith

/-- The least threshold is also no larger than `q log₃ 2`. -/
theorem timeoutOddThreshold_real_upper (q : ℕ) :
    (timeoutOddThreshold q : ℝ) ≤ (q : ℝ) * logThreeTwo := by
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  by_cases hk0 : timeoutOddThreshold q = 0
  · rw [hk0]
    simpa using mul_nonneg (Nat.cast_nonneg q) hp.le
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hnot := Nat.find_min (exists_two_pow_lt_three_pow_succ q)
      (show k < timeoutOddThreshold q by omega)
    have hpowNat : 3 ^ timeoutOddThreshold q ≤ 2 ^ q := by
      rw [hk]
      omega
    have hpow :
        (3 : ℝ) ^ timeoutOddThreshold q ≤ (2 : ℝ) ^ q := by
      exact_mod_cast hpowNat
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr
        (show (0 : ℝ) < (3 : ℝ) ^ timeoutOddThreshold q by positivity))
      (Set.mem_Ioi.mpr (show (0 : ℝ) < (2 : ℝ) ^ q by positivity)) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    unfold logThreeTwo
    rw [show (q : ℝ) * (Real.log 2 / Real.log 3) =
        ((q : ℝ) * Real.log 2) / Real.log 3 by ring]
    rw [le_div_iff₀ hlog3]
    simpa using hlog

/-- Terminal displacement of the exact timeout binomial threshold. -/
def timeoutOddDisplacement (K₀ : ℝ) (L m : ℕ) : ℝ :=
  (timeoutOddThreshold (timeoutTargetRank K₀ L m) : ℝ) / (m : ℝ) - 1 / 2

/-- Explicit first-order loss in the terminal timeout displacement. -/
def timeoutDisplacementLoss (K₀ : ℝ) : ℝ :=
  logThreeTwo * K₀ / 2 + logThreeTwo + 1

theorem timeoutDisplacementLoss_pos {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    0 < timeoutDisplacementLoss K₀ := by
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  unfold timeoutDisplacementLoss
  positivity

/-- Uniform lower approach of the exact timeout displacement to the endpoint
displacement.  Only `m ≥ L` is used; no upper rank window enters this scalar
estimate. -/
theorem timeoutOddDisplacement_gt_endpoint_sub_div
    {K₀ : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L) (hLm : L ≤ m) :
    firstPassageEndpointDisplacement -
        timeoutDisplacementLoss K₀ / (L : ℝ) <
      timeoutOddDisplacement K₀ L m := by
  let r := movingLowRatio K₀ L
  let q := timeoutTargetRank K₀ L m
  let k := timeoutOddThreshold q
  have hLR : 0 < (L : ℝ) := by positivity
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast hL.trans_le hLm
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  have hq : r * (m : ℝ) - 1 < (q : ℝ) := by
    simpa [r, q, timeoutTargetRank] using
      (Nat.sub_one_lt_floor (movingLowRatio K₀ L * (m : ℝ)))
  have hk : (q : ℝ) * logThreeTwo - 1 < (k : ℝ) := by
    simpa [k] using timeoutOddThreshold_real_lower q
  have hcombined :
      logThreeTwo * (r * (m : ℝ) - 1) - 1 < (k : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hq hp
    nlinarith [hmul, hk]
  have hnormalized :
      logThreeTwo * r - (logThreeTwo + 1) / (m : ℝ) <
        (k : ℝ) / (m : ℝ) := by
    rw [lt_div_iff₀ hmR]
    calc
      (logThreeTwo * r - (logThreeTwo + 1) / (m : ℝ)) * (m : ℝ) =
          logThreeTwo * (r * (m : ℝ) - 1) - 1 := by
            field_simp
            ring
      _ < (k : ℝ) := hcombined
  have hinv : 1 / (m : ℝ) ≤ 1 / (L : ℝ) := by
    exact one_div_le_one_div_of_le hLR (by exact_mod_cast hLm)
  have hpOne : 0 ≤ logThreeTwo + 1 := by positivity
  have herror :
      (logThreeTwo + 1) / (m : ℝ) ≤
        (logThreeTwo + 1) / (L : ℝ) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hpOne
  have hendpoint :
      firstPassageEndpointDisplacement = logThreeTwo - 1 / 2 := by
    linarith [endpoint_probability_eq_logThreeTwo]
  rw [timeoutOddDisplacement, timeoutDisplacementLoss, hendpoint]
  dsimp [r] at hnormalized
  unfold movingLowRatio at hnormalized
  have hKterm : 0 ≤ logThreeTwo * K₀ := mul_nonneg hp.le hK₀
  calc
    logThreeTwo - 1 / 2 -
          (logThreeTwo * K₀ / 2 + logThreeTwo + 1) / (L : ℝ)
        ≤ logThreeTwo * (1 - K₀ / (2 * (L : ℝ))) -
            (logThreeTwo + 1) / (m : ℝ) - 1 / 2 := by
          have hsplit :
              (logThreeTwo * K₀ / 2 + logThreeTwo + 1) / (L : ℝ) =
                logThreeTwo * K₀ / (2 * (L : ℝ)) +
                  (logThreeTwo + 1) / (L : ℝ) := by ring
          have hrw :
              logThreeTwo * (1 - K₀ / (2 * (L : ℝ))) =
                logThreeTwo - logThreeTwo * K₀ / (2 * (L : ℝ)) := by ring
          rw [hsplit]
          rw [hrw]
          nlinarith [herror]
    _ < (k : ℝ) / (m : ℝ) - 1 / 2 := by
      linarith

/-- The exact timeout displacement never exceeds the endpoint displacement
when the moving ratio lies in `[0,1]`. -/
theorem timeoutOddDisplacement_le_endpoint
    {K₀ : ℝ} {L m : ℕ}
    (hr0 : 0 ≤ movingLowRatio K₀ L)
    (hr1 : movingLowRatio K₀ L ≤ 1)
    (hm : 0 < m) :
    timeoutOddDisplacement K₀ L m ≤
      firstPassageEndpointDisplacement := by
  let r := movingLowRatio K₀ L
  let q := timeoutTargetRank K₀ L m
  let k := timeoutOddThreshold q
  have hmR : 0 < (m : ℝ) := by positivity
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  have hq : (q : ℝ) ≤ r * (m : ℝ) := by
    dsimp [q, r]
    simpa [timeoutTargetRank] using
      (Nat.floor_le (mul_nonneg hr0 (Nat.cast_nonneg m)))
  have hk : (k : ℝ) ≤ (q : ℝ) * logThreeTwo := by
    simpa [k] using timeoutOddThreshold_real_upper q
  have hkm : (k : ℝ) / (m : ℝ) ≤ logThreeTwo := by
    have hqr : (q : ℝ) * logThreeTwo ≤
        r * (m : ℝ) * logThreeTwo :=
      mul_le_mul_of_nonneg_right hq hp.le
    have hrm : r * (m : ℝ) * logThreeTwo ≤
        (m : ℝ) * logThreeTwo := by
      have hr1' : r ≤ 1 := by simpa [r] using hr1
      have hbase : r * (m : ℝ) ≤ (m : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hr1' (Nat.cast_nonneg m)
      exact mul_le_mul_of_nonneg_right hbase hp.le
    rw [div_le_iff₀ hmR]
    nlinarith [hk, hqr, hrm]
  have hendpoint :
      firstPassageEndpointDisplacement = logThreeTwo - 1 / 2 := by
    linarith [endpoint_probability_eq_logThreeTwo]
  rw [timeoutOddDisplacement, hendpoint]
  exact sub_le_sub_right hkm _

/-- Entropy rate of the exact terminal timeout threshold. -/
def timeoutOddEntropyRate (K₀ : ℝ) (L m : ℕ) : ℝ :=
  binaryBarrierRate (timeoutOddDisplacement K₀ L m)

/-- The exact timeout entropy rate reaches the endpoint rate with an explicit
`O(1/L)` loss, uniformly over all parent ranks `m ≥ L`. -/
theorem exists_timeoutOddEntropyRate_ge_endpoint_sub_div
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ D : ℝ, 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        firstPassageEndpointRate - D / (L : ℝ) ≤
          timeoutOddEntropyRate K₀ L m := by
  obtain ⟨C, hC, hLip⟩ := exists_binaryBarrierRate_endpoint_lipschitz
  let D := C * timeoutDisplacementLoss K₀
  have hLoss := timeoutDisplacementLoss_pos hK₀
  refine ⟨D, mul_pos hC hLoss, ?_⟩
  intro L m hL hLm hr0 hr1 hscale
  have hLR : 0 < (L : ℝ) := by positivity
  have hm : 0 < m := hL.trans_le hLm
  have hlower := timeoutOddDisplacement_gt_endpoint_sub_div hK₀ hL hLm
  have hupper := timeoutOddDisplacement_le_endpoint hr0 hr1 hm
  have hlowerHalf :
      firstPassageEndpointDisplacement / 2 ≤
        timeoutOddDisplacement K₀ L m := by
    have hLossDiv :
        timeoutDisplacementLoss K₀ / (L : ℝ) ≤
          firstPassageEndpointDisplacement / 2 := by
      rw [div_le_iff₀ hLR]
      nlinarith
    linarith
  have hTimeoutWindow :
      timeoutOddDisplacement K₀ L m ∈
        Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement :=
    ⟨hlowerHalf, hupper⟩
  have hEndpointWindow :
      firstPassageEndpointDisplacement ∈
        Set.Icc (firstPassageEndpointDisplacement / 2)
          firstPassageEndpointDisplacement :=
    ⟨by linarith [firstPassageEndpointDisplacement_pos], le_rfl⟩
  have hnorm := hLip
    (timeoutOddDisplacement K₀ L m) hTimeoutWindow
    firstPassageEndpointDisplacement hEndpointWindow
  have hdiffNonneg :
      0 ≤ firstPassageEndpointDisplacement -
        timeoutOddDisplacement K₀ L m := sub_nonneg.mpr hupper
  have hrateError :
      firstPassageEndpointRate - timeoutOddEntropyRate K₀ L m ≤
        C * (firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m) := by
    calc
      firstPassageEndpointRate - timeoutOddEntropyRate K₀ L m ≤
          ‖firstPassageEndpointRate - timeoutOddEntropyRate K₀ L m‖ :=
        le_abs_self _
      _ ≤ C * ‖firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m‖ := by
        simpa [firstPassageEndpointRate, timeoutOddEntropyRate] using hnorm
      _ = C * (firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hdiffNonneg]
  have hdispError :
      firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m <
        timeoutDisplacementLoss K₀ / (L : ℝ) := by
    linarith
  have hscaled :
      C * (firstPassageEndpointDisplacement -
          timeoutOddDisplacement K₀ L m) ≤ D / (L : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hdispError hC
    dsimp [D]
    have heq :
        C * (timeoutDisplacementLoss K₀ / (L : ℝ)) =
          (C * timeoutDisplacementLoss K₀) / (L : ℝ) := by ring
    rw [heq] at hmul
    exact hmul.le
  linarith [hrateError.trans hscaled]

/-- Literal timeout sources in a complete parent shell. -/
noncomputable def timeoutShellBad (K₀ : ℝ) (L m : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell m).filter (LowStageTimeout K₀ L m)

/-- Every literal timeout lies in the exact terminal binomial upper tail. -/
theorem timeoutShellBad_subset_terminalOddUpperShell
    (K₀ : ℝ) (L m : ℕ) :
    timeoutShellBad K₀ L m ⊆
      terminalOddUpperShell m
        (timeoutOddThreshold (timeoutTargetRank K₀ L m)) := by
  classical
  intro x hx
  rw [timeoutShellBad, Finset.mem_filter] at hx
  rw [terminalOddUpperShell, Finset.mem_filter]
  refine ⟨hx.1, ?_⟩
  exact timeoutOddThreshold_le_of_two_pow_lt_three_pow_succ
    (three_pow_timeoutTargetRank_lt_three_pow_oddCount_succ hx.1 hx.2)

/-- Exact finite timeout count before asymptotic rate comparison. -/
theorem card_timeoutShellBad_le_binomialUpperTail
    {K₀ : ℝ} {L m : ℕ}
    (hk : timeoutOddThreshold (timeoutTargetRank K₀ L m) ≤ m) :
    (timeoutShellBad K₀ L m).card ≤
      binomialUpperTail m
        (timeoutOddThreshold (timeoutTargetRank K₀ L m)) := by
  calc
    (timeoutShellBad K₀ L m).card ≤
        (terminalOddUpperShell m
          (timeoutOddThreshold (timeoutTargetRank K₀ L m))).card :=
      Finset.card_le_card (timeoutShellBad_subset_terminalOddUpperShell K₀ L m)
    _ = binomialUpperTail m
          (timeoutOddThreshold (timeoutTargetRank K₀ L m)) :=
      card_terminalOddUpperShell hk

/-- Fixed positive terminal displacement kept uniformly inside the sharp
binomial socket. -/
def timeoutEndpointT₀ : ℝ :=
  firstPassageEndpointDisplacement / 4

theorem timeoutEndpointT₀_pos : 0 < timeoutEndpointT₀ := by
  exact div_pos firstPassageEndpointDisplacement_pos (by norm_num)

/-- Sharp probability estimate for the literal timeout set.  The hypotheses
are only the moving-ratio range and the explicit startup ensuring that the
`O(1/L)` threshold loss stays inside the fixed endpoint window. -/
theorem exists_card_timeoutShellBad_sharp_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ K₀ : ℝ, ∀ L m : ℕ,
        0 ≤ K₀ → 0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          (C / Real.sqrt m) *
            Real.exp (-((m : ℝ) * timeoutOddEntropyRate K₀ L m)) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_normalized_binomialUpperTail_le_binaryBarrierRate
      timeoutEndpointT₀_pos
  refine ⟨C, hC, ?_⟩
  intro K₀ L m hK₀ hL hLm hr0 hr1 hscale
  let k := timeoutOddThreshold (timeoutTargetRank K₀ L m)
  have hm : 0 < m := hL.trans_le hLm
  have hmR : 0 < (m : ℝ) := by positivity
  have hdispLower :=
    timeoutOddDisplacement_gt_endpoint_sub_div hK₀ hL hLm
  have hdispUpper := timeoutOddDisplacement_le_endpoint hr0 hr1 hm
  have hLR : 0 < (L : ℝ) := by positivity
  have hLossDiv :
      timeoutDisplacementLoss K₀ / (L : ℝ) ≤
        firstPassageEndpointDisplacement / 2 := by
    rw [div_le_iff₀ hLR]
    nlinarith
  have hdispHalf :
      firstPassageEndpointDisplacement / 2 ≤
        timeoutOddDisplacement K₀ L m := by
    linarith
  have hratioLower :
      1 / 2 + firstPassageEndpointDisplacement / 2 ≤
        (k : ℝ) / (m : ℝ) := by
    simpa [timeoutOddDisplacement, k, add_comm] using
      add_le_add_left hdispHalf (1 / 2)
  have hratioUpper : (k : ℝ) / (m : ℝ) < 3 / 4 := by
    have hquarter := firstPassageEndpointDisplacement_lt_quarter
    have hraw :
        (k : ℝ) / (m : ℝ) - 1 / 2 ≤
          firstPassageEndpointDisplacement := by
      simpa [timeoutOddDisplacement, k] using hdispUpper
    linarith
  have hgap :
      (m : ℝ) * (1 / 2 + timeoutEndpointT₀) ≤ (k : ℝ) := by
    have ht₀ : timeoutEndpointT₀ ≤
        firstPassageEndpointDisplacement / 2 := by
      unfold timeoutEndpointT₀
      linarith [firstPassageEndpointDisplacement_pos]
    rw [mul_comm]
    have hsum : 1 / 2 + timeoutEndpointT₀ ≤
        1 / 2 + firstPassageEndpointDisplacement / 2 := by
      linarith
    exact (le_div_iff₀ hmR).1 (hsum.trans hratioLower)
  have hk : 0 < k := by
    have hpositive : 0 < (m : ℝ) * (1 / 2 + timeoutEndpointT₀) := by
      exact mul_pos hmR (by linarith [timeoutEndpointT₀_pos])
    have hkR : 0 < (k : ℝ) := lt_of_lt_of_le hpositive hgap
    exact_mod_cast hkR
  have hklt : k < m := by
    have hratioOne : (k : ℝ) / (m : ℝ) < 1 :=
      hratioUpper.trans (by norm_num)
    have hkR : (k : ℝ) < (m : ℝ) := by
      rwa [div_lt_one hmR] at hratioOne
    exact_mod_cast hkR
  have hkLower : (m : ℝ) / 4 ≤ (k : ℝ) := by
    have hhalf : (1 / 2 : ℝ) ≤
        1 / 2 + firstPassageEndpointDisplacement / 2 := by
      linarith [firstPassageEndpointDisplacement_pos]
    have hratioQuarter : (1 / 4 : ℝ) ≤ (k : ℝ) / (m : ℝ) := by
      linarith [hhalf.trans hratioLower]
    have hscaled := (le_div_iff₀ hmR).1 hratioQuarter
    calc
      (m : ℝ) / 4 = (1 / 4 : ℝ) * (m : ℝ) := by ring
      _ ≤ (k : ℝ) := hscaled
  have hmkLower :
      (m : ℝ) / 4 ≤ ((m - k : ℕ) : ℝ) := by
    have hkThreeQuarter : (k : ℝ) < 3 * (m : ℝ) / 4 := by
      rw [div_lt_iff₀ hmR] at hratioUpper
      nlinarith
    have hsubCast : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hklt.le]
    rw [hsubCast]
    linarith
  have hcount := card_timeoutShellBad_le_binomialUpperTail
    (K₀ := K₀) (L := L) (m := m) hklt.le
  have hcountR :
      ((timeoutShellBad K₀ L m).card : ℝ) ≤
        (binomialUpperTail m k : ℝ) := by exact_mod_cast hcount
  have hpow : 0 < (2 : ℝ) ^ m := by positivity
  calc
    ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
        (binomialUpperTail m k : ℝ) / (2 : ℝ) ^ m :=
      (div_le_div_iff_of_pos_right hpow).2 hcountR
    _ ≤ (C / Real.sqrt m) *
          Real.exp (-((m : ℝ) *
            binaryBarrierRate ((k : ℝ) / (m : ℝ) - 1 / 2))) :=
      htail m k hm hk hklt hgap hkLower hmkLower
    _ = (C / Real.sqrt m) *
          Real.exp (-((m : ℝ) * timeoutOddEntropyRate K₀ L m)) := by
      rfl

/-- Referee-facing sharp timeout density with the endpoint rate and its
explicit `D/L` loss. -/
theorem exists_card_timeoutShellBad_endpointRate_le
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          (C / Real.sqrt m) *
            Real.exp (-((m : ℝ) *
              (firstPassageEndpointRate - D / (L : ℝ)))) := by
  obtain ⟨C, hC, hsharp⟩ := exists_card_timeoutShellBad_sharp_le
  obtain ⟨D, hD, hrate⟩ :=
    exists_timeoutOddEntropyRate_ge_endpoint_sub_div hK₀
  refine ⟨C, D, hC, hD, ?_⟩
  intro L m hL hLm hr0 hr1 hscale
  have hm : 0 < m := hL.trans_le hLm
  have hfirst := hsharp K₀ L m hK₀ hL hLm hr0 hr1 hscale
  have hrate' := hrate L m hL hLm hr0 hr1 hscale
  have hexp :
      Real.exp (-((m : ℝ) * timeoutOddEntropyRate K₀ L m)) ≤
        Real.exp (-((m : ℝ) *
          (firstPassageEndpointRate - D / (L : ℝ)))) := by
    apply Real.exp_le_exp.2
    have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  exact hfirst.trans
    (mul_le_mul_of_nonneg_left hexp (div_nonneg hC.le (Real.sqrt_nonneg _)))

end

end FirstPassageLinearTransport
