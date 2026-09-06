/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutCore
import FirstPassageLinearTransport.FiniteBallot

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

/-- Up to its shell-rank horizon, the exact affine iterate is bounded by
twice its pure multiplicative parity term. -/
theorem orbit_scaled_lt_two_mul_parity
    {m x j : ℕ} (hx : x ∈ dyadicShell m) (hj : j ≤ m) :
    2 ^ j * orbit j x < 2 * 3 ^ oddCount x j * x := by
  rw [exact_affine_iterate_scaled]
  have hcorr := affineCorrection_lt_two_pow_mul_three_pow x j
  have hjpow : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hj
  have hxm : 2 ^ m ≤ x := (mem_dyadicShell.mp hx).1
  have htwojx : 2 ^ j ≤ x := hjpow.trans hxm
  calc
    3 ^ oddCount x j * x + affineCorrection x j <
        3 ^ oddCount x j * x + 2 ^ j * 3 ^ oddCount x j :=
      Nat.add_lt_add_left hcorr _
    _ ≤ 3 ^ oddCount x j * x + x * 3 ^ oddCount x j := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right (3 ^ oddCount x j) htwojx) _
    _ = 2 * 3 ^ oddCount x j * x := by ring

theorem wordPrefix_boolParityWord
    {m : ℕ} (x : ℕ) (j : Fin (m + 1)) :
    wordPrefix (boolParityWord m x) j = boolParityWord j x := by
  funext i
  simp [wordPrefix, boolParityWord]

/-- Every prefix of a literal timeout word stays above the exact logarithmic
barrier supplied by the parent and target ranks. -/
theorem timeout_prefix_word_sum_lower
    {K₀ : ℝ} {L m x : ℕ}
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m)
    (j : Fin (m + 1)) :
    -(((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ) * Real.log 2) <
      wordIncrementSum collatzLogIncrement (boolParityWord j x) := by
  let q := timeoutTargetRank K₀ L m
  let k := (j : ℕ)
  have hk : k ≤ m := by
    dsimp [k]
    omega
  have htimeoutj : 2 ^ q < orbit k x := by
    simpa [q, k] using htimeout j
  have hscaled := orbit_scaled_lt_two_mul_parity hx hk
  have hxupper : x < 2 ^ (m + 1) := (mem_dyadicShell.mp hx).2
  have hpowk : 0 < 2 ^ k := by positivity
  have hnat :
      2 ^ (q + k) < 3 ^ oddCount x k * 2 ^ (m + 2) := by
    calc
      2 ^ (q + k) = 2 ^ k * 2 ^ q := by
        rw [pow_add]
        ring
      _ < 2 ^ k * orbit k x :=
        Nat.mul_lt_mul_of_pos_left htimeoutj hpowk
      _ < 2 * 3 ^ oddCount x k * x := hscaled
      _ < 2 * 3 ^ oddCount x k * 2 ^ (m + 1) := by
        exact Nat.mul_lt_mul_of_pos_left hxupper (by positivity)
      _ = 3 ^ oddCount x k * 2 ^ (m + 2) := by
        rw [pow_succ]
        ring
  have hreal :
      (2 : ℝ) ^ (q + k) <
        (3 : ℝ) ^ oddCount x k * (2 : ℝ) ^ (m + 2) := by
    exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < (2 : ℝ) ^ (q + k)))
    (Set.mem_Ioi.mpr
      (by positivity : (0 : ℝ) <
        (3 : ℝ) ^ oddCount x k * (2 : ℝ) ^ (m + 2))) hreal
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  have hqle : q ≤ m + 2 := hq.trans (by omega)
  have hcastsub : ((m + 2 - q : ℕ) : ℝ) =
      (m + 2 : ℝ) - (q : ℝ) := by
    rw [Nat.cast_sub hqle]
    push_cast
    rfl
  have hsum :
      wordIncrementSum collatzLogIncrement (boolParityWord j x) =
        (oddCount x k : ℝ) * Real.log 3 - (k : ℝ) * Real.log 2 := by
    rw [wordIncrementSum_collatz, card_boolSupport_boolParityWord]
  rw [hsum, hcastsub]
  push_cast at hlog ⊢
  linarith

/-- Literal timeout containment in an exact finite-word barrier language.
The following uniform low-rank theorem replaces this rank-dependent barrier
by the fixed constant used in Lemma 6.3. -/
theorem timeout_word_survives_exact_barrier
    {K₀ : ℝ} {L m x : ℕ}
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m) :
    wordSurvivesFrom
      (-(((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ) * Real.log 2))
      collatzLogIncrement m 0 (boolParityWord m x) := by
  apply wordSurvivesFrom_of_prefix
  intro j
  rw [wordPrefix_boolParityWord]
  simpa using (timeout_prefix_word_sum_lower hx htimeout hq j).le

/-- Lowering a finite-word barrier preserves survival. -/
theorem wordSurvivesFrom_mono_lower
    {lo lo' : ℝ} {increment : Bool → ℝ} {r : ℕ} {z : ℝ}
    {v : Fin r → Bool} (hlo : lo' ≤ lo)
    (h : wordSurvivesFrom lo increment r z v) :
    wordSurvivesFrom lo' increment r z v := by
  induction r generalizing z with
  | zero =>
      exact hlo.trans h
  | succ r ih =>
      exact ⟨hlo.trans h.1, ih h.2⟩

/-- On a low-rank window `m ≤ C L`, the timeout target loses at most a
fixed real amount of rank.  This is the floor calculation behind the uniform
barrier used in the finite ballot estimate. -/
theorem timeout_rank_gap_le_uniform
    {K₀ C : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ)) :
    (m : ℝ) - timeoutTargetRank K₀ L m ≤ C * K₀ / 2 + 1 := by
  let r := movingLowRatio K₀ L
  let q := timeoutTargetRank K₀ L m
  have hLR : 0 < (L : ℝ) := by positivity
  have hq : r * (m : ℝ) - 1 < (q : ℝ) := by
    simpa [r, q, timeoutTargetRank] using
      (Nat.sub_one_lt_floor (movingLowRatio K₀ L * (m : ℝ)))
  have hscale : K₀ * (m : ℝ) / (2 * (L : ℝ)) ≤ C * K₀ / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hmC hK₀
    rw [div_le_iff₀ (show 0 < (2 : ℝ) * (L : ℝ) by positivity)]
    nlinarith
  dsimp [r] at hq
  unfold movingLowRatio at hq
  change (m : ℝ) - (q : ℝ) ≤ C * K₀ / 2 + 1
  have hrw :
      (1 - K₀ / (2 * (L : ℝ))) * (m : ℝ) =
        (m : ℝ) - K₀ * (m : ℝ) / (2 * (L : ℝ)) := by
    field_simp
  rw [hrw] at hq
  nlinarith

/-- Every literal timeout word in a fixed low-rank window survives one
barrier depending only on the window constants.  The extra two rank units
come from the uniform affine-orbit comparison above. -/
theorem timeout_word_survives_uniform_barrier
    {K₀ C : ℝ} {L m x : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ))
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m) :
    wordSurvivesFrom
      (-((C * K₀ / 2 + 3) * Real.log 2))
      collatzLogIncrement m 0 (boolParityWord m x) := by
  have hqle : timeoutTargetRank K₀ L m ≤ m + 2 := hq.trans (by omega)
  have hgapcast :
      (((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ)) =
        (m : ℝ) + 2 - timeoutTargetRank K₀ L m := by
    rw [Nat.cast_sub hqle]
    push_cast
    rfl
  have hgap := timeout_rank_gap_le_uniform hK₀ hL hmC
  apply wordSurvivesFrom_mono_lower
    (lo := -(((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ) * Real.log 2))
  · rw [hgapcast]
    apply neg_le_neg
    gcongr
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  · exact timeout_word_survives_exact_barrier hx htimeout hq

/-- Survival includes the endpoint after all letters have been read. -/
theorem wordSurvivesFrom_terminal
    {lo : ℝ} {increment : Bool → ℝ} {r : ℕ} {z : ℝ}
    {v : Fin r → Bool}
    (h : wordSurvivesFrom lo increment r z v) :
    lo ≤ z + wordIncrementSum increment v := by
  induction r generalizing z with
  | zero =>
      simpa [wordIncrementSum, wordSurvivesFrom] using h
  | succ r ih =>
      have ht := ih h.2
      unfold wordIncrementSum at ht
      rw [wordIncrementSum, Fin.sum_univ_succ]
      simpa [add_assoc] using ht

/-- The unique integer bin containing the shifted terminal logarithmic
increment of a finite word. -/
noncomputable def collatzTerminalBinIndex
    {m : ℕ} (B : ℝ) (v : Fin m → Bool) : ℕ :=
  ⌊B + wordIncrementSum collatzLogIncrement v⌋₊

/-- Every lower-barrier-surviving word belongs to its canonical terminal
unit bin. -/
theorem collatzFullBarrierBinEvent_at_index
    {m : ℕ} {B : ℝ} {v : Fin m → Bool}
    (hsurv : wordSurvivesFrom (-B) collatzLogIncrement m 0 v) :
    collatzFullBarrierBinEvent B (collatzTerminalBinIndex B v) v := by
  have hterminal := wordSurvivesFrom_terminal hsurv
  have hnonneg : 0 ≤ B + wordIncrementSum collatzLogIncrement v := by
    linarith
  have hfloor :
      (collatzTerminalBinIndex B v : ℝ) ≤
        B + wordIncrementSum collatzLogIncrement v := by
    simpa [collatzTerminalBinIndex] using Nat.floor_le hnonneg
  have hfloorNext :
      B + wordIncrementSum collatzLogIncrement v <
        (collatzTerminalBinIndex B v : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one
      (B + wordIncrementSum collatzLogIncrement v)
    simpa [collatzTerminalBinIndex] using h
  refine ⟨hsurv, ?_⟩
  unfold collatzMiddleInterval
  constructor <;> linarith

/-- The Collatz logarithmic increment of a word is at most its length. -/
theorem wordIncrementSum_collatz_le_length
    {m : ℕ} (v : Fin m → Bool) :
    wordIncrementSum collatzLogIncrement v ≤ m := by
  unfold wordIncrementSum
  calc
    (∑ i : Fin m, collatzLogIncrement (v i)) ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (le_abs_self _).trans (collatzLogIncrement_abs_le_one (v i))
    _ = (m : ℝ) := by simp

/-- The canonical terminal bin lies in a finite range depending only on the
word length and the barrier. -/
theorem collatzTerminalBinIndex_lt
    {m : ℕ} {B : ℝ} {v : Fin m → Bool}
    (hnonneg : 0 ≤ B + wordIncrementSum collatzLogIncrement v) :
    collatzTerminalBinIndex B v < m + ⌈B⌉₊ + 2 := by
  have hsum := wordIncrementSum_collatz_le_length v
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  unfold collatzTerminalBinIndex
  rw [Nat.floor_lt hnonneg]
  push_cast
  linarith

/-- The indicator of a literal full-word barrier/bin event is nonnegative. -/
theorem collatzFullBarrierBinIndicator_nonneg
    {m : ℕ} (B q : ℝ) (v : Fin m → Bool) :
    0 ≤ collatzFullBarrierBinIndicator B q v := by
  classical
  unfold collatzFullBarrierBinIndicator
  split <;> norm_num

/-- Survival mass is covered by the finite sum of canonical terminal bins. -/
theorem collatzSurvivalMass_le_fullWordBins
    {m Q : ℕ} {B : ℝ}
    (hQ : m + ⌈B⌉₊ + 2 ≤ Q) :
    weightedSurvivalWordMass (1 / 2) collatzLogIncrement (-B) m 0 ≤
      ∑ q ∈ Finset.range Q,
        collatzFullWordMass (1 / 2) m B (q : ℝ) := by
  classical
  unfold weightedSurvivalWordMass collatzFullWordMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hsurv : wordSurvivesFrom (-B) collatzLogIncrement m 0 v
  · have hterminal := wordSurvivesFrom_terminal hsurv
    have hnonneg : 0 ≤ B + wordIncrementSum collatzLogIncrement v := by
      linarith
    have hindex := collatzTerminalBinIndex_lt hnonneg
    have hindexQ : collatzTerminalBinIndex B v ∈ Finset.range Q := by
      simp only [Finset.mem_range]
      omega
    have hevent := collatzFullBarrierBinEvent_at_index hsurv
    calc
      bernoulliWordWeight (1 / 2) v *
          (if wordSurvivesFrom (-B) collatzLogIncrement m 0 v then 1 else 0) =
          bernoulliWordWeight (1 / 2) v *
            collatzFullBarrierBinIndicator B (collatzTerminalBinIndex B v) v := by
        simp [hsurv, collatzFullBarrierBinIndicator, hevent]
      _ ≤ ∑ q ∈ Finset.range Q,
          bernoulliWordWeight (1 / 2) v *
            collatzFullBarrierBinIndicator B (q : ℝ) v := by
        exact Finset.single_le_sum
          (f := fun q : ℕ => bernoulliWordWeight (1 / 2) v *
            collatzFullBarrierBinIndicator B (q : ℝ) v)
          (fun q _hq => mul_nonneg
            (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v)
            (collatzFullBarrierBinIndicator_nonneg B (q : ℝ) v))
          hindexQ
  · simp only [hsurv, if_false, mul_zero]
    exact Finset.sum_nonneg fun q _hq =>
      mul_nonneg
        (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v)
        (collatzFullBarrierBinIndicator_nonneg B (q : ℝ) v)

/-- Finite set of lower-barrier-surviving Boolean words. -/
noncomputable def collatzSurvivalWords (m : ℕ) (B : ℝ) :
    Finset (Fin m → Bool) := by
  classical
  exact Finset.univ.filter
    (wordSurvivesFrom (-B) collatzLogIncrement m 0)

/-- At fair weight, normalized survivor cardinality is exactly survivor
mass. -/
theorem weightedSurvivalWordMass_half_eq_card
    (m : ℕ) (B : ℝ) :
    weightedSurvivalWordMass (1 / 2) collatzLogIncrement (-B) m 0 =
      ((collatzSurvivalWords m B).card : ℝ) / (2 : ℝ) ^ m := by
  classical
  unfold weightedSurvivalWordMass collatzSurvivalWords
  rw [show (∑ v : Fin m → Bool,
      bernoulliWordWeight (1 / 2) v *
        (if wordSurvivesFrom (-B) collatzLogIncrement m 0 v then 1 else 0)) =
      ∑ v : Fin m → Bool,
        if wordSurvivesFrom (-B) collatzLogIncrement m 0 v then
          (1 / 2 : ℝ) ^ m else 0 by
    apply Finset.sum_congr rfl
    intro v _hv
    rw [bernoulliWordWeight_half_eq]
    split <;> simp_all]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [one_div, inv_pow]
  field_simp

/-- Surviving residue classes in one complete parity block. -/
noncomputable def collatzSurvivalResidues (m : ℕ) (B : ℝ) :
    Finset (Fin (2 ^ m)) := by
  classical
  exact Finset.univ.filter (fun x =>
    wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityCode m x))

/-- The parity equivalence restricted to surviving words. -/
noncomputable def collatzSurvivalResidueEquiv (m : ℕ) (B : ℝ) :
    {x : Fin (2 ^ m) //
      wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityCode m x)} ≃
      {v : Fin m → Bool //
        wordSurvivesFrom (-B) collatzLogIncrement m 0 v} :=
  (boolParityEquiv m).subtypeEquiv (fun x => by
    rw [boolParityEquiv_apply])

theorem card_collatzSurvivalResidues (m : ℕ) (B : ℝ) :
    (collatzSurvivalResidues m B).card =
      (collatzSurvivalWords m B).card := by
  classical
  unfold collatzSurvivalResidues collatzSurvivalWords
  rw [← Fintype.card_subtype (fun x : Fin (2 ^ m) =>
        wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityCode m x)),
      ← Fintype.card_subtype
        (wordSurvivesFrom (-B) collatzLogIncrement m 0)]
  exact Fintype.card_congr (collatzSurvivalResidueEquiv m B)

/-- Surviving parity words realized by sources in one dyadic shell. -/
noncomputable def collatzSurvivalShell (m : ℕ) (B : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell m).filter (fun x =>
    wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityWord m x))

/-- Exact parity coding identifies shell survivors with abstract word
survivors. -/
theorem card_collatzSurvivalShell (m : ℕ) (B : ℝ) :
    (collatzSurvivalShell m B).card =
      (collatzSurvivalWords m B).card := by
  classical
  have heq : collatzSurvivalShell m B =
      (dyadicShell m).filter (fun n =>
        (⟨n % (2 ^ m), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
          Fin (2 ^ m)) ∈ collatzSurvivalResidues m B) := by
    ext n
    simp only [collatzSurvivalShell, collatzSurvivalResidues,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => by
      rw [boolParityCode_eq_word, boolParityWord_mod])
  rw [heq, card_dyadicShell_filter_mod_mem,
    card_collatzSurvivalResidues]

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

/-- Literal low-stage timeout sources are contained in the corresponding
uniform finite-word barrier event. -/
theorem timeoutShellBad_subset_collatzSurvivalShell
    {K₀ C : ℝ} {L m : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ))
    (hq : timeoutTargetRank K₀ L m ≤ m) :
    timeoutShellBad K₀ L m ⊆
      collatzSurvivalShell m ((C * K₀ / 2 + 3) * Real.log 2) := by
  intro x hx
  simp only [timeoutShellBad, collatzSurvivalShell,
    Finset.mem_filter] at hx ⊢
  exact ⟨hx.1,
    timeout_word_survives_uniform_barrier hK₀ hL hmC hx.1 hx.2 hq⟩

/-- Exact finite ballot timeout estimate on every low-rank window.  This is
the formal shell-level form of the manuscript's `m^{-3/2}` improvement,
before absorbing the fixed barrier into the implied constant. -/
theorem exists_timeoutShellBad_ballot_ratio_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ K₀ C : ℝ, ∀ L m : ℕ,
        0 ≤ K₀ → 0 ≤ C → 0 < L → L ≤ m →
        (m : ℝ) ≤ C * (L : ℝ) →
        timeoutTargetRank K₀ L m ≤ m → 8 ≤ m →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          C₀ * (((C * K₀ / 2 + 3) * Real.log 2) + 1) /
              ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
              collatzTiltLambda * ((C * K₀ / 2 + 3) * Real.log 2)) := by
  obtain ⟨C₀, hC₀, hBallot⟩ :=
    exists_sum_collatzQuarterSplitFullWordMass_le
  refine ⟨C₀, hC₀, ?_⟩
  intro K₀ C L m hK₀ hC hL _hLm hmC hq hm
  let B := (C * K₀ / 2 + 3) * Real.log 2
  let Q := m + ⌈B⌉₊ + 2
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsubset := timeoutShellBad_subset_collatzSurvivalShell
    hK₀ hL hmC hq
  have hcard : (timeoutShellBad K₀ L m).card ≤
      (collatzSurvivalShell m B).card := by
    exact Finset.card_le_card hsubset
  have hcardR : ((timeoutShellBad K₀ L m).card : ℝ) ≤
      (collatzSurvivalShell m B).card := by exact_mod_cast hcard
  have hpow : 0 < (2 : ℝ) ^ m := by positivity
  calc
    ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
        ((collatzSurvivalShell m B).card : ℝ) / (2 : ℝ) ^ m := by
      exact div_le_div_of_nonneg_right hcardR hpow.le
    _ = weightedSurvivalWordMass (1 / 2) collatzLogIncrement (-B) m 0 := by
      rw [card_collatzSurvivalShell,
        weightedSurvivalWordMass_half_eq_card]
    _ ≤ ∑ q ∈ Finset.range Q,
        collatzFullWordMass (1 / 2) m B (q : ℝ) := by
      exact collatzSurvivalMass_le_fullWordBins (le_refl Q)
    _ ≤ C₀ * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
            collatzTiltLambda * B) := hBallot m Q B hm hB
    _ = C₀ * (((C * K₀ / 2 + 3) * Real.log 2) + 1) /
              ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
              collatzTiltLambda * ((C * K₀ / 2 + 3) * Real.log 2)) := by
      rfl

/-- The finite-word change-of-measure rate is exactly the endpoint entropy
rate already used by the first-passage parameter layer. -/
theorem collatzFairTiltRate_eq_firstPassageEndpointRate :
    collatzFairTiltRate = firstPassageEndpointRate := by
  rw [collatzFairTiltRate_eq_entropy, firstPassageEndpointRate,
    binaryBarrierRate, endpoint_probability_eq_logThreeTwo]
  rfl

/-- Fixed-parameter form of the ballot timeout estimate.  The barrier and
terminal-bin constants are absorbed once `K₀` and the low-window multiplier
`C` are fixed. -/
theorem exists_timeoutShellBad_ballot_fixed_constant
    (K₀ C : ℝ) (hK₀ : 0 ≤ K₀) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m → (m : ℝ) ≤ C * (L : ℝ) →
        timeoutTargetRank K₀ L m ≤ m → 8 ≤ m →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          D / ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(firstPassageEndpointRate * (m : ℝ))) := by
  obtain ⟨C₀, hC₀, hRaw⟩ := exists_timeoutShellBad_ballot_ratio_le
  let B := (C * K₀ / 2 + 3) * Real.log 2
  let D := C₀ * (B + 1) * Real.exp (collatzTiltLambda * B)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro L m hL hLm hmC hq hm
  have hbound := hRaw K₀ C L m hK₀ hC hL hLm hmC hq hm
  rw [collatzFairTiltRate_eq_firstPassageEndpointRate] at hbound
  calc
    ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
        C₀ * (B + 1) / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(firstPassageEndpointRate * (m : ℝ)) +
            collatzTiltLambda * B) := by simpa [B] using hbound
    _ = D / ((m : ℝ) * Real.sqrt m) *
          Real.exp (-(firstPassageEndpointRate * (m : ℝ))) := by
      rw [show -(firstPassageEndpointRate * (m : ℝ)) +
          collatzTiltLambda * B =
          collatzTiltLambda * B +
            -(firstPassageEndpointRate * (m : ℝ)) by ring,
        Real.exp_add]
      dsimp [D]
      ring

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
    have ht₀' : 1 / 2 + timeoutEndpointT₀ ≤
        1 / 2 + firstPassageEndpointDisplacement / 2 := by
      simpa [add_comm] using add_le_add_left ht₀ (1 / 2)
    rw [mul_comm]
    exact (le_div_iff₀ hmR).1
      (ht₀'.trans hratioLower)
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
