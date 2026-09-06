/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.OrbitCeiling

/-!
# Reciprocal height obstruction

This module transfers the finite reciprocal multiplicative-maximum theorem
to arbitrary prefix lengths inside complete dyadic shells.  A prefix crossing
forces a genuine shortcut iterate above the relative-height ceiling.  If the
target is too small to be reached during that prefix, every such source fails
the simultaneous target-and-height conclusion.

The resulting finite shell inequality is the exact quantitative core of the
moving-ceiling obstruction.  It uses only parity-periodicity and does not
model an infinite Collatz orbit by independent random variables.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators Real

noncomputable section

/-! ## Prefix residues inside a larger shell -/

/-- Translation identifies the complete shell `[2^M,2^(M+1))` with one
complete residue block modulo `2^M`. -/
def dyadicShellEquivFin (M : ℕ) :
    {n : ℕ // n ∈ dyadicShell M} ≃ Fin (2 ^ M) where
  toFun n := ⟨n.1 - 2 ^ M, by
    have hn := mem_dyadicShell.mp n.2
    have hpow : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by
      simp [pow_succ, Nat.mul_comm, Nat.two_mul]
    omega⟩
  invFun x := ⟨2 ^ M + x.1, mem_dyadicShell.mpr ⟨by omega, by
    have hpow : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by
      simp [pow_succ, Nat.mul_comm, Nat.two_mul]
    omega⟩⟩
  left_inv n := by
    apply Subtype.ext
    have hn := (mem_dyadicShell.mp n.2).1
    simp only
    omega
  right_inv x := by
    apply Fin.ext
    simp only
    omega

/-- Split a complete shell residue into a block index and its residue modulo
`2^h`. -/
def dyadicShellPrefixEquiv (M h : ℕ) (hhM : h ≤ M) :
    {n : ℕ // n ∈ dyadicShell M} ≃
      Fin (2 ^ (M - h)) × Fin (2 ^ h) :=
  (dyadicShellEquivFin M).trans
    ((finCongr (by
      rw [← pow_add]
      congr 1
      omega : 2 ^ M = 2 ^ (M - h) * 2 ^ h)).trans
      finProdFinEquiv.symm)

theorem dyadicShellPrefixEquiv_second_mod
    (M h : ℕ) (hhM : h ≤ M)
    (n : {n : ℕ // n ∈ dyadicShell M}) :
    ((dyadicShellPrefixEquiv M h hhM n).2 : ℕ) = n.1 % (2 ^ h) := by
  have hpowDvd : 2 ^ h ∣ 2 ^ M := pow_dvd_pow 2 hhM
  have hbaseMod : 2 ^ M % 2 ^ h = 0 := Nat.mod_eq_zero_of_dvd hpowDvd
  have hnLower := (mem_dyadicShell.mp n.2).1
  have hshift : n.1 = 2 ^ M + (n.1 - 2 ^ M) := by omega
  simp only [dyadicShellPrefixEquiv, Equiv.trans_apply,
    finProdFinEquiv_symm_apply, Fin.coe_modNat, finCongr_apply,
    dyadicShellEquivFin]
  simp only [Fin.coe_cast]
  rw [hshift, Nat.add_mod, hbaseMod]
  simp

/-- Sources in the `M`-shell whose length-`h` residue belongs to `S`. -/
noncomputable def shellPrefixResidueSet
    (M h : ℕ) (hhM : h ≤ M) (S : Finset (Fin (2 ^ h))) :
    Finset {n : ℕ // n ∈ dyadicShell M} := by
  classical
  exact Finset.univ.filter fun n => (dyadicShellPrefixEquiv M h hhM n).2 ∈ S

theorem card_shellPrefixResidueSet
    (M h : ℕ) (hhM : h ≤ M) (S : Finset (Fin (2 ^ h))) :
    (shellPrefixResidueSet M h hhM S).card = 2 ^ (M - h) * S.card := by
  classical
  let e : {n : ℕ // n ∈ dyadicShell M} ≃
      Fin (2 ^ (M - h)) × Fin (2 ^ h) :=
    dyadicShellPrefixEquiv M h hhM
  have hc :
      (shellPrefixResidueSet M h hhM S).card =
        ((Finset.univ : Finset (Fin (2 ^ (M - h)))).product S).card := by
    apply Finset.card_bij (fun n _hn => e n)
    · intro n hn
      have hnS := (Finset.mem_filter.mp hn).2
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hnS⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      exact e.injective heq
    · intro b hb
      refine ⟨e.symm b, ?_, by simp [e]⟩
      simp only [shellPrefixResidueSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hbS : b.2 ∈ S := (Finset.mem_product.mp hb).2
      simpa [e] using hbS
  rw [hc]
  calc
    ((Finset.univ : Finset (Fin (2 ^ (M - h)))).product S).card =
        (Finset.univ : Finset (Fin (2 ^ (M - h)))).card * S.card :=
      Finset.card_product _ _
    _ = 2 ^ (M - h) * S.card := by simp

/-! ## The exact prefix hit event -/

/-- The length-`h` multiplicative-hit event, repeated exactly through the
complete `M`-shell. -/
noncomputable def shellPrefixMultiplicativeHit
    (M h : ℕ) (hhM : h ≤ M) (u : ℝ) :
    Finset {n : ℕ // n ∈ dyadicShell M} :=
  shellPrefixResidueSet M h hhM (multiplicativeHitResidues h u)

theorem card_shellPrefixMultiplicativeHit
    (M h : ℕ) (hhM : h ≤ M) (u : ℝ) :
    (shellPrefixMultiplicativeHit M h hhM u).card =
      2 ^ (M - h) * multiplicativeHitCount u h 1 := by
  rw [shellPrefixMultiplicativeHit, card_shellPrefixResidueSet,
    card_multiplicativeHitResidues]

theorem shellPrefixMultiplicativeHit_crosses
    {M h : ℕ} (hhM : h ≤ M) {u : ℝ}
    {n : {n : ℕ // n ∈ dyadicShell M}}
    (hn : n ∈ shellPrefixMultiplicativeHit M h hhM u) :
    crossesMultiplicativeFrom u h 1 (boolParityWord h n.1) := by
  classical
  have hnResidue :
      (dyadicShellPrefixEquiv M h hhM n).2 ∈
        multiplicativeHitResidues h u := by
    simpa [shellPrefixMultiplicativeHit, shellPrefixResidueSet] using hn
  have hcrossCode :
      crossesMultiplicativeFrom u h 1
        (boolParityCode h (dyadicShellPrefixEquiv M h hhM n).2) := by
    rw [multiplicativeHitResidues] at hnResidue
    exact (Finset.mem_filter.mp hnResidue).2
  have hword :
      boolParityCode h (dyadicShellPrefixEquiv M h hhM n).2 =
        boolParityWord h n.1 := by
    rw [boolParityCode_eq_word]
    change boolParityWord h
        ((dyadicShellPrefixEquiv M h hhM n).2 : ℕ) =
      boolParityWord h n.1
    rw [dyadicShellPrefixEquiv_second_mod, boolParityWord_mod]
  rwa [hword] at hcrossCode

theorem exists_orbit_gt_mul_of_mem_shellPrefixMultiplicativeHit
    {M h : ℕ} (hhM : h ≤ M) {u : ℝ}
    {n : {n : ℕ // n ∈ dyadicShell M}}
    (hn : n ∈ shellPrefixMultiplicativeHit M h hhM u) :
    ∃ j : ℕ, j ≤ h ∧ u * (n.1 : ℝ) < (orbit j n.1 : ℝ) := by
  have hcross := shellPrefixMultiplicativeHit_crosses hhM hn
  obtain ⟨j, hjh, hj⟩ :=
    exists_multiplicative_prefix_gt_of_crosses hcross
  have hnPosNat : 0 < n.1 := by
    exact (pow_pos (by omega) M).trans_le (mem_dyadicShell.mp n.2).1
  have hnPos : 0 < (n.1 : ℝ) := by exact_mod_cast hnPosNat
  have hscaled := mul_lt_mul_of_pos_right hj hnPos
  have hscaled' :
      u * (n.1 : ℝ) <
        ((3 : ℝ) ^ oddCount n.1 j / (2 : ℝ) ^ j) * (n.1 : ℝ) := by
    simpa using hscaled
  exact ⟨j, hjh, hscaled'.trans_le (pure_multiplicative_le_orbit n.1 j)⟩

/-! ## Target-and-height obstruction -/

theorem orbit_lower_by_halving (n j : ℕ) :
    (n : ℝ) / (2 : ℝ) ^ j ≤ (orbit j n : ℝ) := by
  have hthree : (1 : ℝ) ≤ (3 : ℝ) ^ oddCount n j :=
    one_le_pow₀ (by norm_num)
  calc
    (n : ℝ) / (2 : ℝ) ^ j =
        (1 / (2 : ℝ) ^ j) * (n : ℝ) := by ring
    _ ≤ ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) := by
      gcongr
    _ ≤ (orbit j n : ℝ) := pure_multiplicative_le_orbit n j

/-- A witness that simultaneously lands below `f n` and respects the relative
shortcut ceiling `u * n`. -/
def HasTargetHeightWitness (f : ℕ → ℝ) (u : ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (orbit k n : ℝ) ≤ f n ∧
      ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ u * (n : ℝ)

/-- Sources in one shell without a simultaneous target-and-height witness. -/
noncomputable def shellTargetHeightFailure
    (M : ℕ) (f : ℕ → ℝ) (u : ℝ) :
    Finset {n : ℕ // n ∈ dyadicShell M} := by
  classical
  exact Finset.univ.filter fun n => ¬HasTargetHeightWitness f u n.1

theorem shellPrefixMultiplicativeHit_subset_shellTargetHeightFailure
    {M h : ℕ} (hhM : h ≤ M) {u : ℝ} {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    shellPrefixMultiplicativeHit M h hhM u ⊆
      shellTargetHeightFailure M f u := by
  classical
  intro n hn
  simp only [shellTargetHeightFailure, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro hwitness
  obtain ⟨k, hkTarget, hkHeight⟩ := hwitness
  have hhk : h < k := by
    by_contra hnot
    have hkh : k ≤ h := Nat.le_of_not_gt hnot
    have hnPosNat : 0 < n.1 :=
      (pow_pos (by omega) M).trans_le (mem_dyadicShell.mp n.2).1
    have hnPos : 0 < (n.1 : ℝ) := by exact_mod_cast hnPosNat
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ h :=
      pow_le_pow_right₀ (by norm_num) hkh
    have hdiv :
        (n.1 : ℝ) / (2 : ℝ) ^ h ≤
          (n.1 : ℝ) / (2 : ℝ) ^ k :=
      (div_le_div_iff_of_pos_left hnPos (by positivity) (by positivity)).2 hpow
    have hlower := orbit_lower_by_halving n.1 k
    linarith [htarget n.1 n.2]
  obtain ⟨j, hjh, hjHigh⟩ :=
    exists_orbit_gt_mul_of_mem_shellPrefixMultiplicativeHit hhM hn
  have hjk : j ≤ k := hjh.trans hhk.le
  exact (not_lt_of_ge (hkHeight j hjk)) hjHigh

theorem normalized_card_shellPrefixMultiplicativeHit
    (M h : ℕ) (hhM : h ≤ M) (u : ℝ) :
    ((shellPrefixMultiplicativeHit M h hhM u).card : ℝ) /
        (2 : ℝ) ^ M =
      (multiplicativeHitCount u h 1 : ℝ) / (2 : ℝ) ^ h := by
  rw [card_shellPrefixMultiplicativeHit]
  push_cast
  have hpow : (2 : ℝ) ^ M =
      (2 : ℝ) ^ (M - h) * (2 : ℝ) ^ h := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp

/-- Exact finite moving-shell obstruction.  The target-unreachability and
logarithmic-slope hypotheses can be discharged asymptotically by taking, for
example, `h = floor (M/2)` and subexponential shell targets and ceilings. -/
theorem normalized_card_shellTargetHeightFailure_ge_reciprocal
    {M h : ℕ} (hhM : h ≤ M) (hh : 0 < h)
    {u : ℝ} (hu : 1 ≤ u)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) ≤
      ((shellTargetHeightFailure M f u).card : ℝ) / (2 : ℝ) ^ M := by
  have hfinite := reciprocal_finite_multiplicative_maximum hu hh hlog
  rw [← normalized_card_shellPrefixMultiplicativeHit M h hhM u] at hfinite
  have hcardNat := Finset.card_le_card
    (shellPrefixMultiplicativeHit_subset_shellTargetHeightFailure
      (u := u) hhM htarget)
  have hcard :
      ((shellPrefixMultiplicativeHit M h hhM u).card : ℝ) ≤
        (shellTargetHeightFailure M f u).card := by
    exact_mod_cast hcardNat
  exact hfinite.1.trans <|
    div_le_div_of_nonneg_right hcard (by positivity)

/-! ## Periodic residue blocks and the fixed-ceiling lower density -/

/-- The global set of sources without a simultaneous target-and-height
witness. -/
def targetHeightFailureSet (f : ℕ → ℝ) (u : ℝ) : Set ℕ :=
  {n | ¬HasTargetHeightWitness f u n}

/-- Prefix count for the global target-and-height failure set. -/
noncomputable def targetHeightFailureCount
    (f : ℕ → ℝ) (u : ℝ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range X).filter fun n => n ∈ targetHeightFailureSet f u).card

noncomputable def targetHeightFailureFinset
    (f : ℕ → ℝ) (u : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter fun n => n ∈ targetHeightFailureSet f u

/-- Complete periodic blocks of the length-`h` hit residues.  Blocks below
`N` are omitted so that an eventual target bound may be applied uniformly. -/
noncomputable def periodicMultiplicativeHitBlock
    (N t h : ℕ) (u : ℝ) : Finset ℕ := by
  classical
  let blocks := (Finset.Ico N t).product (multiplicativeHitResidues h u)
  exact blocks.map (Nat.divModEquiv (2 ^ h)).symm.toEmbedding

theorem card_periodicMultiplicativeHitBlock
    (N t h : ℕ) (u : ℝ) :
    (periodicMultiplicativeHitBlock N t h u).card =
      (t - N) * multiplicativeHitCount u h 1 := by
  classical
  rw [periodicMultiplicativeHitBlock, Finset.card_map]
  calc
    ((Finset.Ico N t).product (multiplicativeHitResidues h u)).card =
        (Finset.Ico N t).card * (multiplicativeHitResidues h u).card :=
      Finset.card_product _ _
    _ = (t - N) * multiplicativeHitCount u h 1 := by
      rw [Nat.card_Ico, card_multiplicativeHitResidues]

theorem periodicMultiplicativeHitBlock_crosses
    {N t h n : ℕ} {u : ℝ}
    (hn : n ∈ periodicMultiplicativeHitBlock N t h u) :
    N ≤ n ∧ n < t * 2 ^ h ∧
      crossesMultiplicativeFrom u h 1 (boolParityWord h n) := by
  classical
  rw [periodicMultiplicativeHitBlock, Finset.mem_map] at hn
  obtain ⟨p, hp, rfl⟩ := hn
  have hpMem := Finset.mem_product.mp hp
  have hpBlock := Finset.mem_Ico.mp hpMem.1
  have hpResidue := hpMem.2
  have hqPos : 0 < 2 ^ h := pow_pos (by omega) h
  have hlower : N ≤ (Nat.divModEquiv (2 ^ h)).symm p := by
    rw [Nat.divModEquiv_symm_apply]
    have hqOne : 1 ≤ 2 ^ h := hqPos
    calc
      N ≤ p.1 := hpBlock.1
      _ = p.1 * 1 := by omega
      _ ≤ p.1 * 2 ^ h := Nat.mul_le_mul_left p.1 hqOne
      _ ≤ p.1 * 2 ^ h + p.2 := Nat.le_add_right _ _
  have hupper : (Nat.divModEquiv (2 ^ h)).symm p < t * 2 ^ h := by
    rw [Nat.divModEquiv_symm_apply]
    calc
      p.1 * 2 ^ h + p.2 < p.1 * 2 ^ h + 2 ^ h :=
        Nat.add_lt_add_left p.2.isLt _
      _ = (p.1 + 1) * 2 ^ h := by ring
      _ ≤ t * 2 ^ h :=
        Nat.mul_le_mul_right (2 ^ h) (Nat.succ_le_of_lt hpBlock.2)
  have hcrossCode :
      crossesMultiplicativeFrom u h 1 (boolParityCode h p.2) := by
    rw [multiplicativeHitResidues] at hpResidue
    exact (Finset.mem_filter.mp hpResidue).2
  have hmod :
      (Nat.divModEquiv (2 ^ h)).symm p % 2 ^ h = p.2 := by
    rw [Nat.divModEquiv_symm_apply]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt p.2.isLt]
  have hword :
      boolParityCode h p.2 =
        boolParityWord h ((Nat.divModEquiv (2 ^ h)).symm p) := by
    rw [boolParityCode_eq_word]
    change boolParityWord h (p.2 : ℕ) =
      boolParityWord h ((Nat.divModEquiv (2 ^ h)).symm p)
    rw [← hmod, boolParityWord_mod]
  refine ⟨hlower, hupper, ?_⟩
  change crossesMultiplicativeFrom u h 1
    (boolParityWord h ((Nat.divModEquiv (2 ^ h)).symm p))
  rwa [← hword]

theorem not_hasTargetHeightWitness_of_prefix_crossing
    {h n : ℕ} {u : ℝ} {f : ℕ → ℝ}
    (hn : 0 < n)
    (htarget : f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hcross : crossesMultiplicativeFrom u h 1 (boolParityWord h n)) :
    ¬HasTargetHeightWitness f u n := by
  intro hwitness
  obtain ⟨k, hkTarget, hkHeight⟩ := hwitness
  have hhk : h < k := by
    by_contra hnot
    have hkh : k ≤ h := Nat.le_of_not_gt hnot
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ h :=
      pow_le_pow_right₀ (by norm_num) hkh
    have hdiv :
        (n : ℝ) / (2 : ℝ) ^ h ≤ (n : ℝ) / (2 : ℝ) ^ k :=
      (div_le_div_iff_of_pos_left hnPos (by positivity) (by positivity)).2 hpow
    have hlower := orbit_lower_by_halving n k
    linarith
  obtain ⟨j, hjh, hj⟩ :=
    exists_multiplicative_prefix_gt_of_crosses hcross
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscaled := mul_lt_mul_of_pos_right hj hnPos
  have hscaled' :
      u * (n : ℝ) <
        ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) := by
    simpa using hscaled
  have hjHigh := hscaled'.trans_le (pure_multiplicative_le_orbit n j)
  exact (not_lt_of_ge (hkHeight j (hjh.trans hhk.le))) hjHigh

theorem periodicMultiplicativeHitBlock_subset_targetHeightFailure
    {N t h X : ℕ} (hN : 1 ≤ N) (hblocks : t * 2 ^ h ≤ X)
    {u : ℝ} {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, N ≤ n →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    periodicMultiplicativeHitBlock N t h u ⊆
      targetHeightFailureFinset f u X := by
  classical
  intro n hn
  obtain ⟨hnN, hnUpper, hcross⟩ :=
    periodicMultiplicativeHitBlock_crosses hn
  have hnPos : 0 < n := hN.trans hnN
  simp only [targetHeightFailureFinset, Finset.mem_filter,
    Finset.mem_range, targetHeightFailureSet, Set.mem_setOf_eq]
  exact ⟨hnUpper.trans_le hblocks,
    not_hasTargetHeightWitness_of_prefix_crossing hnPos
      (htarget n hnN) hcross⟩

theorem targetHeightFailureCount_ge_periodicBlock
    {N t h X : ℕ} (hN : 1 ≤ N) (hblocks : t * 2 ^ h ≤ X)
    {u : ℝ} {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, N ≤ n →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    (t - N) * multiplicativeHitCount u h 1 ≤
      targetHeightFailureCount f u X := by
  classical
  rw [← card_periodicMultiplicativeHitBlock N t h u]
  have hcard := Finset.card_le_card
    (periodicMultiplicativeHitBlock_subset_targetHeightFailure
      (u := u) hN hblocks htarget)
  simpa [targetHeightFailureCount, targetHeightFailureFinset] using hcard

/-! ## Lower natural density -/

noncomputable def lowerDensityCount (E : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range X).filter fun n => n ∈ E).card

/-- Lower natural density at least `d`, in the equivalent strict-test form:
every `d' < d` is eventually a lower bound for the prefix proportions. -/
def LowerNaturalDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ d' : ℝ, d' < d →
    ∀ᶠ X : ℕ in Filter.atTop,
      d' ≤ (lowerDensityCount E X : ℝ) / (X : ℝ)

theorem lowerNaturalDensityAtLeast_targetHeightFailure_fixedPrefix
    {h : ℕ} {u : ℝ} {f : ℕ → ℝ}
    (htarget : ∀ᶠ n : ℕ in Filter.atTop,
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    LowerNaturalDensityAtLeast (targetHeightFailureSet f u)
      ((multiplicativeHitCount u h 1 : ℝ) / (2 : ℝ) ^ h) := by
  intro d hd
  obtain ⟨N₀, hN₀⟩ := (Filter.eventually_atTop.1 htarget)
  let N := max 1 N₀
  let q := 2 ^ h
  let a := multiplicativeHitCount u h 1
  have hN : 1 ≤ N := le_max_left _ _
  have htargetN : ∀ n : ℕ, N ≤ n →
      f n < (n : ℝ) / (2 : ℝ) ^ h := by
    intro n hn
    exact hN₀ n ((le_max_right 1 N₀).trans hn)
  have hqPos : 0 < q := by dsimp [q]; positivity
  have hgap : 0 < (a : ℝ) / (q : ℝ) - d := by
    have hd' : d < (a : ℝ) / (q : ℝ) := by
      simpa [a, q] using hd
    linarith
  let threshold : ℝ :=
    max (((N + 1) * q : ℕ) : ℝ)
      (2 * (((N + 1) * a : ℕ) : ℝ) /
        ((a : ℝ) / (q : ℝ) - d))
  obtain ⟨X₀ : ℕ, hX₀⟩ := exists_nat_gt threshold
  refine Filter.eventually_atTop.2 ⟨X₀, ?_⟩
  intro X hX
  have hXR : threshold < (X : ℝ) :=
    hX₀.trans_le (by exact_mod_cast hX)
  have hXblockR : (((N + 1) * q : ℕ) : ℝ) < X :=
    (le_max_left _ _).trans_lt hXR
  have hXblock : (N + 1) * q ≤ X := by
    exact_mod_cast hXblockR.le
  have hXposNat : 0 < X :=
    (Nat.mul_pos (by omega) hqPos).trans_le hXblock
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXposNat
  let t := X / q
  have hNt : N + 1 ≤ t := by
    dsimp [t]
    exact (Nat.le_div_iff_mul_le hqPos).2 hXblock
  have htN : N ≤ t := by omega
  have htqX : t * 2 ^ h ≤ X := by
    dsimp [t, q] at *
    exact Nat.div_mul_le_self X (2 ^ h)
  have hcountNat := targetHeightFailureCount_ge_periodicBlock
    (u := u) hN htqX htargetN
  have hcount :
      (((t - N) * a : ℕ) : ℝ) ≤
        targetHeightFailureCount f u X := by
    dsimp [a]
    exact_mod_cast hcountNat
  have hcount' :
      ((t : ℝ) - (N : ℝ)) * (a : ℝ) ≤
        (targetHeightFailureCount f u X : ℝ) := by
    rw [← Nat.cast_sub htN, ← Nat.cast_mul]
    exact hcount
  have hxltNat : X < (t + 1) * q := by
    dsimp [t]
    calc
      X < X / q * q + q := Nat.lt_div_mul_add hqPos
      _ = (X / q + 1) * q := by ring
  have hxlt : (X : ℝ) < ((t : ℝ) + 1) * (q : ℝ) := by
    exact_mod_cast hxltNat
  have htailR :
      2 * (((N + 1) * a : ℕ) : ℝ) /
          ((a : ℝ) / (q : ℝ) - d) < X :=
    (le_max_right _ _).trans_lt hXR
  have htail :
      (((N + 1) * a : ℕ) : ℝ) / (X : ℝ) <
        ((a : ℝ) / (q : ℝ) - d) / 2 := by
    apply (div_lt_div_iff₀ hXpos (by norm_num : (0 : ℝ) < 2)).2
    have hmul := (div_lt_iff₀ hgap).1 htailR
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hperiodic :
      (a : ℝ) / (q : ℝ) -
          (((N + 1) * a : ℕ) : ℝ) / (X : ℝ) ≤
        ((t : ℝ) - (N : ℝ)) * (a : ℝ) / (X : ℝ) := by
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hqPos
    have ha : 0 ≤ (a : ℝ) := by positivity
    have hxdiv : (X : ℝ) / (q : ℝ) ≤ (t : ℝ) + 1 :=
      (div_le_iff₀ hqR).2 hxlt.le
    have hamul :
        (a : ℝ) * ((X : ℝ) / (q : ℝ)) ≤
          (a : ℝ) * ((t : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hxdiv ha
    apply (le_div_iff₀ hXpos).2
    calc
      ((a : ℝ) / (q : ℝ) -
          (((N + 1) * a : ℕ) : ℝ) / (X : ℝ)) * (X : ℝ) =
          (a : ℝ) * ((X : ℝ) / (q : ℝ)) -
            (((N + 1) * a : ℕ) : ℝ) := by field_simp
      _ ≤ (a : ℝ) * ((t : ℝ) + 1) -
            (((N + 1) * a : ℕ) : ℝ) :=
        sub_le_sub_right hamul _
      _ = ((t : ℝ) - (N : ℝ)) * (a : ℝ) := by
        push_cast
        ring
  have hdPeriodic :
      d < (a : ℝ) / (q : ℝ) -
        (((N + 1) * a : ℕ) : ℝ) / (X : ℝ) := by
    linarith
  have hratio :
      ((t : ℝ) - (N : ℝ)) * (a : ℝ) / (X : ℝ) ≤
        (targetHeightFailureCount f u X : ℝ) / (X : ℝ) :=
    div_le_div_of_nonneg_right hcount' hXpos.le
  have hresult :
      d ≤ (targetHeightFailureCount f u X : ℝ) / (X : ℝ) :=
    hdPeriodic.le.trans (hperiodic.trans hratio)
  change d ≤ (targetHeightFailureCount f u X : ℝ) / (X : ℝ)
  exact hresult

/-- Manuscript Proposition 8.1.  The hypothesis is the exact
prefix-unreachability consequence of `f(n) = o(n)` consumed by the proof. -/
theorem lowerNaturalDensityAtLeast_reciprocal_fixedCeiling
    {u : ℝ} (hu : 1 ≤ u) {f : ℕ → ℝ}
    (hsublinear : ∀ h : ℕ,
      ∀ᶠ n : ℕ in Filter.atTop,
        f n < (n : ℝ) / (2 : ℝ) ^ h) :
    LowerNaturalDensityAtLeast (targetHeightFailureSet f u) (2 / (3 * u)) := by
  intro d hd
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hDPos : 0 < 2 / (3 * u) := by positivity
  have hgap : 0 < 2 / (3 * u) - d := by linarith
  have hepsLogPos :
      0 < reciprocalMaximumEpsilon * Real.log 3 :=
    mul_pos reciprocalMaximumEpsilon_pos (Real.log_pos (by norm_num))
  let threshold : ℝ := max 1 <|
    max (Real.log u /
      (reciprocalMaximumEpsilon * Real.log 3))
      ((2 / (3 * u)) * reciprocalMaximumConstant /
        (2 / (3 * u) - d))
  obtain ⟨h : ℕ, hh⟩ := exists_nat_gt threshold
  have hhOneR : (1 : ℝ) < h :=
    (le_max_left _ _).trans_lt hh
  have hhPos : 0 < h := by
    exact_mod_cast (show (0 : ℝ) < h by linarith)
  have hhSlope :
      Real.log u /
          (reciprocalMaximumEpsilon * Real.log 3) < (h : ℝ) :=
    ((le_max_left _ _).trans (le_max_right (1 : ℝ) _)).trans_lt hh
  have hlog :
      Real.log u ≤
        reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3 := by
    have hmul := (div_lt_iff₀ hepsLogPos).1 hhSlope
    nlinarith
  have hhLoss :
      (2 / (3 * u)) * reciprocalMaximumConstant /
          (2 / (3 * u) - d) < (h : ℝ) :=
    ((le_max_right _ _).trans (le_max_right (1 : ℝ) _)).trans_lt hh
  have hlossMul := (div_lt_iff₀ hgap).1 hhLoss
  have hhRPos : 0 < (h : ℝ) := by exact_mod_cast hhPos
  have hlowerD :
      d < (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) := by
    have hloss :
        (2 / (3 * u)) * reciprocalMaximumConstant / (h : ℝ) <
          2 / (3 * u) - d := by
      apply (div_lt_iff₀ hhRPos).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlossMul
    calc
      d < 2 / (3 * u) -
          (2 / (3 * u)) * reciprocalMaximumConstant / (h : ℝ) := by
        linarith
      _ = (2 / (3 * u)) *
          (1 - reciprocalMaximumConstant / (h : ℝ)) := by ring
  have hfinite := reciprocal_finite_multiplicative_maximum hu hhPos hlog
  have hdHit :
      d < (multiplicativeHitCount u h 1 : ℝ) / (2 : ℝ) ^ h :=
    hlowerD.trans_le hfinite.1
  exact lowerNaturalDensityAtLeast_targetHeightFailure_fixedPrefix
    (hsublinear h) d hdHit

end

end FirstPassageLinearTransport
