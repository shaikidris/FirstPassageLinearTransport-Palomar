/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.AdjustableBarrierDensity
import FirstPassageLinearTransport.RankScaledLoss

/-!
# Exact first-bad landing envelope

This module performs the finite union used by the optimized terminal profile.
It keeps the bad-target cardinality at each landing rank explicit.  The
separate semantic step that puts every recursively generated first failure in
this envelope is not assumed here.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

noncomputable section

/-- The half-open first-passage landing band `(2^(q-1), 2^q]`. -/
def landingBand (q : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ (q - 1)) (2 ^ q)

/-- Points in the landing band which fail the orbit-envelope certification. -/
noncomputable def landingBad (q : ℕ) (t : ℝ) : Finset ℕ := by
  classical
  exact (landingBand q).filter fun y => y ∉ initialWindowGood t

@[simp] theorem mem_landingBad {q y : ℕ} {t : ℝ} :
    y ∈ landingBad q t ↔
      2 ^ (q - 1) < y ∧ y ≤ 2 ^ q ∧ y ∉ initialWindowGood t := by
  classical
  simp [landingBad, landingBand, and_assoc]

/-- Apart from the upper power-of-two endpoint, the landing target lies in
the ordinary dyadic shell of rank `q-1`. -/
theorem landingBad_subset_insert_shellBad
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    landingBad q t ⊆ insert (2 ^ q) (shellInitialWindowBad (q - 1) t) := by
  classical
  intro y hy
  have hmem := mem_landingBad.mp hy
  by_cases hyTop : y = 2 ^ q
  · simp [hyTop]
  · have hyLt : y < 2 ^ q := lt_of_le_of_ne hmem.2.1 hyTop
    have hyShell : y ∈ dyadicShell (q - 1) := by
      rw [mem_dyadicShell]
      constructor
      · exact hmem.1.le
      · simpa [Nat.sub_add_cancel hq] using hyLt
    have hyBad : y ∈ shellBad (initialWindowGood t) (q - 1) := by
      rw [shellBad, Finset.mem_filter]
      exact ⟨hyShell, hmem.2.2⟩
    rw [shellBad_initialWindowGood] at hyBad
    simp [hyBad]

theorem card_landingBad_le_shellBad_add_one
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    (landingBad q t).card ≤ (shellInitialWindowBad (q - 1) t).card + 1 := by
  have hcard := Finset.card_le_card (landingBad_subset_insert_shellBad hq t)
  exact hcard.trans (Finset.card_insert_le _ _)

/-- Entropy-sharp target-cardinality bound for the actual first-passage
landing band, including its single upper power-of-two endpoint. -/
theorem eventually_card_landingBad_adjustable_le
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
  have htail := eventually_card_shellInitialWindowBad_adjustable_le
    hlambda0 hlambda1 ht0 htA
  rw [Filter.eventually_atTop] at htail ⊢
  obtain ⟨M0, hM0⟩ := htail
  refine ⟨M0 + 1, ?_⟩
  intro q hqM
  have hq1 : 1 ≤ q := by omega
  have hMq : M0 ≤ q - 1 := by omega
  have hshell := hM0 (q - 1) hMq
  have hcardNat := card_landingBad_le_shellBad_add_one hq1 t
  have hcardReal :
      ((landingBad q t).card : ℝ) ≤
        ((shellInitialWindowBad (q - 1) t).card : ℝ) + 1 := by
    exact_mod_cast hcardNat
  calc
    ((landingBad q t).card : ℝ) ≤
        ((shellInitialWindowBad (q - 1) t).card : ℝ) + 1 := hcardReal
    _ ≤ ((2 : ℝ) ^ ((q - 1) + 1) *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t)))) + 1 :=
      by simpa [add_comm] using add_le_add_right hshell 1
    _ = 1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by
      rw [Nat.sub_add_cancel hq1]
      ring

/-- All direct first-passage sources whose landing lies in one of the bad
rank targets and whose scaled loss satisfies the rank budget. -/
noncomputable def firstBadLandingEnvelope
    (M L U H : ℕ) (r : ℚ) (t : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc L U).biUnion fun q =>
    lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
      (((q + 2 : ℕ) : ℚ) / r)

@[simp] theorem mem_firstBadLandingEnvelope
    {M L U H n : ℕ} {r : ℚ} {t : ℝ} :
    n ∈ firstBadLandingEnvelope M L U H r t ↔
      ∃ q : ℕ, L ≤ q ∧ q ≤ U ∧ n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage (2 ^ q) n h ∧
          orbit h n ∈ landingBad q t ∧
          scaledReverseLoss (2 ^ q) n h ≤ ((q + 2 : ℕ) : ℚ) / r := by
  classical
  simp only [firstBadLandingEnvelope, Finset.mem_biUnion,
    Finset.mem_Icc, mem_lossFilteredTransportedSources]
  aesop

/-- Exact rank-by-rank transport bound for the first-bad landing envelope. -/
theorem firstBadLandingEnvelope_card_le
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((firstBadLandingEnvelope M L U H r t).card : ℚ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by
  classical
  have houter := card_biUnion_le_sum (Finset.Icc L U) fun q =>
    lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
      (((q + 2 : ℕ) : ℚ) / r)
  have houterQ :
      ((firstBadLandingEnvelope M L U H r t).card : ℚ) ≤
        ∑ q ∈ Finset.Icc L U,
          ((lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
            (((q + 2 : ℕ) : ℚ) / r)).card : ℚ) := by
    unfold firstBadLandingEnvelope
    exact_mod_cast houter
  calc
    ((firstBadLandingEnvelope M L U H r t).card : ℚ) ≤
        ∑ q ∈ Finset.Icc L U,
          ((lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
            (((q + 2 : ℕ) : ℚ) / r)).card : ℚ) := houterQ
    _ ≤ ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqU : q ≤ U := (Finset.mem_Icc.mp hq).2
      have hqM : q < M := hqU.trans_lt hUM
      have hYM : 2 ^ q < 2 ^ M := Nat.pow_lt_pow_right (by omega) hqM
      have hD : (0 : ℚ) ≤ ((q + 2 : ℕ) : ℚ) / r := by positivity
      have htransport := lossFiltered_arbitraryTarget_transport_uniform
        (M := M) (Y := 2 ^ q) (H := H)
        (D := ((q + 2 : ℕ) : ℚ) / r)
        (landingBad q t) (by positivity) hD (hsmall q hq) hYM
      simpa using htransport



/-- A generated first-bad witness: a finite certified rank chain lands in a
bad target, within the declared time and rank window. -/
def HasGeneratedFirstBadLanding
    (r : ℚ) (t : ℝ) (n L U H : ℕ) : Prop :=
  ∃ h q : ℕ, L ≤ q ∧ q ≤ U ∧ 1 ≤ h ∧ h ≤ H ∧
    CertifiedRankChain r n h q ∧ orbit h n ∈ landingBad q t

/-- Sources in one outer shell carrying a generated first-bad witness. -/
noncomputable def generatedFirstBadSources
    (M L U H : ℕ) (r : ℚ) (t : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    HasGeneratedFirstBadLanding r t n L U H

@[simp] theorem mem_generatedFirstBadSources
    {M L U H n : ℕ} {r : ℚ} {t : ℝ} :
    n ∈ generatedFirstBadSources M L U H r t ↔
      n ∈ dyadicShell M ∧ HasGeneratedFirstBadLanding r t n L U H := by
  classical
  simp [generatedFirstBadSources]

/-- Every generated finite-chain first-bad witness lies in the direct
loss-filtered transport envelope. -/
theorem generatedFirstBadSources_subset_envelope
    {M L U H : ℕ} {r : ℚ} {t : ℝ} (hr : 0 < r) :
    generatedFirstBadSources M L U H r t ⊆
      firstBadLandingEnvelope M L U H r t := by
  intro n hn
  have hmem := mem_generatedFirstBadSources.mp hn
  rcases hmem.2 with ⟨h, q, hLq, hqU, hh1, hhH, hchain, hbad⟩
  have hfp := hchain.directFirstPassage
  have hloss := hchain.scaledReverseLoss_le hr
  exact mem_firstBadLandingEnvelope.mpr
    ⟨q, hLq, hqU, hmem.1, h, hh1, hhH, hfp, hbad, hloss⟩

theorem generatedFirstBadSources_card_le
    {M L U H : ℕ} {r : ℚ} (t : ℝ)
    (hr : 0 < r) (hUM : U < M)
    (hsmall : ∀ q ∈ Finset.Icc L U,
      ((((q + 2 : ℕ) : ℚ) / r) / ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((generatedFirstBadSources M L U H r t).card : ℚ) ≤
      ∑ q ∈ Finset.Icc L U,
        (H : ℚ) * (1 + 3 * (((q + 2 : ℕ) : ℚ) / r)) *
          (2 : ℚ) ^ M / (2 : ℚ) ^ q * ((landingBad q t).card : ℚ) := by
  have hcard := Finset.card_le_card
    (generatedFirstBadSources_subset_envelope
      (M := M) (L := L) (U := U) (H := H) (r := r) (t := t) hr)
  have hcardQ :
      ((generatedFirstBadSources M L U H r t).card : ℚ) ≤
        ((firstBadLandingEnvelope M L U H r t).card : ℚ) := by
    exact_mod_cast hcard
  exact hcardQ.trans (firstBadLandingEnvelope_card_le t hr hUM hsmall)

end

end FirstPassageLinearTransport
