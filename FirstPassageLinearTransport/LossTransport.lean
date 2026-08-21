/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Transport

/-!
# Loss-filtered first-passage transport

This module formalizes the reverse-product loss used by the optimized
first-passage re-certification argument.  The filter is sourcewise and exact:
no generated-distribution or independence hypothesis is introduced.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

noncomputable section

/-- Sum of the exact reverse losses through time `h`. -/
def reverseLossTotal (n h : ℕ) : ℚ :=
  ∑ i ∈ Finset.range h, reverseLoss n i

/-- Reverse loss rescaled by the landing threshold `Y`. -/
def scaledReverseLoss (Y n h : ℕ) : ℚ :=
  (Y : ℚ) * reverseLossTotal n h


theorem reverseProduct_le_one {n : ℕ} (hn : 0 < n) (h : ℕ) :
    reverseProduct n h ≤ 1 := by
  rw [reverseProduct_eq_prod_loss]
  apply Finset.prod_le_one
  · intro i hi
    exact sub_nonneg.mpr (reverseLoss_le_one hn i)
  · intro i hi
    linarith [reverseLoss_nonneg n i]

theorem one_sub_reverseLossTotal_le_reverseProduct
    {n : ℕ} (hn : 0 < n) (h : ℕ) :
    1 - reverseLossTotal n h ≤ reverseProduct n h := by
  rw [reverseLossTotal, reverseProduct_eq_prod_loss]
  apply one_sub_sum_le_prod
  intro i hi
  exact ⟨reverseLoss_nonneg n i, reverseLoss_le_one hn i⟩

theorem reverseLossTotal_le_div_of_scaled_le
    {Y n h : ℕ} {D : ℚ} (hY : 0 < Y)
    (hloss : scaledReverseLoss Y n h ≤ D) :
    reverseLossTotal n h ≤ D / (Y : ℚ) := by
  have hYQ : (0 : ℚ) < Y := by exact_mod_cast hY
  apply (le_div_iff₀ hYQ).2
  simpa [scaledReverseLoss, mul_comm] using hloss

theorem one_sub_div_le_reverseProduct_of_scaledLoss
    {Y n h : ℕ} {D : ℚ} (hn : 0 < n) (hY : 0 < Y)
    (hloss : scaledReverseLoss Y n h ≤ D) :
    1 - D / (Y : ℚ) ≤ reverseProduct n h := by
  have htotal := reverseLossTotal_le_div_of_scaled_le hY hloss
  exact (sub_le_sub_left htotal 1).trans
    (one_sub_reverseLossTotal_le_reverseProduct hn h)

/-- A tagged fiber restricted to sources with scaled reverse loss at most
`D`. -/
noncomputable def lossFilteredTaggedFiber
    (M Y h y : ℕ) (D : ℚ) : Finset ℕ := by
  classical
  exact (taggedFiber M Y h y).filter fun n => scaledReverseLoss Y n h ≤ D

@[simp] theorem mem_lossFilteredTaggedFiber
    {M Y h y n : ℕ} {D : ℚ} :
    n ∈ lossFilteredTaggedFiber M Y h y D ↔
      n ∈ dyadicShell M ∧ IsFirstPassage Y n h ∧ orbit h n = y ∧
        scaledReverseLoss Y n h ≤ D := by
  classical
  simp [lossFilteredTaggedFiber, and_assoc]

/-- Loss-filtered sources in one half-open dyadic shell and one tag have one
common odd count. -/
theorem lossFiltered_oddCount_rigidity
    {M Y h y n₁ n₂ : ℕ} {D : ℚ}
    (hn₁ : n₁ ∈ lossFilteredTaggedFiber M Y h y D)
    (hn₂ : n₂ ∈ lossFilteredTaggedFiber M Y h y D)
    (hY : 0 < Y) (_hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    oddCount n₁ h = oddCount n₂ h := by
  have hmem₁ := mem_lossFilteredTaggedFiber.mp hn₁
  have hmem₂ := mem_lossFilteredTaggedFiber.mp hn₂
  have hn₁pos : 0 < n₁ := by
    have hlo := (mem_dyadicShell.mp hmem₁.1).1
    have hp : 0 < 2 ^ M := by positivity
    omega
  have hn₂pos : 0 < n₂ := by
    have hlo := (mem_dyadicShell.mp hmem₂.1).1
    have hp : 0 < 2 ^ M := by positivity
    omega
  have hP₁low := one_sub_div_le_reverseProduct_of_scaledLoss
    hn₁pos hY hmem₁.2.2.2
  have hP₂low := one_sub_div_le_reverseProduct_of_scaledLoss
    hn₂pos hY hmem₂.2.2.2
  have hP₁up := reverseProduct_le_one hn₁pos h
  have hP₂up := reverseProduct_le_one hn₂pos h
  have hfactor : (2 / 3 : ℚ) ≤ 1 - D / (Y : ℚ) := by linarith
  have hA₁ := reverseScale_nonneg n₁ h
  have hA₂ := reverseScale_nonneg n₂ h
  have hid₁ : (n₁ : ℚ) = reverseScale n₁ h * reverseProduct n₁ h := by
    simpa [reverseScale] using reverse_product_identity hn₁pos h
  have hid₂ : (n₂ : ℚ) = reverseScale n₂ h * reverseProduct n₂ h := by
    simpa [reverseScale] using reverse_product_identity hn₂pos h
  rcases lt_trichotomy (oddCount n₁ h) (oddCount n₂ h) with hs | hs | hs
  · have hscale := reverseScale_three_le_of_same_landing
      hmem₁.2.2.1 hmem₂.2.2.1 hs
    have hn₁lower : (2 / 3 : ℚ) * reverseScale n₁ h ≤ n₁ := by
      rw [hid₁]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hfactor.trans hP₁low) hA₁
    have hn₂upper : (n₂ : ℚ) ≤ reverseScale n₂ h := by
      rw [hid₂]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hP₂up hA₂
    have htwiceQ : (2 : ℚ) * n₂ ≤ n₁ := by
      calc
        (2 : ℚ) * n₂ ≤ 2 * reverseScale n₂ h :=
          mul_le_mul_of_nonneg_left hn₂upper (by norm_num)
        _ ≤ (2 / 3 : ℚ) * reverseScale n₁ h := by nlinarith
        _ ≤ n₁ := hn₁lower
    have htwice : 2 * n₂ ≤ n₁ := by exact_mod_cast htwiceQ
    have hn₁lt := (mem_dyadicShell.mp hmem₁.1).2
    have hn₂lo := (mem_dyadicShell.mp hmem₂.1).1
    rw [pow_succ] at hn₁lt
    omega
  · exact hs
  · have hscale := reverseScale_three_le_of_same_landing
      hmem₂.2.2.1 hmem₁.2.2.1 hs
    have hn₂lower : (2 / 3 : ℚ) * reverseScale n₂ h ≤ n₂ := by
      rw [hid₂]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hfactor.trans hP₂low) hA₂
    have hn₁upper : (n₁ : ℚ) ≤ reverseScale n₁ h := by
      rw [hid₁]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hP₁up hA₁
    have htwiceQ : (2 : ℚ) * n₁ ≤ n₂ := by
      calc
        (2 : ℚ) * n₁ ≤ 2 * reverseScale n₁ h :=
          mul_le_mul_of_nonneg_left hn₁upper (by norm_num)
        _ ≤ (2 / 3 : ℚ) * reverseScale n₂ h := by nlinarith
        _ ≤ n₂ := hn₂lower
    have htwice : 2 * n₁ ≤ n₂ := by exact_mod_cast htwiceQ
    have hn₂lt := (mem_dyadicShell.mp hmem₂.1).2
    have hn₁lo := (mem_dyadicShell.mp hmem₁.1).1
    rw [pow_succ] at hn₂lt
    omega

/-- Cardinality of one loss-filtered tagged fiber. -/
theorem lossFilteredTaggedFiber_bound
    {M Y h y : ℕ} {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTaggedFiber M Y h y D).card : ℚ) ≤
      1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ) := by
  classical
  by_cases hf : (lossFilteredTaggedFiber M Y h y D).Nonempty
  · rcases hf with ⟨n₀, hn₀⟩
    let A : ℚ := reverseScale n₀ h
    let ε : ℚ := D / (Y : ℚ)
    have hmem₀ := mem_lossFilteredTaggedFiber.mp hn₀
    have hn₀pos : 0 < n₀ := by
      have hlo := (mem_dyadicShell.mp hmem₀.1).1
      have hp : 0 < 2 ^ M := by positivity
      omega
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact reverseScale_nonneg n₀ h
    have hε0 : 0 ≤ ε := by
      dsimp [ε]
      positivity
    have hfactor : (2 / 3 : ℚ) ≤ 1 - ε := by
      dsimp [ε]
      linarith
    have hbounds : ∀ n ∈ lossFilteredTaggedFiber M Y h y D,
        (1 - ε) * A ≤ (n : ℚ) ∧ (n : ℚ) ≤ A := by
      intro n hn
      have hmem := mem_lossFilteredTaggedFiber.mp hn
      have hnpos : 0 < n := by
        have hlo := (mem_dyadicShell.mp hmem.1).1
        have hp : 0 < 2 ^ M := by positivity
        omega
      have hcount := lossFiltered_oddCount_rigidity hn hn₀ hY hD hsmall
      have hscale : reverseScale n h = A := by
        dsimp [A]
        simp only [reverseScale, hmem.2.2.1, hmem₀.2.2.1, hcount]
      have hid : (n : ℚ) = A * reverseProduct n h := by
        rw [← hscale]
        simpa [reverseScale] using reverse_product_identity hnpos h
      have hpLow := one_sub_div_le_reverseProduct_of_scaledLoss
        hnpos hY hmem.2.2.2
      have hpUp := reverseProduct_le_one hnpos h
      dsimp [ε] at hid hpLow ⊢
      constructor
      · rw [hid]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLow hA0
      · rw [hid]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpUp hA0
    have hn₀lower := (hbounds n₀ hn₀).1
    have hn₀ltNat := (mem_dyadicShell.mp hmem₀.1).2
    have hn₀lt : (n₀ : ℚ) < (2 : ℚ) ^ (M + 1) := by
      exact_mod_cast hn₀ltNat
    have hAupper : A < (3 / 2 : ℚ) * (2 : ℚ) ^ (M + 1) := by
      have htwoThird : (2 / 3 : ℚ) * A ≤ n₀ :=
        (mul_le_mul_of_nonneg_right hfactor hA0).trans hn₀lower
      nlinarith
    have hspan :
        ((lossFilteredTaggedFiber M Y h y D).max' ⟨n₀, hn₀⟩ : ℚ) -
            ((lossFilteredTaggedFiber M Y h y D).min' ⟨n₀, hn₀⟩ : ℚ) ≤
          3 * D * (2 : ℚ) ^ M / (Y : ℚ) := by
      let s := lossFilteredTaggedFiber M Y h y D
      have hmaxMem : s.max' ⟨n₀, hn₀⟩ ∈ s := Finset.max'_mem _ _
      have hminMem : s.min' ⟨n₀, hn₀⟩ ∈ s := Finset.min'_mem _ _
      have hmax := (hbounds (s.max' ⟨n₀, hn₀⟩) hmaxMem).2
      have hmin := (hbounds (s.min' ⟨n₀, hn₀⟩) hminMem).1
      have hdiff :
          ((s.max' ⟨n₀, hn₀⟩ : ℕ) : ℚ) -
              ((s.min' ⟨n₀, hn₀⟩ : ℕ) : ℚ) ≤ ε * A := by
        nlinarith
      have hmul : ε * A ≤
          ε * ((3 / 2 : ℚ) * (2 : ℚ) ^ (M + 1)) :=
        mul_le_mul_of_nonneg_left hAupper.le hε0
      calc
        ((s.max' ⟨n₀, hn₀⟩ : ℕ) : ℚ) -
              ((s.min' ⟨n₀, hn₀⟩ : ℕ) : ℚ) ≤ ε * A := hdiff
        _ ≤ ε * ((3 / 2 : ℚ) * (2 : ℚ) ^ (M + 1)) := hmul
        _ = 3 * D * (2 : ℚ) ^ M / (Y : ℚ) := by
          dsimp [ε]
          rw [pow_succ]
          ring
    have hcard := finset_card_le_one_add_span
      (lossFilteredTaggedFiber M Y h y D) ⟨n₀, hn₀⟩
    linarith
  · have hempty : lossFilteredTaggedFiber M Y h y D = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hf
    rw [hempty]
    simp
    positivity

/-- All first-passage sources represented by a target cell and satisfying the
scaled reverse-loss filter.  As in `transportedSources`, the `range H`
parameter uses the actual time `t + 1`. -/
noncomputable def lossFilteredTransportedSources
    (M Y H : ℕ) (B : Finset ℕ) (D : ℚ) : Finset ℕ := by
  classical
  exact (Finset.range H).biUnion fun t =>
    B.biUnion fun y => lossFilteredTaggedFiber M Y (t + 1) y D

@[simp] theorem mem_lossFilteredTransportedSources
    {M Y H n : ℕ} {B : Finset ℕ} {D : ℚ} :
    n ∈ lossFilteredTransportedSources M Y H B D ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage Y n h ∧
          orbit h n ∈ B ∧ scaledReverseLoss Y n h ≤ D := by
  classical
  constructor
  · intro hn
    unfold lossFilteredTransportedSources at hn
    rcases Finset.mem_biUnion.mp hn with ⟨t, ht, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨y, hy, hn⟩
    have htag := mem_lossFilteredTaggedFiber.mp hn
    refine ⟨htag.1, t + 1, by omega, ?_, htag.2.1, ?_, htag.2.2.2⟩
    · exact Finset.mem_range.mp ht
    · simpa [htag.2.2.1] using hy
  · rintro ⟨hShell, h, hpos, hhH, hfp, hB, hloss⟩
    unfold lossFilteredTransportedSources
    have ht : h - 1 < H := by omega
    have htime : h - 1 + 1 = h := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨h - 1, Finset.mem_range.mpr ht, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨orbit h n, hB, ?_⟩
    simpa [htime] using
      (mem_lossFilteredTaggedFiber.mpr ⟨hShell, hfp, rfl, hloss⟩ :
        n ∈ lossFilteredTaggedFiber M Y h (orbit h n) D)

/-- Loss-filtered arbitrary-target transport.  The time aggregation costs one
factor `H`; the second factor present in the unfiltered theorem is replaced by
the sourcewise scaled-loss budget `D`. -/
theorem lossFiltered_arbitraryTarget_transport
    {M Y H : ℕ} (B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) :
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) *
        (B.card : ℚ) := by
  classical
  have houter := card_biUnion_le_sum (Finset.range H)
    (fun t => B.biUnion fun y =>
      lossFilteredTaggedFiber M Y (t + 1) y D)
  have hinner :
      ∀ t ∈ Finset.range H,
        (B.biUnion fun y =>
            lossFilteredTaggedFiber M Y (t + 1) y D).card ≤
          ∑ y ∈ B, (lossFilteredTaggedFiber M Y (t + 1) y D).card := by
    intro t _ht
    exact card_biUnion_le_sum B fun y =>
      lossFilteredTaggedFiber M Y (t + 1) y D
  have hcardNat :
      (lossFilteredTransportedSources M Y H B D).card ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (lossFilteredTaggedFiber M Y (t + 1) y D).card := by
    unfold lossFilteredTransportedSources
    calc
      ((Finset.range H).biUnion fun t =>
          B.biUnion fun y =>
            lossFilteredTaggedFiber M Y (t + 1) y D).card ≤
          ∑ t ∈ Finset.range H,
            (B.biUnion fun y =>
              lossFilteredTaggedFiber M Y (t + 1) y D).card := houter
      _ ≤ ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (lossFilteredTaggedFiber M Y (t + 1) y D).card := by
            apply Finset.sum_le_sum
            intro t ht
            exact hinner t ht
  have hcardQ :
      ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((lossFilteredTaggedFiber M Y (t + 1) y D).card : ℚ) := by
    exact_mod_cast hcardNat
  let K : ℚ := 1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)
  calc
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((lossFilteredTaggedFiber M Y (t + 1) y D).card : ℚ) := hcardQ
    _ ≤ ∑ _t ∈ Finset.range H, ∑ _y ∈ B, K := by
      apply Finset.sum_le_sum
      intro t _ht
      apply Finset.sum_le_sum
      intro y _hy
      exact lossFilteredTaggedFiber_bound hY hD hsmall
    _ = (H : ℚ) * (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) *
        (B.card : ℚ) := by
      simp [K]
      ring

/-- The uniform form used by the nested re-certification argument.  When the
landing threshold lies below the source shell, the additive `1` in the exact
transport bound is absorbed by `2^M / Y`. -/
theorem lossFiltered_arbitraryTarget_transport_uniform
    {M Y H : ℕ} (B : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) (hYM : Y < 2 ^ M) :
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
        (B.card : ℚ) := by
  have hYQ : (0 : ℚ) < (Y : ℚ) := by exact_mod_cast hY
  have hYMq : (Y : ℚ) < (2 : ℚ) ^ M := by exact_mod_cast hYM
  have hratio : (1 : ℚ) ≤ (2 : ℚ) ^ M / (Y : ℚ) := by
    apply (le_div_iff₀ hYQ).2
    simpa using hYMq.le
  have hK :
      1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ) ≤
        (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) := by
    calc
      1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ) ≤
          (2 : ℚ) ^ M / (Y : ℚ) +
            3 * D * (2 : ℚ) ^ M / (Y : ℚ) :=
        by
          simpa [add_comm] using
            add_le_add_right hratio
              (3 * D * (2 : ℚ) ^ M / (Y : ℚ))
      _ = (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) := by ring
  have hbase := lossFiltered_arbitraryTarget_transport
    (M := M) (Y := Y) (H := H) (D := D) B hY hD hsmall
  have hcoef : 0 ≤ (H : ℚ) * (B.card : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hK hcoef
  calc
    ((lossFilteredTransportedSources M Y H B D).card : ℚ) ≤
        (H : ℚ) *
          (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) *
            (B.card : ℚ) := hbase
    _ = ((H : ℚ) * (B.card : ℚ)) *
          (1 + 3 * D * (2 : ℚ) ^ M / (Y : ℚ)) := by ring
    _ ≤ ((H : ℚ) * (B.card : ℚ)) *
          ((1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ)) := hmul
    _ = (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
          (B.card : ℚ) := by ring

/-- Arbitrary source restriction can only decrease loss-filtered transported
mass. -/
theorem lossFiltered_arbitraryTarget_transport_restricted
    {M Y H : ℕ} (B A : Finset ℕ) {D : ℚ}
    (hY : 0 < Y) (hD : 0 ≤ D)
    (hsmall : D / (Y : ℚ) ≤ 1 / 3) (hYM : Y < 2 ^ M) :
    (((lossFilteredTransportedSources M Y H B D) ∩ A).card : ℚ) ≤
      (H : ℚ) * (1 + 3 * D) * (2 : ℚ) ^ M / (Y : ℚ) *
        (B.card : ℚ) := by
  have hcard :
      (((lossFilteredTransportedSources M Y H B D) ∩ A).card : ℚ) ≤
        ((lossFilteredTransportedSources M Y H B D).card : ℚ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  exact hcard.trans
    (lossFiltered_arbitraryTarget_transport_uniform B hY hD hsmall hYM)

end

end FirstPassageLinearTransport
