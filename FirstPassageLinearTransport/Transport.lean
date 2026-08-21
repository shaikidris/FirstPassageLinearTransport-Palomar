/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.FirstPassage

/-!
# Arbitrary-target first-passage transport

This module formalizes the uniform tagged-fiber bound and arbitrary-target
linear transport.
-/

namespace FirstPassageLinearTransport

/-- A tagged first-passage fiber has uniformly bounded cardinality. -/
theorem taggedFiber_bound_uniform {M Y H h y : ℕ}
    (hY : 0 < Y) (hpos : 1 ≤ h) (hhH : h ≤ H)
    (hHY : (H : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hYM : Y < 2 ^ M) :
    ((taggedFiber M Y h y).card : ℚ) ≤
      (5 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := by
  have hYQ : (0 : ℚ) < (Y : ℚ) := by exact_mod_cast hY
  have htwoY : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
  have hhHq : (h : ℚ) ≤ (H : ℚ) := by exact_mod_cast hhH
  have hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3 := by
    exact (div_le_div_of_nonneg_right hhHq (by positivity)).trans hHY
  have hscaled := (div_le_iff₀ htwoY).mp hHY
  have hHupper : (H : ℚ) ≤ 2 * (Y : ℚ) / 3 := by
    nlinarith
  have hden : (0 : ℚ) < 2 * (Y : ℚ) - (h : ℚ) := by
    nlinarith
  have hdenLower : (4 / 3 : ℚ) * (Y : ℚ) ≤
      2 * (Y : ℚ) - (h : ℚ) := by
    nlinarith
  have hratioCross :
      (2 * (h : ℚ)) * (Y : ℚ) ≤
        ((3 / 2 : ℚ) * (H : ℚ)) *
          (2 * (Y : ℚ) - (h : ℚ)) := by
    have hleft :
        (2 * (h : ℚ)) * (Y : ℚ) ≤
          (2 * (H : ℚ)) * (Y : ℚ) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have hright :
        (2 * (H : ℚ)) * (Y : ℚ) ≤
          ((3 / 2 : ℚ) * (H : ℚ)) *
            (2 * (Y : ℚ) - (h : ℚ)) := by
      have := mul_le_mul_of_nonneg_left hdenLower
        (show 0 ≤ (3 / 2 : ℚ) * (H : ℚ) by positivity)
      nlinarith
    exact hleft.trans hright
  have hratio :
      (2 * (h : ℚ)) / (2 * (Y : ℚ) - (h : ℚ)) ≤
        ((3 / 2 : ℚ) * (H : ℚ)) / (Y : ℚ) := by
    exact (div_le_div_iff₀ hden hYQ).2 hratioCross
  have hpowNonneg : (0 : ℚ) ≤ (2 : ℚ) ^ M := by positivity
  have hterm :
      2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) ≤
        (3 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := by
    have := mul_le_mul_of_nonneg_right hratio hpowNonneg
    simpa [div_mul_eq_mul_div, mul_assoc] using this
  have hYMq : (Y : ℚ) < (2 : ℚ) ^ M := by exact_mod_cast hYM
  have hone : (1 : ℚ) ≤ (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := by
    apply (le_div_iff₀ hYQ).2
    have hHone : (1 : ℚ) ≤ (H : ℚ) := by exact_mod_cast (hpos.trans hhH)
    have hPowLe : (2 : ℚ) ^ M ≤ (H : ℚ) * (2 : ℚ) ^ M := by
      simpa using mul_le_mul_of_nonneg_right hHone hpowNonneg
    simpa using (le_of_lt hYMq).trans hPowLe
  have hraw := taggedFiber_bound (M := M) (Y := Y) (h := h) (y := y) hY hsmall
  have hterm' :
      2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) ≤
        (3 / 2 : ℚ) * ((H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)) := by
    calc
      2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) ≤
          (3 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := hterm
      _ = (3 / 2 : ℚ) * ((H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)) := by ring
  have hfinal :
      ((taggedFiber M Y h y).card : ℚ) ≤
        (5 / 2 : ℚ) * ((H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)) := by
    nlinarith
  convert hfinal using 1
  ring

theorem card_biUnion_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert]
      calc
        (f a ∪ s.biUnion f).card ≤ (f a).card + (s.biUnion f).card :=
          Finset.card_union_le _ _
        _ ≤ (f a).card + ∑ x ∈ s, (f x).card := by omega
        _ = ∑ x ∈ insert a s, (f x).card := by simp [ha]

/-- All sources represented by a target cell with passage time in `1,...,H`.
The `range H` parametrization uses the actual time `t+1`. -/
noncomputable def transportedSources (M Y H : ℕ) (B : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range H).biUnion fun t =>
    B.biUnion fun y => taggedFiber M Y (t + 1) y

@[simp] theorem mem_transportedSources {M Y H n : ℕ} {B : Finset ℕ} :
    n ∈ transportedSources M Y H B ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage Y n h ∧ orbit h n ∈ B := by
  classical
  constructor
  · intro hn
    unfold transportedSources at hn
    rcases Finset.mem_biUnion.mp hn with ⟨t, ht, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨y, hy, hn⟩
    have htag := mem_taggedFiber.mp hn
    refine ⟨htag.1, t + 1, by omega, ?_, htag.2.1, ?_⟩
    · exact Finset.mem_range.mp ht
    · simpa [htag.2.2] using hy
  · rintro ⟨hShell, h, hpos, hhH, hfp, hB⟩
    unfold transportedSources
    have ht : h - 1 < H := by omega
    have htime : h - 1 + 1 = h := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨h - 1, Finset.mem_range.mpr ht, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨orbit h n, hB, ?_⟩
    simpa [htime] using
      (mem_taggedFiber.mpr ⟨hShell, hfp, rfl⟩ :
        n ∈ taggedFiber M Y h (orbit h n))

/-- Arbitrary-target linear transport. -/
theorem arbitraryTarget_linear_transport {M Y H : ℕ} (B : Finset ℕ)
    (hY : 0 < Y) (_hH : 1 ≤ H)
    (hHY : (H : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hYM : Y < 2 ^ M) :
    ((transportedSources M Y H B).card : ℚ) ≤
      (5 / 2 : ℚ) * (H : ℚ) ^ 2 * (2 : ℚ) ^ M /
        (Y : ℚ) * (B.card : ℚ) := by
  classical
  have houter := card_biUnion_le_sum (Finset.range H)
    (fun t => B.biUnion fun y => taggedFiber M Y (t + 1) y)
  have hinner :
      ∀ t ∈ Finset.range H,
        (B.biUnion fun y => taggedFiber M Y (t + 1) y).card ≤
          ∑ y ∈ B, (taggedFiber M Y (t + 1) y).card := by
    intro t _ht
    exact card_biUnion_le_sum B fun y => taggedFiber M Y (t + 1) y
  have hcardNat :
      (transportedSources M Y H B).card ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (taggedFiber M Y (t + 1) y).card := by
    unfold transportedSources
    calc
      ((Finset.range H).biUnion fun t =>
          B.biUnion fun y => taggedFiber M Y (t + 1) y).card ≤
          ∑ t ∈ Finset.range H,
            (B.biUnion fun y => taggedFiber M Y (t + 1) y).card := houter
      _ ≤ ∑ t ∈ Finset.range H, ∑ y ∈ B,
          (taggedFiber M Y (t + 1) y).card := by
            apply Finset.sum_le_sum
            intro t ht
            exact hinner t ht
  have hcardQ :
      ((transportedSources M Y H B).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((taggedFiber M Y (t + 1) y).card : ℚ) := by
    exact_mod_cast hcardNat
  let K : ℚ := (5 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)
  calc
    ((transportedSources M Y H B).card : ℚ) ≤
        ∑ t ∈ Finset.range H, ∑ y ∈ B,
          ((taggedFiber M Y (t + 1) y).card : ℚ) := hcardQ
    _ ≤ ∑ _t ∈ Finset.range H, ∑ _y ∈ B, K := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro y _hy
      exact taggedFiber_bound_uniform hY (by omega)
        (by simpa using Finset.mem_range.mp ht) hHY hYM
    _ = (5 / 2 : ℚ) * (H : ℚ) ^ 2 * (2 : ℚ) ^ M /
        (Y : ℚ) * (B.card : ℚ) := by
      simp [K]
      ring


end FirstPassageLinearTransport
