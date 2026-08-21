/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.Parity

/-!
# First-passage reversal

This module begins the independent formalization of Section 4.  It first
records the exact stopped-path algebra; estimates and fiber counting are added
only after these identities compile.
-/

namespace FirstPassageLinearTransport

/-- `h` is the first time that the orbit of `n` reaches `[0,Y]`. -/
def IsFirstPassage (Y n h : ℕ) : Prop :=
  orbit h n ≤ Y ∧ ∀ j : ℕ, j < h → Y < orbit j n



/-- The final crossing cannot be an odd shortcut step. -/
theorem firstPassage_final_even {Y n k : ℕ}
    (hfp : IsFirstPassage Y n (k + 1)) :
    orbit k n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
  · exact heven
  · have hprev : Y < orbit k n := hfp.2 k (by omega)
    have hland : orbit (k + 1) n ≤ Y := hfp.1
    have hstep := two_mul_shortcut_of_odd hodd
    rw [← orbit_succ] at hstep
    omega

/-- The first-passage landing band in the division-free integer form
`Y < 2y` and `y ≤ Y`. -/
theorem firstPassage_band {Y n h : ℕ} (hh : 0 < h)
    (hfp : IsFirstPassage Y n h) :
    Y < 2 * orbit h n ∧ orbit h n ≤ Y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have heven := firstPassage_final_even hfp
  have hstep : 2 * orbit (k + 1) n = orbit k n := by
    simpa [orbit_succ] using two_mul_shortcut_of_even heven
  constructor
  · have hprev : Y < orbit k n := hfp.2 k (by omega)
    have hband : Y < 2 * orbit (k + 1) n := by omega
    simpa [Nat.succ_eq_add_one] using hband
  · simpa [Nat.succ_eq_add_one] using hfp.1

/-- The correction factor attached to reversing one odd shortcut step. -/
def reverseOddFactor (x : ℕ) : ℚ :=
  1 - 1 / (2 * (x : ℚ))

/-- The factor attached to the state at time `i`; even states contribute one. -/
def reverseStepFactor (n i : ℕ) : ℚ :=
  if (parityBit n i : ℕ) = 1 then reverseOddFactor (orbit (i + 1) n) else 1

/-- Product of all reverse factors through time `h`. -/
def reverseProduct (n h : ℕ) : ℚ :=
  ∏ i ∈ Finset.range h, reverseStepFactor n i

theorem reverseProduct_succ (n h : ℕ) :
    reverseProduct n (h + 1) =
      reverseProduct n h * reverseStepFactor n h := by
  simp [reverseProduct, Finset.prod_range_succ]

/-- Exact one-step reverse identity, cleared only of the power of three. -/
theorem reverse_step_scaled {n : ℕ} (hn : 0 < n) :
    (3 : ℚ) ^ (n % 2) * (n : ℚ) =
      2 * (shortcut n : ℚ) *
        (if n % 2 = 1 then reverseOddFactor (shortcut n) else 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hstep := two_mul_shortcut_of_even heven
    simp [heven]
    exact_mod_cast hstep.symm
  · have hstep := two_mul_shortcut_of_odd hodd
    have hspos : (shortcut n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (shortcut_pos hn))
    simp only [hodd, pow_one, if_pos, reverseOddFactor]
    have hstepQ :
        (2 : ℚ) * (shortcut n : ℚ) = (3 : ℚ) * (n : ℚ) + 1 := by
      exact_mod_cast hstep
    calc
      (3 : ℚ) * (n : ℚ) = 2 * (shortcut n : ℚ) - 1 := by linarith
      _ = 2 * (shortcut n : ℚ) *
          (1 - 1 / (2 * (shortcut n : ℚ))) := by
            field_simp [hspos]

/-- Exact reverse-product identity with the power of three cleared. -/
theorem reverse_product_scaled {n : ℕ} (hn : 0 < n) (h : ℕ) :
    (3 : ℚ) ^ (oddCount n h) * (n : ℚ) =
      (2 : ℚ) ^ h * (orbit h n : ℚ) * reverseProduct n h := by
  induction h with
  | zero => simp [reverseProduct]
  | succ h ih =>
      have hlocal :
          (3 : ℚ) ^ (parityBit n h : ℕ) * (orbit h n : ℚ) =
            2 * (orbit (h + 1) n : ℚ) * reverseStepFactor n h := by
        simpa [reverseStepFactor, parityBit, orbit_succ] using
          reverse_step_scaled (orbit_pos hn h)
      rw [oddCount_succ, reverseProduct_succ]
      calc
        (3 : ℚ) ^ (oddCount n h + (parityBit n h : ℕ)) * (n : ℚ) =
            (3 : ℚ) ^ (parityBit n h : ℕ) *
              ((3 : ℚ) ^ (oddCount n h) * (n : ℚ)) := by
                rw [pow_add]
                ring
        _ = (3 : ℚ) ^ (parityBit n h : ℕ) *
              ((2 : ℚ) ^ h * (orbit h n : ℚ) * reverseProduct n h) := by
                rw [ih]
        _ = (2 : ℚ) ^ h *
              ((3 : ℚ) ^ (parityBit n h : ℕ) * (orbit h n : ℚ)) *
                reverseProduct n h := by ring
        _ = (2 : ℚ) ^ h *
              (2 * (orbit (h + 1) n : ℚ) * reverseStepFactor n h) *
                reverseProduct n h := by rw [hlocal]
        _ = (2 : ℚ) ^ (h + 1) * (orbit (h + 1) n : ℚ) *
              (reverseProduct n h * reverseStepFactor n h) := by
                rw [pow_succ]
                ring

/-- Exact reverse product in the manuscript normalization. -/
theorem reverse_product_identity {n : ℕ} (hn : 0 < n) (h : ℕ) :
    (n : ℚ) =
      ((2 : ℚ) ^ h * (orbit h n : ℚ) /
        (3 : ℚ) ^ (oddCount n h)) * reverseProduct n h := by
  have hthree : (3 : ℚ) ^ (oddCount n h) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hthree).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using reverse_product_scaled hn h

/-- The loss variable in one reverse step. -/
def reverseLoss (n i : ℕ) : ℚ :=
  if (parityBit n i : ℕ) = 1 then
    1 / (2 * (orbit (i + 1) n : ℚ))
  else 0

theorem reverseStepFactor_eq_one_sub_reverseLoss (n i : ℕ) :
    reverseStepFactor n i = 1 - reverseLoss n i := by
  by_cases hodd : (parityBit n i : ℕ) = 1
  · simp [reverseStepFactor, reverseOddFactor, reverseLoss, hodd]
  · simp [reverseStepFactor, reverseOddFactor, reverseLoss, hodd]

theorem reverseProduct_eq_prod_loss (n h : ℕ) :
    reverseProduct n h =
      ∏ i ∈ Finset.range h, (1 - reverseLoss n i) := by
  simp [reverseProduct, reverseStepFactor_eq_one_sub_reverseLoss]

theorem shortcut_gt_of_odd {x : ℕ} (hodd : x % 2 = 1) : x < shortcut x := by
  have hstep := two_mul_shortcut_of_odd hodd
  omega

theorem firstPassage_odd_following_gt {Y n h i : ℕ}
    (hfp : IsFirstPassage Y n h) (hi : i < h)
    (hodd : (parityBit n i : ℕ) = 1) :
    Y < orbit (i + 1) n := by
  have hprev : Y < orbit i n := hfp.2 i hi
  have hparity : orbit i n % 2 = 1 := hodd
  have hinc := shortcut_gt_of_odd hparity
  simpa [orbit_succ] using hprev.trans hinc

theorem reverseLoss_nonneg (n i : ℕ) : 0 ≤ reverseLoss n i := by
  by_cases hodd : (parityBit n i : ℕ) = 1
  · simp [reverseLoss, hodd]
  · simp [reverseLoss, hodd]

theorem reverseLoss_le_one {n : ℕ} (hn : 0 < n) (i : ℕ) :
    reverseLoss n i ≤ 1 := by
  by_cases hodd : (parityBit n i : ℕ) = 1
  · simp only [reverseLoss, hodd, if_pos]
    have hxpos : 0 < orbit (i + 1) n := orbit_pos hn (i + 1)
    have hden : (1 : ℚ) ≤ 2 * (orbit (i + 1) n : ℚ) := by
      exact_mod_cast (show 1 ≤ 2 * orbit (i + 1) n by omega)
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hden
  · simp [reverseLoss, hodd]

theorem reverseLoss_le_firstPassage {Y n h i : ℕ}
    (hY : 0 < Y) (hfp : IsFirstPassage Y n h) (hi : i < h) :
    reverseLoss n i ≤ 1 / (2 * (Y : ℚ)) := by
  by_cases hodd : (parityBit n i : ℕ) = 1
  · simp only [reverseLoss, hodd, if_pos]
    have hnext := firstPassage_odd_following_gt hfp hi hodd
    have hdenpos : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
    have hdenle :
        (2 : ℚ) * (Y : ℚ) ≤ 2 * (orbit (i + 1) n : ℚ) := by
      exact_mod_cast (show 2 * Y ≤ 2 * orbit (i + 1) n by omega)
    exact one_div_le_one_div_of_le hdenpos hdenle
  · simp [reverseLoss, hodd]

/-- Elementary finite-product form of `prod (1-u_i) ≥ 1-sum u_i`. -/
theorem one_sub_sum_le_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hua := hu a (by simp)
      have hus : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1 := by
        intro i hi
        exact hu i (by simp [hi])
      have hsum : 0 ≤ ∑ i ∈ s, u i :=
        Finset.sum_nonneg fun i hi => (hus i hi).1
      have hfactor : 0 ≤ 1 - u a := sub_nonneg.mpr hua.2
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      calc
        1 - (u a + ∑ i ∈ s, u i) ≤
            (1 - u a) * (1 - ∑ i ∈ s, u i) := by
              nlinarith [hua.1]
        _ ≤ (1 - u a) * ∏ i ∈ s, (1 - u i) :=
          mul_le_mul_of_nonneg_left (ih hus) hfactor

theorem reverseProduct_bounds {Y n h : ℕ}
    (hn : 0 < n) (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    1 - (h : ℚ) / (2 * (Y : ℚ)) ≤ reverseProduct n h ∧
      reverseProduct n h ≤ 1 := by
  have hloss :
      ∀ i ∈ Finset.range h, 0 ≤ reverseLoss n i ∧ reverseLoss n i ≤ 1 := by
    intro i hi
    exact ⟨reverseLoss_nonneg n i, reverseLoss_le_one hn i⟩
  have hsum :
      ∑ i ∈ Finset.range h, reverseLoss n i ≤
        (h : ℚ) / (2 * (Y : ℚ)) := by
    calc
      ∑ i ∈ Finset.range h, reverseLoss n i ≤
          ∑ _i ∈ Finset.range h, (1 / (2 * (Y : ℚ)) : ℚ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact reverseLoss_le_firstPassage hY hfp (Finset.mem_range.mp hi)
      _ = (h : ℚ) / (2 * (Y : ℚ)) := by
        simp
        ring
  rw [reverseProduct_eq_prod_loss]
  constructor
  · calc
      1 - (h : ℚ) / (2 * (Y : ℚ)) ≤
          1 - ∑ i ∈ Finset.range h, reverseLoss n i := by linarith
      _ ≤ ∏ i ∈ Finset.range h, (1 - reverseLoss n i) :=
        one_sub_sum_le_prod _ _ hloss
  · apply Finset.prod_le_one
    · intro i hi
      exact sub_nonneg.mpr (hloss i hi).2
    · intro i hi
      linarith [(hloss i hi).1]

/-- The uncorrected reverse scale `2^h y / 3^s`. -/
def reverseScale (n h : ℕ) : ℚ :=
  (2 : ℚ) ^ h * (orbit h n : ℚ) / (3 : ℚ) ^ (oddCount n h)

theorem reverseScale_nonneg (n h : ℕ) : 0 ≤ reverseScale n h := by
  unfold reverseScale
  positivity

/-- First-passage reverse bounds in exact rational arithmetic. -/
theorem firstPassage_reverse_bounds {Y n h : ℕ}
    (hn : 0 < n) (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    (1 - (h : ℚ) / (2 * (Y : ℚ))) * reverseScale n h ≤ (n : ℚ) ∧
      (n : ℚ) ≤ reverseScale n h := by
  have hp := reverseProduct_bounds hn hY hfp
  have hA := reverseScale_nonneg n h
  have hid : (n : ℚ) = reverseScale n h * reverseProduct n h := by
    simpa [reverseScale] using reverse_product_identity hn h
  rw [hid]
  constructor
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left hp.1 hA
  · simpa using mul_le_mul_of_nonneg_left hp.2 hA

theorem reverseScale_three_le_of_same_landing {n₁ n₂ h y : ℕ}
    (hy₁ : orbit h n₁ = y) (hy₂ : orbit h n₂ = y)
    (hs : oddCount n₁ h < oddCount n₂ h) :
    3 * reverseScale n₂ h ≤ reverseScale n₁ h := by
  let N : ℚ := (2 : ℚ) ^ h * (y : ℚ)
  let d₁ : ℚ := (3 : ℚ) ^ (oddCount n₁ h)
  let d₂ : ℚ := (3 : ℚ) ^ (oddCount n₂ h)
  have hd₁ : 0 < d₁ := by
    dsimp [d₁]
    positivity
  have hd₂ : 0 < d₂ := by
    dsimp [d₂]
    positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hpow : 3 * d₁ ≤ d₂ := by
    dsimp [d₁, d₂]
    have hp :
        (3 : ℚ) ^ (oddCount n₁ h + 1) ≤
          (3 : ℚ) ^ (oddCount n₂ h) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simpa [pow_succ, mul_comm] using hp
  have hcross : 3 * N * d₁ ≤ N * d₂ := by
    have := mul_le_mul_of_nonneg_left hpow hN
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  simp only [reverseScale, hy₁, hy₂]
  change 3 * (N / d₂) ≤ N / d₁
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ hd₂ hd₁).2 hcross

/-- A nonempty tagged fiber in one half-open dyadic shell has one
odd count. -/
theorem oddCount_rigidity {M Y h y n₁ n₂ : ℕ}
    (hn₁ : n₁ ∈ dyadicShell M) (hn₂ : n₂ ∈ dyadicShell M)
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hfp₁ : IsFirstPassage Y n₁ h) (hy₁ : orbit h n₁ = y)
    (hfp₂ : IsFirstPassage Y n₂ h) (hy₂ : orbit h n₂ = y) :
    oddCount n₁ h = oddCount n₂ h := by
  have hn₁pos : 0 < n₁ := by
    have := (mem_dyadicShell.mp hn₁).1
    have hpowpos : 0 < 2 ^ M := pow_pos (by omega) M
    omega
  have hn₂pos : 0 < n₂ := by
    have := (mem_dyadicShell.mp hn₂).1
    have hpowpos : 0 < 2 ^ M := pow_pos (by omega) M
    omega
  have hb₁ := firstPassage_reverse_bounds hn₁pos hY hfp₁
  have hb₂ := firstPassage_reverse_bounds hn₂pos hY hfp₂
  have hA₁ := reverseScale_nonneg n₁ h
  have hA₂ := reverseScale_nonneg n₂ h
  rcases lt_trichotomy (oddCount n₁ h) (oddCount n₂ h) with hs | hs | hs
  · have hscale := reverseScale_three_le_of_same_landing hy₁ hy₂ hs
    have htwiceQ : (2 : ℚ) * (n₂ : ℚ) ≤ (n₁ : ℚ) := by
      nlinarith
    have htwice : 2 * n₂ ≤ n₁ := by exact_mod_cast htwiceQ
    have hn₁lt : n₁ < 2 ^ (M + 1) := (mem_dyadicShell.mp hn₁).2
    have hn₂lo : 2 ^ M ≤ n₂ := (mem_dyadicShell.mp hn₂).1
    rw [pow_succ] at hn₁lt
    omega
  · exact hs
  · have hscale := reverseScale_three_le_of_same_landing hy₂ hy₁ hs
    have htwiceQ : (2 : ℚ) * (n₁ : ℚ) ≤ (n₂ : ℚ) := by
      nlinarith
    have htwice : 2 * n₁ ≤ n₂ := by exact_mod_cast htwiceQ
    have hn₂lt : n₂ < 2 ^ (M + 1) := (mem_dyadicShell.mp hn₂).2
    have hn₁lo : 2 ^ M ≤ n₁ := (mem_dyadicShell.mp hn₁).1
    rw [pow_succ] at hn₂lt
    omega

/-- Sources in one dyadic shell with one first-passage time and landing. -/
noncomputable def taggedFiber (M Y h y : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n => IsFirstPassage Y n h ∧ orbit h n = y

@[simp] theorem mem_taggedFiber {M Y h y n : ℕ} :
    n ∈ taggedFiber M Y h y ↔
      n ∈ dyadicShell M ∧ IsFirstPassage Y n h ∧ orbit h n = y := by
  classical
  simp [taggedFiber, and_assoc]

theorem finset_card_le_one_add_span (s : Finset ℕ) (hs : s.Nonempty) :
    (s.card : ℚ) ≤
      1 + (s.max' hs : ℚ) - (s.min' hs : ℚ) := by
  let a := s.min' hs
  let b := s.max' hs
  have hab : a ≤ b := by
    rcases hs with ⟨x, hx⟩
    exact (s.min'_le x hx).trans (s.le_max' x hx)
  have hsub : s ⊆ Finset.Icc a b := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hcardNat : s.card ≤ b + 1 - a := by
    have := Finset.card_le_card hsub
    simpa using this
  have hcast : (s.card : ℚ) ≤ ((b + 1 - a : ℕ) : ℚ) := by
    exact_mod_cast hcardNat
  have hsubcast : ((b + 1 - a : ℕ) : ℚ) = (b : ℚ) + 1 - (a : ℚ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    norm_num
  change (s.card : ℚ) ≤ 1 + (b : ℚ) - (a : ℚ)
  linarith

theorem taggedFiber_algebra {M Y h : ℕ}
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3) :
    ((h : ℚ) / (2 * (Y : ℚ))) *
          ((2 : ℚ) ^ (M + 1) /
            (1 - (h : ℚ) / (2 * (Y : ℚ)))) =
      2 * (h : ℚ) * (2 : ℚ) ^ M /
        (2 * (Y : ℚ) - (h : ℚ)) := by
  have hYQ : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
  have hden : (0 : ℚ) < 2 * (Y : ℚ) - (h : ℚ) := by
    have hscaled := (div_le_iff₀ hYQ).mp hsmall
    have : (h : ℚ) ≤ (2 * (Y : ℚ)) / 3 := by
      nlinarith
    nlinarith
  field_simp
  rw [pow_succ]
  ring

/-- The tagged-fiber estimate as a rational cardinality bound. -/
theorem taggedFiber_bound {M Y h y : ℕ}
    (hY : 0 < Y)
    (hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3) :
    ((taggedFiber M Y h y).card : ℚ) ≤
      1 + 2 * (h : ℚ) * (2 : ℚ) ^ M /
        (2 * (Y : ℚ) - (h : ℚ)) := by
  classical
  by_cases hf : (taggedFiber M Y h y).Nonempty
  · rcases hf with ⟨n₀, hn₀⟩
    let A : ℚ := reverseScale n₀ h
    let ε : ℚ := (h : ℚ) / (2 * (Y : ℚ))
    have htag₀ := mem_taggedFiber.mp hn₀
    have hn₀pos : 0 < n₀ := by
      have hlo := (mem_dyadicShell.mp htag₀.1).1
      have hp : 0 < 2 ^ M := pow_pos (by omega) M
      omega
    have hb₀ := firstPassage_reverse_bounds hn₀pos hY htag₀.2.1
    have hεnonneg : 0 ≤ ε := by
      dsimp [ε]
      positivity
    have hεle : ε ≤ 1 / 3 := hsmall
    have hfactor : 0 < 1 - ε := by linarith
    have hAupper : A < (2 : ℚ) ^ (M + 1) / (1 - ε) := by
      have hn₀ltNat := (mem_dyadicShell.mp htag₀.1).2
      have hn₀lt : (n₀ : ℚ) < (2 : ℚ) ^ (M + 1) := by
        exact_mod_cast hn₀ltNat
      apply (lt_div_iff₀ hfactor).2
      dsimp [A, ε] at hb₀ ⊢
      nlinarith
    have hsameScale :
        ∀ n ∈ taggedFiber M Y h y, reverseScale n h = A := by
      intro n hn
      have htag := mem_taggedFiber.mp hn
      have hs := oddCount_rigidity htag₀.1 htag.1 hY hsmall
        htag₀.2.1 htag₀.2.2 htag.2.1 htag.2.2
      simp only [reverseScale, htag₀.2.2, htag.2.2, hs, A]
    have hbounds :
        ∀ n ∈ taggedFiber M Y h y,
          (1 - ε) * A ≤ (n : ℚ) ∧ (n : ℚ) ≤ A := by
      intro n hn
      have htag := mem_taggedFiber.mp hn
      have hnpos : 0 < n := by
        have hlo := (mem_dyadicShell.mp htag.1).1
        have hp : 0 < 2 ^ M := pow_pos (by omega) M
        omega
      have hb := firstPassage_reverse_bounds hnpos hY htag.2.1
      rw [hsameScale n hn] at hb
      simpa [ε] using hb
    have hmaxmem : (taggedFiber M Y h y).max' ⟨n₀, hn₀⟩ ∈
        taggedFiber M Y h y := Finset.max'_mem _ _
    have hminmem : (taggedFiber M Y h y).min' ⟨n₀, hn₀⟩ ∈
        taggedFiber M Y h y := Finset.min'_mem _ _
    have hspan := finset_card_le_one_add_span
      (taggedFiber M Y h y) ⟨n₀, hn₀⟩
    have hcardA : ((taggedFiber M Y h y).card : ℚ) ≤ 1 + ε * A := by
      have hmax := (hbounds _ hmaxmem).2
      have hmin := (hbounds _ hminmem).1
      nlinarith
    have hmul : ε * A ≤ ε *
        ((2 : ℚ) ^ (M + 1) / (1 - ε)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hAupper) hεnonneg
    calc
      ((taggedFiber M Y h y).card : ℚ) ≤ 1 + ε * A := hcardA
      _ ≤ 1 + ε * ((2 : ℚ) ^ (M + 1) / (1 - ε)) := by linarith
      _ = 1 + 2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) := by
            rw [taggedFiber_algebra hY hsmall]
  · have hempty : taggedFiber M Y h y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    rw [hempty]
    simp
    have hden : (0 : ℚ) < 2 * (Y : ℚ) - (h : ℚ) := by
      have hYQ : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
      have hscaled := (div_le_iff₀ hYQ).mp hsmall
      have : (h : ℚ) ≤ (2 * (Y : ℚ)) / 3 := by
        nlinarith
      nlinarith
    positivity

end FirstPassageLinearTransport
