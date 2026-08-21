/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import FirstPassageLinearTransport.Parity
import FirstPassageLinearTransport.Density

/-!
# Maximal parity barrier

This is the finite pruned-tree cosh-potential proof of the maximal Boolean
barrier estimate, together with the exact adapter from the V2 parity-vector
bijection to Boolean words.
It is source-adapted from the independent maximal-barrier component of CET;
no CET module is imported.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators

/-- A Boolean parity digit as a centered walk increment in `{-1,1}`. -/
def boolWalkStep (b : Bool) : ℤ :=
  if b then 1 else -1

@[simp] theorem boolWalkStep_false : boolWalkStep false = -1 := rfl
@[simp] theorem boolWalkStep_true : boolWalkStep true = 1 := rfl

/-- Whether a continuation hits the open absolute barrier `a`, including the
current position among the inspected vertices. -/
def hitsBarrierFrom (a : ℝ) :
    (r : ℕ) → ℤ → (Fin r → Bool) → Prop
  | 0, y, _ => a < |(y : ℝ)|
  | r + 1, y, v =>
      a < |(y : ℝ)| ∨
        hitsBarrierFrom a r (y + boolWalkStep (v 0))
          (fun i => v i.succ)

/-- Exact number of `r`-bit continuations that hit the barrier. -/
noncomputable def barrierHitCount (a : ℝ) (r : ℕ) (y : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (hitsBarrierFrom a r y)).card

theorem hitsBarrierFrom_of_bad {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : a < |(y : ℝ)|) (v : Fin r → Bool) :
    hitsBarrierFrom a r y v := by
  cases r <;> simp [hitsBarrierFrom, hy]

theorem barrierHitCount_of_bad {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : a < |(y : ℝ)|) :
    barrierHitCount a r y = 2 ^ r := by
  classical
  rw [barrierHitCount]
  have hfilter :
      Finset.univ.filter (hitsBarrierFrom a r y) = Finset.univ := by
    exact Finset.filter_eq_self.mpr (fun v _ => hitsBarrierFrom_of_bad hy v)
  rw [hfilter]
  simp

/-- On a safe current state, expose the first bit of a hitting word. -/
noncomputable def safeHitSuccEquiv {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : ¬a < |(y : ℝ)|) :
    {v : Fin (r + 1) → Bool // hitsBarrierFrom a (r + 1) y v} ≃
      Σ b : Bool,
        {w : Fin r → Bool //
          hitsBarrierFrom a r (y + boolWalkStep b) w} :=
  ((Fin.consEquiv (fun _ : Fin (r + 1) => Bool)).symm.subtypeEquiv (fun v => by
      change
        hitsBarrierFrom a (r + 1) y v ↔
          hitsBarrierFrom a r (y + boolWalkStep (v 0))
            (fun i => v i.succ)
      simp [hitsBarrierFrom, hy])).trans
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun b w => hitsBarrierFrom a r (y + boolWalkStep b) w))

theorem barrierHitCount_succ_of_safe {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : ¬a < |(y : ℝ)|) :
    barrierHitCount a (r + 1) y =
      barrierHitCount a r (y - 1) + barrierHitCount a r (y + 1) := by
  classical
  have hc :
      Fintype.card
          {v : Fin (r + 1) → Bool // hitsBarrierFrom a (r + 1) y v} =
        Fintype.card
          (Σ b : Bool,
            {w : Fin r → Bool //
              hitsBarrierFrom a r (y + boolWalkStep b) w}) :=
    Fintype.card_congr (safeHitSuccEquiv (r := r) hy)
  simpa [barrierHitCount, Fintype.card_subtype, Fintype.card_sigma,
    Fintype.sum_bool, sub_eq_add_neg, add_comm] using hc

theorem cosh_int_children (θ : ℝ) (y : ℤ) :
    Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) +
        Real.cosh (θ * ((y + 1 : ℤ) : ℝ)) =
      2 * Real.cosh (θ * (y : ℝ)) * Real.cosh θ := by
  rw [show θ * ((y - 1 : ℤ) : ℝ) = θ * (y : ℝ) - θ by push_cast; ring]
  rw [show θ * ((y + 1 : ℤ) : ℝ) = θ * (y : ℝ) + θ by push_cast; ring]
  rw [Real.cosh_sub, Real.cosh_add]
  ring

private theorem cosh_barrier_le_position {a θ : ℝ} {y : ℤ}
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hy : a < |(y : ℝ)|) :
    Real.cosh (θ * a) ≤ Real.cosh (θ * (y : ℝ)) := by
  rw [Real.cosh_le_cosh]
  rw [abs_mul, abs_mul, abs_of_nonneg hθ, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (le_of_lt hy) hθ

/-- Finite pruned-tree cosh potential. -/
theorem barrierHitCount_mul_cosh_le
    (a θ : ℝ) (r : ℕ) (y : ℤ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a r y : ℝ) * Real.cosh (θ * a) ≤
      (2 : ℝ) ^ r * Real.cosh (θ * (y : ℝ)) * Real.cosh θ ^ r := by
  induction r generalizing y with
  | zero =>
      by_cases hy : a < |(y : ℝ)|
      · rw [barrierHitCount_of_bad hy]
        simp only [pow_zero, Nat.cast_one, one_mul, mul_one]
        exact cosh_barrier_le_position ha hθ hy
      · simp [barrierHitCount, hitsBarrierFrom, hy, (Real.cosh_pos _).le]
  | succ r ihr =>
      by_cases hy : a < |(y : ℝ)|
      · rw [barrierHitCount_of_bad hy]
        have hcosh := cosh_barrier_le_position ha hθ hy
        have hpow : (1 : ℝ) ≤ Real.cosh θ ^ (r + 1) :=
          one_le_pow₀ (Real.one_le_cosh θ)
        have hcast : (((2 ^ (r + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (r + 1) := by
          norm_num
        calc
          ((2 ^ (r + 1) : ℕ) : ℝ) * Real.cosh (θ * a)
              ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) := by
                rw [hcast]
                exact mul_le_mul_of_nonneg_left hcosh (by positivity)
          _ ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) *
                Real.cosh θ ^ (r + 1) := by
              have hnonneg :
                  0 ≤ (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) := by
                positivity
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hpow hnonneg
      · rw [barrierHitCount_succ_of_safe hy]
        push_cast
        have hminus := ihr (y := y - 1)
        have hplus := ihr (y := y + 1)
        calc
          ((barrierHitCount a r (y - 1) : ℝ) +
                (barrierHitCount a r (y + 1) : ℝ)) * Real.cosh (θ * a) =
              (barrierHitCount a r (y - 1) : ℝ) * Real.cosh (θ * a) +
                (barrierHitCount a r (y + 1) : ℝ) * Real.cosh (θ * a) := by
                  ring
          _ ≤ (2 : ℝ) ^ r * Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) *
                  Real.cosh θ ^ r +
                (2 : ℝ) ^ r * Real.cosh (θ * ((y + 1 : ℤ) : ℝ)) *
                  Real.cosh θ ^ r := add_le_add hminus hplus
          _ = (2 : ℝ) ^ (r + 1) * Real.cosh (θ * (y : ℝ)) *
                Real.cosh θ ^ (r + 1) := by
              calc
                _ = (2 : ℝ) ^ r *
                      (Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) +
                        Real.cosh (θ * ((y + 1 : ℤ) : ℝ))) *
                      Real.cosh θ ^ r := by ring
                _ = (2 : ℝ) ^ r *
                      (2 * Real.cosh (θ * (y : ℝ)) * Real.cosh θ) *
                      Real.cosh θ ^ r := by rw [cosh_int_children]
                _ = _ := by rw [pow_succ, pow_succ]; ring

theorem barrierHitCount_le_chernoff
    (a θ : ℝ) (r : ℕ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a r 0 : ℝ) ≤
      (2 : ℝ) ^ (r + 1) *
        Real.exp (((r : ℝ) * θ ^ 2 / 2) - θ * a) := by
  have hpot := barrierHitCount_mul_cosh_le a θ r 0 ha hθ
  have hlower : Real.exp (θ * a) / 2 ≤ Real.cosh (θ * a) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(θ * a))]
  have hleft :
      (barrierHitCount a r 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (barrierHitCount a r 0 : ℝ) * Real.cosh (θ * a) :=
    mul_le_mul_of_nonneg_left hlower (by positivity)
  have hcoshpow :
      Real.cosh θ ^ r ≤ Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
    calc
      Real.cosh θ ^ r ≤ Real.exp (θ ^ 2 / 2) ^ r :=
        pow_le_pow_left₀ (Real.cosh_pos θ).le
          (Real.cosh_le_exp_half_sq θ) r
      _ = Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
        rw [← Real.exp_nat_mul]
  have hmain :
      (barrierHitCount a r 0 : ℝ) * (Real.exp (θ * a) / 2) ≤
        (2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)) := by
    calc
      _ ≤ (barrierHitCount a r 0 : ℝ) * Real.cosh (θ * a) := hleft
      _ ≤ (2 : ℝ) ^ r * Real.cosh (θ * (0 : ℝ)) * Real.cosh θ ^ r := by
        simpa only [Int.cast_zero] using hpot
      _ = (2 : ℝ) ^ r * Real.cosh θ ^ r := by norm_num
      _ ≤ (2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hcoshpow (by positivity)
  have hmul :
      (barrierHitCount a r 0 : ℝ) * Real.exp (θ * a) ≤
        2 * ((2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2))) := by
    nlinarith
  have hdiv :
      (barrierHitCount a r 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)))) /
          Real.exp (θ * a) :=
    (le_div_iff₀ (Real.exp_pos (θ * a))).2 (by simpa [mul_comm] using hmul)
  calc
    (barrierHitCount a r 0 : ℝ) ≤
        (2 * ((2 : ℝ) ^ r * Real.exp ((r : ℝ) * (θ ^ 2 / 2)))) /
          Real.exp (θ * a) := hdiv
    _ = (2 : ℝ) ^ (r + 1) *
          Real.exp (((r : ℝ) * θ ^ 2 / 2) - θ * a) := by
      rw [Real.exp_sub]
      ring

/-- Optimized two-sided maximal Boolean-walk estimate. -/
theorem barrierHitCount_le_exp
    (h : ℝ) (M : ℕ) (hh : 0 ≤ h) (hM : 0 < M) :
    (barrierHitCount (2 * h) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) * Real.exp (-(2 * h ^ 2 / (M : ℝ))) := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hchernoff :=
    barrierHitCount_le_chernoff (2 * h) (2 * h / (M : ℝ)) M
      (by positivity) (by positivity)
  convert hchernoff using 1
  all_goals field_simp
  all_goals ring

/-- Convert the V2 `Fin 2` parity word to the Boolean word used by the finite
barrier count. -/
def boolParityCode (M : ℕ) (n : Fin (2 ^ M)) : Fin M → Bool :=
  fun i => finTwoEquiv (parityCode M n i)

/-- Boolean form of the exact parity-vector bijection. -/
noncomputable def boolParityEquiv (M : ℕ) :
    Fin (2 ^ M) ≃ (Fin M → Bool) :=
  (parityEquiv M).trans (Equiv.piCongrRight fun _ => finTwoEquiv)

@[simp] theorem boolParityEquiv_apply (M : ℕ) (n : Fin (2 ^ M)) :
    boolParityEquiv M n = boolParityCode M n := rfl

/-- Bad residues in one complete parity block. -/
noncomputable def barrierResidues (M : ℕ) (h : ℝ) :
    Finset (Fin (2 ^ M)) := by
  classical
  exact Finset.univ.filter
    (fun x => hitsBarrierFrom (2 * h) M 0 (boolParityCode M x))

/-- The parity bijection restricted to the barrier-hitting residues. -/
noncomputable def barrierResidueEquiv (M : ℕ) (h : ℝ) :
    {x : Fin (2 ^ M) //
      hitsBarrierFrom (2 * h) M 0 (boolParityCode M x)} ≃
      {v : Fin M → Bool // hitsBarrierFrom (2 * h) M 0 v} :=
  (boolParityEquiv M).subtypeEquiv (fun x => by
    rw [boolParityEquiv_apply])

theorem card_barrierResidues (M : ℕ) (h : ℝ) :
    (barrierResidues M h).card = barrierHitCount (2 * h) M 0 := by
  classical
  have hc := Fintype.card_congr (barrierResidueEquiv M h)
  simpa [barrierResidues, barrierHitCount, Fintype.card_subtype] using hc

/-- The Boolean parity word of an arbitrary natural starting value. -/
def boolParityWord (M n : ℕ) : Fin M → Bool :=
  fun i => finTwoEquiv (parityBit n i)

theorem boolParityWord_congr {M n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ M]) :
    boolParityWord M n = boolParityWord M n' := by
  exact congrArg (fun f : Fin M → Fin 2 => fun i => finTwoEquiv (f i))
    (parityPrefix_congr h)

theorem boolParityWord_mod (M n : ℕ) :
    boolParityWord M (n % (2 ^ M)) = boolParityWord M n := by
  apply boolParityWord_congr
  show n % 2 ^ M % 2 ^ M = n % 2 ^ M
  exact Nat.mod_mod _ _

@[simp] theorem boolParityCode_eq_word (M : ℕ) (n : Fin (2 ^ M)) :
    boolParityCode M n = boolParityWord M n := rfl

/-- A predicate on one complete residue block has the same cardinality on
the corresponding dyadic shell. -/
theorem card_dyadicShell_filter_mod_mem
    (M : ℕ) (S : Finset (Fin (2 ^ M))) :
    ((dyadicShell M).filter
      (fun n =>
        (⟨n % (2 ^ M), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
          Fin (2 ^ M)) ∈ S)).card = S.card := by
  classical
  let q := 2 ^ M
  have hq : 0 < q := pow_pos (by omega) _
  apply Finset.card_bij
      (fun n hn =>
        (⟨n - q, by
          have hnShell := (Finset.mem_filter.mp hn).1
          have hnBounds := mem_dyadicShell.mp hnShell
          have hupper : n < q + q := by
            dsimp [q]
            simpa [pow_succ, Nat.mul_comm, Nat.two_mul] using hnBounds.2
          omega⟩ : Fin q))
  · intro n hn
    have hnS := (Finset.mem_filter.mp hn).2
    have hnShell := (Finset.mem_filter.mp hn).1
    have hnLower := (mem_dyadicShell.mp hnShell).1
    have hnEq : q + (n - q) = n := Nat.add_sub_of_le hnLower
    have hmod : n % q = n - q := by
      calc
        n % q = (q + (n - q)) % q := by rw [hnEq]
        _ = (n - q) % q := by simp [Nat.add_mod]
        _ = n - q := Nat.mod_eq_of_lt (by
          have hnBounds := mem_dyadicShell.mp hnShell
          have hupper : n < q + q := by
            dsimp [q]
            simpa [pow_succ, Nat.mul_comm, Nat.two_mul] using hnBounds.2
          omega)
    simpa [q, hmod] using hnS
  · intro n hn m hm hnm
    have hnLower := (mem_dyadicShell.mp (Finset.mem_filter.mp hn).1).1
    have hmLower := (mem_dyadicShell.mp (Finset.mem_filter.mp hm).1).1
    have hval : n - q = m - q := congrArg Fin.val hnm
    omega
  · intro x hx
    refine ⟨q + (x : ℕ), ?_, ?_⟩
    · simp only [Finset.mem_filter]
      constructor
      · rw [mem_dyadicShell]
        constructor
        · dsimp [q]
          omega
        · have hxlt := x.isLt
          dsimp [q] at hxlt ⊢
          rw [pow_succ]
          omega
      · have hmod : (q + (x : ℕ)) % q = (x : ℕ) := by
          simp [Nat.add_mod, Nat.mod_eq_of_lt x.isLt]
        simpa [q, hmod] using hx
    · apply Fin.ext
      simp

/-- Shell points whose actual shortcut parity word hits the barrier. -/
noncomputable def shellBarrierHit (M : ℕ) (h : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter
    (fun n => hitsBarrierFrom (2 * h) M 0 (boolParityWord M n))

theorem card_shellBarrierHit (M : ℕ) (h : ℝ) :
    (shellBarrierHit M h).card = barrierHitCount (2 * h) M 0 := by
  classical
  have heq :
      shellBarrierHit M h =
        (dyadicShell M).filter
          (fun n =>
            (⟨n % (2 ^ M), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
              Fin (2 ^ M)) ∈ barrierResidues M h) := by
    ext n
    simp only [shellBarrierHit, barrierResidues, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => by
      rw [boolParityCode_eq_word, boolParityWord_mod])
  rw [heq, card_dyadicShell_filter_mod_mem, card_barrierResidues]

theorem boolWalkStep_finTwo (b : Fin 2) :
    boolWalkStep (finTwoEquiv b) = 2 * (b : ℤ) - 1 := by
  fin_cases b <;> norm_num [boolWalkStep, finTwoEquiv]

theorem oddCount_succ_shift (H n : ℕ) :
    oddCount n (H + 1) =
      (parityBit n 0 : ℕ) + oddCount (shortcut n) H := by
  calc
    oddCount n (H + 1) =
        (parityBit n 0 : ℕ) +
          ∑ i ∈ Finset.range H, (parityBit n (i + 1) : ℕ) := by
      unfold oddCount
      rw [Finset.sum_range_succ']
      ac_rfl
    _ = (parityBit n 0 : ℕ) +
          ∑ i ∈ Finset.range H, (parityBit (shortcut n) i : ℕ) := by
      congr 1
    _ = (parityBit n 0 : ℕ) + oddCount (shortcut n) H := by
      rfl

theorem boolParityWord_tail (r n : ℕ) :
    (fun i : Fin r => boolParityWord (r + 1) n i.succ) =
      boolParityWord r (shortcut n) := by
  funext i
  unfold boolParityWord
  congr 1

/-- Avoiding the recursive barrier keeps every prefix position inside it. -/
theorem prefix_position_le_of_not_hitsBarrier :
    ∀ {r n : ℕ} {a : ℝ} {y : ℤ},
      ¬hitsBarrierFrom a r y (boolParityWord r n) →
      ∀ H : ℕ, H ≤ r →
        |(y : ℝ) + 2 * oddCount n H - H| ≤ a := by
  intro r
  induction r with
  | zero =>
      intro n a y hsafe H hHr
      have hy : ¬a < |(y : ℝ)| := by
        simpa [hitsBarrierFrom] using hsafe
      have hH : H = 0 := by omega
      subst H
      simpa using le_of_not_gt hy
  | succ r ihr =>
      intro n a y hsafe H hHr
      have hdecomp :
          ¬a < |(y : ℝ)| ∧
            ¬hitsBarrierFrom a r
              (y + boolWalkStep (boolParityWord (r + 1) n 0))
              (boolParityWord r (shortcut n)) := by
        have hraw :
            ¬a < |(y : ℝ)| ∧
              ¬hitsBarrierFrom a r
                (y + boolWalkStep (boolParityWord (r + 1) n 0))
                (fun i => boolParityWord (r + 1) n i.succ) := by
          simpa [hitsBarrierFrom] using hsafe
        simpa [boolParityWord_tail] using hraw
      rcases hdecomp with ⟨hy, htail⟩
      cases H with
      | zero => simpa using le_of_not_gt hy
      | succ H =>
          have hHr' : H ≤ r := by omega
          have hchild := ihr htail H hHr'
          rw [oddCount_succ_shift]
          have hstep := boolWalkStep_finTwo (parityBit n 0)
          change
            boolWalkStep (boolParityWord (r + 1) n 0) =
              2 * ((parityBit n 0 : ℕ) : ℤ) - 1 at hstep
          have hstepR :
              (boolWalkStep (boolParityWord (r + 1) n 0) : ℝ) =
                2 * ((parityBit n 0 : ℕ) : ℝ) - 1 := by
            exact_mod_cast hstep
          convert hchild using 1
          all_goals
            push_cast
            rw [hstepR]
            ring

/-- Two-sided parity regularity at every prefix through `M`. -/
def MaximalParityRegular (n M : ℕ) (h : ℝ) : Prop :=
  ∀ H : ℕ, H ≤ M →
    |(oddCount n H : ℝ) - (H : ℝ) / 2| ≤ h

theorem maximalParityRegular_of_not_hitsBarrier {M n : ℕ} {h : ℝ}
    (hgood : ¬hitsBarrierFrom (2 * h) M 0 (boolParityWord M n)) :
    MaximalParityRegular n M h := by
  intro H hHM
  have hp := prefix_position_le_of_not_hitsBarrier hgood H hHM
  have habs :
      |(2 : ℝ) * ((oddCount n H : ℝ) - (H : ℝ) / 2)| ≤ 2 * h := by
    convert hp using 1
    all_goals ring
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habs
  nlinarith

/-- Shell members that fail two-sided parity regularity. -/
noncomputable def shellMaximalParityBad (M : ℕ) (h : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n => ¬MaximalParityRegular n M h)

theorem shellMaximalParityBad_subset_hit (M : ℕ) (h : ℝ) :
    shellMaximalParityBad M h ⊆ shellBarrierHit M h := by
  classical
  intro n hn
  rw [shellMaximalParityBad, Finset.mem_filter] at hn
  rw [shellBarrierHit, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  by_contra hnot
  exact hn.2 (maximalParityRegular_of_not_hitsBarrier hnot)

/-- The shellwise maximal-parity exceptional set obeys the optimized
two-sided Boolean-barrier estimate. -/
theorem card_shellMaximalParityBad_le {M : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hM : 0 < M) :
    ((shellMaximalParityBad M h).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-(2 * h ^ 2 / (M : ℝ))) := by
  have hcard :
      (shellMaximalParityBad M h).card ≤ (shellBarrierHit M h).card :=
    Finset.card_le_card (shellMaximalParityBad_subset_hit M h)
  have hcardR :
      ((shellMaximalParityBad M h).card : ℝ) ≤
        ((shellBarrierHit M h).card : ℝ) := by exact_mod_cast hcard
  rw [card_shellBarrierHit] at hcardR
  exact hcardR.trans (barrierHitCount_le_exp h M hh hM)

end FirstPassageLinearTransport
