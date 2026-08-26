/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.BarrierDensity
import FirstPassageLinearTransport.Transport

/-!
# Closed stopped map and first-passage pullback

This module formalizes the exact stopped-map algebra of Section 5 before any
density estimate is applied.  A `StageSetup` records the eventual scalar
shell inequalities; the parameter-choice module will construct it.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- Shell-scaled first-passage target `2^floor(rM)`. -/
noncomputable def targetScale (r : ℝ) (M : ℕ) : ℕ :=
  2 ^ ⌊r * M⌋₊

/-- The exact scalar interface required by one stopped-map stage. -/
structure StageSetup (r eta : ℝ) where
  M0 : ℕ
  r_pos : 0 < r
  r_lt_one : r < 1
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  target_one_lt : ∀ M, M0 ≤ M → 1 < targetScale r M
  target_lt_shell : ∀ M, M0 ≤ M → targetScale r M < 2 ^ M
  horizon_small : ∀ M, M0 ≤ M →
    (M : ℚ) / (2 * (targetScale r M : ℚ)) ≤ 1 / 3
  terminal_budget : ∀ M, M0 ≤ M →
    centralOrbitScale M * ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) ≤
      targetScale r M

/-- Least passage time at most `H`, totalized as zero if no such time
exists. -/
noncomputable def boundedFirstPassage (Y H n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y then Nat.find h else 0

theorem boundedFirstPassage_eq_find {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    boundedFirstPassage Y H n = Nat.find h := by
  classical
  unfold boundedFirstPassage
  rw [dif_pos h]

theorem boundedFirstPassage_le {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    boundedFirstPassage Y H n ≤ H := by
  rw [boundedFirstPassage_eq_find h]
  exact (Nat.find_spec h).1

theorem boundedFirstPassage_spec {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    orbit (boundedFirstPassage Y H n) n ≤ Y := by
  rw [boundedFirstPassage_eq_find h]
  exact (Nat.find_spec h).2

theorem boundedFirstPassage_isFirstPassage {Y H n : ℕ}
    (h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y) :
    IsFirstPassage Y n (boundedFirstPassage Y H n) := by
  refine ⟨boundedFirstPassage_spec h, ?_⟩
  intro j hj
  by_contra hnot
  have hjle : orbit j n ≤ Y := by omega
  have htime := boundedFirstPassage_le h
  have hmin : boundedFirstPassage Y H n ≤ j := by
    rw [boundedFirstPassage_eq_find h]
    exact Nat.find_min' h ⟨by omega, hjle⟩
  omega

/-- Startup-totalized block length. -/
noncomputable def stageLength {r eta : ℝ} (p : StageSetup r eta)
    (n : ℕ) : ℕ :=
  if p.M0 ≤ Nat.log 2 n then
    boundedFirstPassage (targetScale r (Nat.log 2 n)) (Nat.log 2 n) n
  else 0

/-- Total stopped map; every branch is an actual shortcut iterate. -/
noncomputable def stageMap {r eta : ℝ} (p : StageSetup r eta)
    (n : ℕ) : ℕ :=
  orbit (stageLength p n) n

theorem stageMap_is_actual {r eta : ℝ} (p : StageSetup r eta) (n : ℕ) :
    stageMap p n = orbit (stageLength p n) n := rfl

/-- Finite startup enlargement of the maximal-barrier set. -/
def extendedWindow {r eta : ℝ} (p : StageSetup r eta) : Set ℕ :=
  initialWindowGood eta ∪ {n | n < 2 ^ p.M0}

/-- Pullback of a target set through the total stopped map. -/
def firstPassagePullback {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) : Set ℕ :=
  extendedWindow p ∩ stageMap p ⁻¹' S

theorem initialWindowGood_subset_extendedWindow {r eta : ℝ}
    (p : StageSetup r eta) :
    initialWindowGood eta ⊆ extendedWindow p :=
  Set.subset_union_left

/-- Adding the finite startup window preserves the quantitative density of
the initial barrier-good set. -/
theorem extendedWindow_powerDense {r eta : ℝ}
    (p : StageSetup r eta) :
    PowerDense (extendedWindow p)
      (quadraticWindowGlobalConstant eta)
      (quadraticWindowDensityRate eta) :=
  (initialWindowGood_powerDense p.eta_pos p.eta_le_one).mono_set
    (initialWindowGood_subset_extendedWindow p)

theorem mem_initialWindowGood_of_mem_extended_of_large
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : n ∈ extendedWindow p) (hlarge : p.M0 ≤ Nat.log 2 n) :
    n ∈ initialWindowGood eta := by
  rcases hn with hn | hn
  · exact hn
  · have hnlt : n < 2 ^ p.M0 := hn
    have hpow : 2 ^ p.M0 ≤ 2 ^ Nat.log 2 n :=
      Nat.pow_le_pow_right (by norm_num) hlarge
    have hnpos : 0 < n := by
      by_contra hzero
      have : n = 0 := Nat.eq_zero_of_not_pos hzero
      subst n
      have hlarge0 : p.M0 ≤ 0 := by simpa using hlarge
      have hbad := p.target_one_lt 0 hlarge0
      norm_num [targetScale] at hbad
    have hlogle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
    omega

theorem terminal_witness {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    orbit M n ≤ targetScale r M := by
  have hlog := log_two_eq_of_mem_dyadicShell hnShell
  have henv := hnGood M (by simp [hlog])
  have hnUpperNat : n < 2 ^ (M + 1) := (mem_dyadicShell.mp hnShell).2
  have hnUpper : (n : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast hnUpperNat.le
  have hpow :
      (n : ℝ) ^ (1 + eta) ≤ ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) :=
    Real.rpow_le_rpow (by positivity) hnUpper (by linarith [p.eta_pos])
  have hscale : 0 ≤ centralOrbitScale M := (centralOrbitScale_pos M).le
  have hreal :
      (orbit M n : ℝ) ≤ targetScale r M :=
    henv.2.trans ((mul_le_mul_of_nonneg_left hpow hscale).trans
      (p.terminal_budget M hM))
  exact_mod_cast hreal

theorem bounded_passage_exists {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    ∃ k : ℕ, k ≤ M ∧ orbit k n ≤ targetScale r M :=
  ⟨M, le_rfl, terminal_witness p hM hnShell hnGood⟩

theorem stageLength_eq_bounded {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M) :
    stageLength p n = boundedFirstPassage (targetScale r M) M n := by
  have hlog := log_two_eq_of_mem_dyadicShell hnShell
  simp [stageLength, hlog, hM]

theorem stageLength_le_shell {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    stageLength p n ≤ M := by
  rw [stageLength_eq_bounded p hM hnShell]
  exact boundedFirstPassage_le (bounded_passage_exists p hM hnShell hnGood)

theorem stageLength_isFirstPassage {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    IsFirstPassage (targetScale r M) n (stageLength p n) := by
  rw [stageLength_eq_bounded p hM hnShell]
  exact boundedFirstPassage_isFirstPassage
    (bounded_passage_exists p hM hnShell hnGood)

theorem stageLength_pos {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    1 ≤ stageLength p n := by
  have hfp := stageLength_isFirstPassage p hM hnShell hnGood
  by_contra hzero
  have hz : stageLength p n = 0 := by omega
  rw [hz] at hfp
  have hnLower : targetScale r M < n :=
    (p.target_lt_shell M hM).trans_le (mem_dyadicShell.mp hnShell).1
  simpa [IsFirstPassage] using (not_le_of_gt hnLower hfp.1)

/-- Bad target cells below the shell target. -/
noncomputable def badTarget (S : Set ℕ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Y).filter (fun y => y ∉ S)

theorem card_badTarget (S : Set ℕ) (Y : ℕ) :
    (badTarget S Y).card = badCount S Y := by
  rfl

/-- Exact shell decomposition: a failed pullback source is either outside
the retained window or belongs to the already-formalized first-passage
transport set for the bad target cells. -/
theorem shellBad_pullback_subset {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) {M : ℕ} (hM : p.M0 ≤ M) :
    shellBad (firstPassagePullback p S) M ⊆
      shellBad (extendedWindow p) M ∪
        transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M)) := by
  classical
  intro n hn
  rw [shellBad, Finset.mem_filter] at hn
  by_cases hnW : n ∈ extendedWindow p
  · apply Finset.mem_union_right
    have hnGood := mem_initialWindowGood_of_mem_extended_of_large p hnW (by
      simpa [log_two_eq_of_mem_dyadicShell hn.1] using hM)
    have hfp := stageLength_isFirstPassage p hM hn.1 hnGood
    have hpos := stageLength_pos p hM hn.1 hnGood
    have hle := stageLength_le_shell p hM hn.1 hnGood
    apply mem_transportedSources.mpr
    refine ⟨hn.1, stageLength p n, hpos, hle, hfp, ?_⟩
    have hnPull : n ∉ firstPassagePullback p S := hn.2
    have hnotS : stageMap p n ∉ S := by
      intro hs
      exact hnPull ⟨hnW, hs⟩
    have hlandingPos : 1 ≤ stageMap p n :=
      orbit_pos (by
        have hp : 0 < 2 ^ M := by positivity
        exact lt_of_lt_of_le hp (mem_dyadicShell.mp hn.1).1) _
    have hlandingLe : stageMap p n ≤ targetScale r M := hfp.1
    simpa [badTarget, stageMap] using
      (show stageMap p n ∈ badTarget S (targetScale r M) by
        simp [badTarget, hlandingPos, hlandingLe, hnotS])
  · apply Finset.mem_union_left
    simp [shellBad, hn.1, hnW]

theorem card_shellBad_pullback_le {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) {M : ℕ} (hM : p.M0 ≤ M) :
    (shellBad (firstPassagePullback p S) M).card ≤
      (shellBad (extendedWindow p) M).card +
        (transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M))).card := by
  calc
    _ ≤ ((shellBad (extendedWindow p) M) ∪
        transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M))).card :=
      Finset.card_le_card (shellBad_pullback_subset p S hM)
    _ ≤ _ := Finset.card_union_le _ _

theorem targetScale_pos (r : ℝ) (M : ℕ) : 0 < targetScale r M := by
  unfold targetScale
  positivity

/-- The floor in `targetScale` costs at most one factor of two. -/
theorem targetScale_rpow_neg_le {r D : ℝ} {M : ℕ}
    (hr : 0 ≤ r) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    (targetScale r M : ℝ) ^ (-D) ≤
      2 * Real.exp (-(r * D * M * Real.log 2)) := by
  have hx0 : 0 ≤ r * (M : ℝ) := mul_nonneg hr (Nat.cast_nonneg M)
  have hfloor : r * (M : ℝ) - 1 < (⌊r * (M : ℝ)⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  have hExp :
      -D * (⌊r * (M : ℝ)⌋₊ : ℝ) ≤ D - r * D * M := by
    nlinarith
  calc
    (targetScale r M : ℝ) ^ (-D) =
        (2 : ℝ) ^ (-D * (⌊r * (M : ℝ)⌋₊ : ℝ)) := by
      unfold targetScale
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (D - r * D * M) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    _ ≤ (2 : ℝ) ^ (1 - r * D * M) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 * Real.exp (-(r * D * M * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        show Real.log 2 * (1 - r * D * M) =
          Real.log 2 + -(r * D * M * Real.log 2) by ring,
        Real.exp_add, Real.exp_log (by norm_num)]

/-- Elementary polynomial-versus-exponential payment used in (5.14). -/
theorem square_exp_payment {q x : ℝ} (hq : 0 < q) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-(q * x)) ≤ 4 / q ^ 2 := by
  let z := q * x / 2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzexp : z ≤ Real.exp z := by
    have h := Real.add_one_le_exp z
    linarith
  have hsq : z ^ 2 ≤ (Real.exp z) ^ 2 :=
    (sq_le_sq₀ hz (Real.exp_pos z).le).2 hzexp
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hcore : x ^ 2 ≤ (4 / q ^ 2) * Real.exp (q * x) := by
    have hexp : (Real.exp z) ^ 2 = Real.exp (q * x) := by
      rw [pow_two, ← Real.exp_add]
      dsimp [z]
      congr 1
      ring
    rw [hexp] at hsq
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq2).2
    dsimp [z] at hsq
    nlinarith
  have hexpPos : 0 < Real.exp (q * x) := Real.exp_pos _
  calc
    x ^ 2 * Real.exp (-(q * x)) = x ^ 2 / Real.exp (q * x) := by
      rw [Real.exp_neg]
      ring
    _ ≤ 4 / q ^ 2 := (div_le_iff₀ hexpPos).2 (by
      nlinarith [hcore])

/-- The transported part of a failed shell pullback, with the target density
and floor loss already inserted. -/
theorem transportedBad_le {r eta C D : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    {M : ℕ} (hM : p.M0 ≤ M) :
    ((transportedSources M (targetScale r M) M
      (badTarget S (targetScale r M))).card : ℝ) ≤
      5 * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        Real.exp (-(r * D * M * Real.log 2)) := by
  let Y := targetScale r M
  have hY : 0 < Y := targetScale_pos r M
  have hYone : 1 ≤ Y := hY
  have hYM := p.target_lt_shell M hM
  have hMpos : 1 ≤ M := by
    have hYgt := p.target_one_lt M hM
    by_contra hzero
    have : M = 0 := by omega
    subst M
    have hbad := p.target_one_lt 0 hM
    norm_num [targetScale] at hbad
  have htransportQ := arbitraryTarget_linear_transport
    (M := M) (Y := Y) (H := M) (badTarget S Y)
    hY hMpos (p.horizon_small M hM) hYM
  have htransport :
      ((transportedSources M Y M (badTarget S Y)).card : ℝ) ≤
        (5 / 2 : ℝ) * (M : ℝ) ^ 2 * (2 : ℝ) ^ M /
          (Y : ℝ) * ((badTarget S Y).card : ℝ) := by
    have hcast :
        (((transportedSources M Y M (badTarget S Y)).card : ℚ) : ℝ) ≤
          (((5 / 2 : ℚ) * (M : ℚ) ^ 2 * (2 : ℚ) ^ M /
            (Y : ℚ) * ((badTarget S Y).card : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.2 htransportQ
    simpa using hcast
  have hbad : ((badTarget S Y).card : ℝ) ≤
      C * (Y : ℝ) ^ (1 - D) := by
    rw [card_badTarget]
    exact hS.bad_bound Y hYone
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hC : 0 < C := hS.C_pos
  have hmain :
      ((transportedSources M Y M (badTarget S Y)).card : ℝ) ≤
        (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
          (Y : ℝ) ^ (-D) := by
    calc
      _ ≤ (5 / 2 : ℝ) * (M : ℝ) ^ 2 * (2 : ℝ) ^ M /
          (Y : ℝ) * ((badTarget S Y).card : ℝ) := htransport
      _ ≤ (5 / 2 : ℝ) * (M : ℝ) ^ 2 * (2 : ℝ) ^ M /
          (Y : ℝ) * (C * (Y : ℝ) ^ (1 - D)) := by
        exact mul_le_mul_of_nonneg_left hbad (by positivity)
      _ = (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
          (Y : ℝ) ^ (-D) := by
        rw [show (1 : ℝ) - D = 1 + (-D) by ring,
          Real.rpow_add hYreal, Real.rpow_one]
        field_simp
  have hfloor := targetScale_rpow_neg_le p.r_pos.le hS.D_pos.le hS.D_le_one
    (M := M)
  calc
    _ ≤ (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        (Y : ℝ) ^ (-D) := hmain
    _ ≤ (5 / 2 : ℝ) * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        (2 * Real.exp (-(r * D * M * Real.log 2))) := by
      exact mul_le_mul_of_nonneg_left hfloor (by positivity)
    _ = 5 * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        Real.exp (-(r * D * M * Real.log 2)) := by ring

/-- Exponential margin available when transport uses `chi < r`. -/
def transportGap (r chi : ℝ) : ℝ := (r - chi) * Real.log 2

theorem transportGap_pos {r chi : ℝ} (hchi : chi < r) :
    0 < transportGap r chi := by
  unfold transportGap
  exact mul_pos (sub_pos.mpr hchi) (Real.log_pos (by norm_num))

/-- Pay the polynomial transport factor from the strict exponent gap
`chi < r`. -/
theorem transportedBad_le_paid
    {r eta C D chi : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi : chi < r) {M : ℕ} (hM : p.M0 ≤ M) :
    ((transportedSources M (targetScale r M) M
      (badTarget S (targetScale r M))).card : ℝ) ≤
      (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
  have hraw := transportedBad_le p S hS hM
  have hq := transportGap_pos hchi
  have hD := hS.D_pos
  have hx : 0 ≤ D * (M : ℝ) := by positivity
  have hpay := square_exp_payment hq hx
  have hexpSplit :
      Real.exp (-(r * D * M * Real.log 2)) =
        Real.exp (-(transportGap r chi * (D * M))) *
          Real.exp (-(chi * D * Real.log 2 * M)) := by
    rw [← Real.exp_add]
    congr 1
    unfold transportGap
    ring
  have hpoly :
      (M : ℝ) ^ 2 *
          Real.exp (-(transportGap r chi * (D * M))) ≤
        (4 / transportGap r chi ^ 2) * D⁻¹ ^ 2 := by
    have hDne : D ≠ 0 := ne_of_gt hD
    calc
      (M : ℝ) ^ 2 * Real.exp (-(transportGap r chi * (D * M))) =
          D⁻¹ ^ 2 *
            ((D * M) ^ 2 *
              Real.exp (-(transportGap r chi * (D * M)))) := by
        field_simp [hDne]
      _ ≤ D⁻¹ ^ 2 * (4 / transportGap r chi ^ 2) :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
      _ = (4 / transportGap r chi ^ 2) * D⁻¹ ^ 2 := by ring
  rw [hexpSplit] at hraw
  calc
    _ ≤ 5 * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        (Real.exp (-(transportGap r chi * (D * M))) *
          Real.exp (-(chi * D * Real.log 2 * M))) := hraw
    _ = 5 * C *
        ((M : ℝ) ^ 2 *
          Real.exp (-(transportGap r chi * (D * M)))) *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by ring
    _ ≤ 5 * C *
        ((4 / transportGap r chi ^ 2) * D⁻¹ ^ 2) *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
      have hfiveC : 0 ≤ 5 * C := mul_nonneg (by norm_num) hS.C_pos.le
      gcongr
    _ = (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by ring

/-- The fixed maximal-barrier complement is cheaper than the requested
`chi*D` shell exponent whenever `chi*D ≤ D_eta`. -/
theorem extendedWindow_shellBad_le
    {r eta D chi Dc : ℝ} (p : StageSetup r eta)
    (hDDc : D ≤ Dc)
    (hchi0 : 0 ≤ chi)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (M : ℕ) :
    ((shellBad (extendedWindow p) M).card : ℝ) ≤
      2 * quadraticWindowGlobalConstant eta *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
  have hW := extendedWindow_powerDense p
  have hcardNat := shellBad_card_le_badCount (extendedWindow p) M
  have hcard :
      ((shellBad (extendedWindow p) M).card : ℝ) ≤
        (badCount (extendedWindow p) (2 ^ (M + 1)) : ℝ) := by
    exact_mod_cast hcardNat
  have hprefix := hW.bad_bound (2 ^ (M + 1))
    (Nat.one_le_pow (M + 1) 2 (by omega))
  norm_num at hprefix
  have hrate : chi * D ≤ quadraticWindowDensityRate eta := by
    exact (mul_le_mul_of_nonneg_left hDDc hchi0).trans hDcRate
  have hExp :
      ((M : ℝ) + 1) * (1 - quadraticWindowDensityRate eta) ≤
        (M : ℝ) + 1 - chi * D * M := by
    have hratePos := hW.D_pos
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hpow :
      ((2 : ℝ) ^ (M + 1)) ^
          (1 - quadraticWindowDensityRate eta) ≤
        (2 : ℝ) ^ ((M : ℝ) + 1 - chi * D * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num at hExp ⊢
    exact hExp
  have hKpos := hW.C_pos.le
  calc
    ((shellBad (extendedWindow p) M).card : ℝ) ≤
        (badCount (extendedWindow p) (2 ^ (M + 1)) : ℝ) := hcard
    _ ≤ quadraticWindowGlobalConstant eta *
        ((2 : ℝ) ^ (M + 1)) ^
          (1 - quadraticWindowDensityRate eta) := hprefix
    _ ≤ quadraticWindowGlobalConstant eta *
        (2 : ℝ) ^ ((M : ℝ) + 1 - chi * D * M) :=
      mul_le_mul_of_nonneg_left hpow hKpos
    _ = 2 * quadraticWindowGlobalConstant eta *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        show Real.log 2 * ((M : ℝ) + 1 - chi * D * M) =
          Real.log 2 + (M : ℝ) * Real.log 2 +
            -(chi * D * Real.log 2 * M) by ring,
        Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
        Real.exp_nat_mul (Real.log 2) M, Real.exp_log (by norm_num)]
      ring

/-- One-shell prefactor in the dense-set first-passage pullback. -/
def pullbackShellConstant {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) : ℝ :=
  Real.exp (chi * Dc * Real.log 2 * p.M0) +
    2 * quadraticWindowGlobalConstant eta +
    20 / transportGap r chi ^ 2

/-- Global prefactor obtained by summing the pullback shell estimates. -/
def pullbackGlobalConstant {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) : ℝ :=
  2 * pullbackShellConstant p chi Dc /
    (2 * Real.exp (-(chi * Dc * Real.log 2)) - 1)

theorem pullbackShellConstant_pos {r eta chi Dc : ℝ}
    (p : StageSetup r eta) (hchi : chi < r) :
    0 < pullbackShellConstant p chi Dc := by
  unfold pullbackShellConstant
  have hq := transportGap_pos hchi
  have hW := extendedWindow_powerDense p
  have hC := hW.C_pos
  positivity

/-- Uniform all-shell bound underlying the dense-set pullback theorem. -/
theorem firstPassagePullback_shell_bound
    {r eta C D chi Dc : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi0 : 0 < chi) (hchi : chi < r)
    (hDc0 : 0 < Dc)
    (hDDc : D ≤ Dc)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (M : ℕ) :
    ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
      pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
  classical
  have hD0 := hS.D_pos
  have hD1 := hS.D_le_one
  have hC0 := hS.C_pos
  have hC1 : 1 ≤ C + 1 := by linarith
  have hDinv : 1 ≤ D⁻¹ ^ 2 := by
    have hInv : 1 ≤ D⁻¹ := by
      exact (one_le_inv₀ hD0).2 hD1
    exact one_le_pow₀ hInv
  by_cases hlarge : p.M0 ≤ M
  · have hcardNat := card_shellBad_pullback_le p S hlarge
    have hcard :
        ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
          ((shellBad (extendedWindow p) M).card : ℝ) +
            ((transportedSources M (targetScale r M) M
              (badTarget S (targetScale r M))).card : ℝ) := by
      exact_mod_cast hcardNat
    have hW := extendedWindow_shellBad_le p hDDc hchi0.le hDcRate M
    have hT := transportedBad_le_paid p S hS hchi hlarge
    have hcoeff :
        2 * quadraticWindowGlobalConstant eta +
            (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 ≤
          pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
      have hWconst := (extendedWindow_powerDense p).C_pos.le
      have hgap : 0 ≤ 20 / transportGap r chi ^ 2 := by positivity
      have hstart : 0 ≤ Real.exp (chi * Dc * Real.log 2 * p.M0) := by
        positivity
      have hB : 0 ≤ 2 * quadraticWindowGlobalConstant eta := by positivity
      have hE : 0 ≤ D⁻¹ ^ 2 := sq_nonneg _
      have hCplus : 0 ≤ C + 1 := (by linarith : 0 ≤ C + 1)
      have hF : 1 ≤ (C + 1) * D⁻¹ ^ 2 := by
        simpa only [one_mul] using
          mul_le_mul hC1 hDinv (by norm_num : (0 : ℝ) ≤ 1) hCplus
      have hBpay :
          2 * quadraticWindowGlobalConstant eta ≤
            (2 * quadraticWindowGlobalConstant eta) * ((C + 1) * D⁻¹ ^ 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hF hB
      have hGpay :
          (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 ≤
            (20 / transportGap r chi ^ 2) * (C + 1) * D⁻¹ ^ 2 := by
        have hCle : C ≤ C + 1 := by linarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCle hgap) hE
      calc
        2 * quadraticWindowGlobalConstant eta +
              (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 ≤
            (2 * quadraticWindowGlobalConstant eta) * ((C + 1) * D⁻¹ ^ 2) +
              (20 / transportGap r chi ^ 2) * (C + 1) * D⁻¹ ^ 2 :=
          add_le_add hBpay hGpay
        _ = (2 * quadraticWindowGlobalConstant eta +
              20 / transportGap r chi ^ 2) * ((C + 1) * D⁻¹ ^ 2) := by ring
        _ ≤ (Real.exp (chi * Dc * Real.log 2 * p.M0) +
              2 * quadraticWindowGlobalConstant eta +
              20 / transportGap r chi ^ 2) * ((C + 1) * D⁻¹ ^ 2) := by
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hCplus hE)
        _ = pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
          unfold pullbackShellConstant
          ring
    have hnonneg :
        0 ≤ Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
      positivity
    calc
      _ ≤ ((shellBad (extendedWindow p) M).card : ℝ) +
          ((transportedSources M (targetScale r M) M
            (badTarget S (targetScale r M))).card : ℝ) := hcard
      _ ≤ (2 * quadraticWindowGlobalConstant eta +
            (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2) *
          Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
        nlinarith [hW, hT]
      _ ≤ pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
          Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
        calc
          _ = (2 * quadraticWindowGlobalConstant eta +
                (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2) *
              (Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M) := by
            ring
          _ ≤ (pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2) *
              (Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M) :=
            mul_le_mul_of_nonneg_right hcoeff hnonneg
          _ = _ := by ring
  · have hMlt : M < p.M0 := by omega
    have hcardNat :
        (shellBad (firstPassagePullback p S) M).card ≤ (dyadicShell M).card := by
      apply Finset.card_le_card
      intro n hn
      exact (Finset.mem_filter.mp hn).1
    have hcard :
        ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
          (2 : ℝ) ^ M := by
      rw [card_dyadicShell] at hcardNat
      exact_mod_cast hcardNat
    have hrate :
        chi * D * (M : ℝ) ≤ chi * Dc * p.M0 := by
      have hMle : (M : ℝ) ≤ p.M0 := by exact_mod_cast hMlt.le
      calc
        chi * D * (M : ℝ) ≤ chi * Dc * (M : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDDc hchi0.le) (Nat.cast_nonneg M)
        _ ≤ chi * Dc * (p.M0 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hMle
            (mul_nonneg hchi0.le hDc0.le)
    have hfactor :
        1 ≤ Real.exp (chi * Dc * Real.log 2 * p.M0) *
          Real.exp (-(chi * D * Real.log 2 * M)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    have hK :
        Real.exp (chi * Dc * Real.log 2 * p.M0) ≤
          pullbackShellConstant p chi Dc := by
      unfold pullbackShellConstant
      have hWconst := (extendedWindow_powerDense p).C_pos.le
      have hgap : 0 ≤ 20 / transportGap r chi ^ 2 := by positivity
      nlinarith
    have hbig :
        1 ≤ pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
          Real.exp (-(chi * D * Real.log 2 * M)) := by
      have hKC :
          Real.exp (chi * Dc * Real.log 2 * p.M0) ≤
            pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
        calc
          _ ≤ pullbackShellConstant p chi Dc := hK
          _ ≤ pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
            have hpK := (pullbackShellConstant_pos (Dc := Dc) p hchi).le
            have hCplus : 0 ≤ C + 1 := by linarith
            have hF : 1 ≤ (C + 1) * D⁻¹ ^ 2 := by
              simpa only [one_mul] using
                mul_le_mul hC1 hDinv (by norm_num : (0 : ℝ) ≤ 1) hCplus
            calc
              pullbackShellConstant p chi Dc =
                  pullbackShellConstant p chi Dc * 1 := by ring
              _ ≤ pullbackShellConstant p chi Dc * ((C + 1) * D⁻¹ ^ 2) :=
                mul_le_mul_of_nonneg_left hF hpK
              _ = pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
                ring
      have hexp0 : 0 ≤ Real.exp (-(chi * D * Real.log 2 * M)) := by
        positivity
      exact hfactor.trans
        (mul_le_mul_of_nonneg_right hKC hexp0)
    calc
      _ ≤ (2 : ℝ) ^ M := hcard
      _ = 1 * (2 : ℝ) ^ M := by ring
      _ ≤ (pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
          Real.exp (-(chi * D * Real.log 2 * M))) * (2 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = _ := by ring

/-- First-passage pullback preserves quantitative density with
linear exponent transport `D ↦ chi D`. -/
theorem firstPassagePullback_powerDense
    {r eta C D chi Dc : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi0 : 0 < chi) (hchi : chi < r)
    (hDc0 : 0 < Dc)
    (hDDc : D ≤ Dc)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) :
    PowerDense (firstPassagePullback p S)
      (pullbackGlobalConstant p chi Dc * (C + 1) * D⁻¹ ^ 2)
      (chi * D) := by
  have hD0 := hS.D_pos
  have hD1 := hS.D_le_one
  have hc0 : 0 < chi * D * Real.log 2 := by positivity
  have hcLt : chi * D * Real.log 2 < Real.log 2 := by
    have : chi * D < 1 :=
      (mul_le_mul_of_nonneg_left hDDc hchi0.le).trans_lt hchiDc
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hK0 :
      0 < pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
    exact mul_pos
      (mul_pos (pullbackShellConstant_pos p hchi) (by linarith [hS.C_pos]))
      (sq_pos_of_pos (inv_pos.mpr hD0))
  have hshell : ∀ M : ℕ,
      ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
        (pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2) *
          Real.exp (-(chi * D * Real.log 2) * M) * (2 : ℝ) ^ M := by
    intro M
    convert firstPassagePullback_shell_bound p S hS hchi0 hchi hDc0
      hDDc hDcRate M using 1
    all_goals ring
  have hraw := powerDense_of_shell_bound hK0 hc0 hcLt hshell
  have hlog2ne : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hrateEq : chi * D * Real.log 2 / Real.log 2 = chi * D := by
    field_simp [hlog2ne]
  rw [hrateEq] at hraw
  have hdenDc : 0 < 2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 := by
    have hExpLog : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have hlt : -Real.log 2 < -(chi * Dc * Real.log 2) := by
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    have hexp := Real.exp_lt_exp.2 hlt
    rw [hExpLog] at hexp
    linarith
  have hden :
      2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 ≤
        2 * Real.exp (-(chi * D * Real.log 2)) - 1 := by
    have hrate := mul_le_mul_of_nonneg_left hDDc hchi0.le
    have hexp :
        Real.exp (-(chi * Dc * Real.log 2)) ≤
          Real.exp (-(chi * D * Real.log 2)) := by
      apply Real.exp_le_exp.2
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    nlinarith
  apply hraw.mono_constant
  unfold pullbackGlobalConstant
  have hnum :
      0 ≤ 2 * pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
    exact (mul_pos
      (mul_pos (mul_pos (by norm_num) (pullbackShellConstant_pos p hchi))
        (by linarith [hS.C_pos]))
      (sq_pos_of_pos (inv_pos.mpr hD0))).le
  have hdiv := div_le_div_of_nonneg_left hnum hdenDc hden
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

end

end FirstPassageLinearTransport
