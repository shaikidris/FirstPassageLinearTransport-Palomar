/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.NaturalDensityDescent
import FirstPassageLinearTransport.TimeoutDensity
import FirstPassageLinearTransport.RawDynamics

/-!
# Intermediate-orbit ceiling

Formalization of the intermediate path bound.  The maximal barrier controls
every shortcut prefix inside one stopped block.  Iterating that estimate
introduces only a power of the fixed startup constant; on the logarithmic
stage schedule this is polynomial in the shell index and is absorbed by the
strict exponent margin `eta < beta`.
-/

namespace FirstPassageLinearTransport

open Filter
open scoped Real Topology

noncomputable section

/-! ## Finite multiplicative maximum: shell and trajectory adapters -/

theorem ballotMultiplier_finTwoEquiv (b : Fin 2) :
    ballotMultiplier (finTwoEquiv b) = (3 : ℝ) ^ (b : ℕ) / 2 := by
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  rcases hb with hb | hb
  · have hbeq : b = 0 := Fin.ext hb
    subst b
    norm_num [ballotMultiplier, finTwoEquiv]
  · have hbeq : b = 1 := Fin.ext hb
    subst b
    norm_num [ballotMultiplier, finTwoEquiv]

theorem ballotMultiplier_boolParityWord_zero (r n : ℕ) :
    ballotMultiplier (boolParityWord (r + 1) n 0) =
      (3 : ℝ) ^ (parityBit n 0 : ℕ) / 2 := by
  exact ballotMultiplier_finTwoEquiv (parityBit n 0)

/-- Avoiding the recursive multiplicative hit event bounds every pure
Collatz multiplicative prefix. -/
theorem multiplicative_prefix_le_of_not_crosses :
    ∀ {r n : ℕ} {u z : ℝ},
      0 ≤ z →
      ¬crossesMultiplicativeFrom u r z (boolParityWord r n) →
      ∀ H : ℕ, H ≤ r →
        z * ((3 : ℝ) ^ oddCount n H / (2 : ℝ) ^ H) ≤ u := by
  intro r
  induction r with
  | zero =>
      intro n u z hz hsafe H hHr
      have hH : H = 0 := by omega
      subst H
      have hzu : z ≤ u := le_of_not_gt (by
        simpa [crossesMultiplicativeFrom] using hsafe)
      simpa using hzu
  | succ r ih =>
      intro n u z hz hsafe H hHr
      have hdecomp :
          ¬u < z ∧
            ¬crossesMultiplicativeFrom u r
              (z * ballotMultiplier (boolParityWord (r + 1) n 0))
              (boolParityWord r (shortcut n)) := by
        have hraw :
            ¬u < z ∧
              ¬crossesMultiplicativeFrom u r
                (z * ballotMultiplier (boolParityWord (r + 1) n 0))
                (fun i => boolParityWord (r + 1) n i.succ) := by
          simpa [crossesMultiplicativeFrom] using hsafe
        simpa [boolParityWord_tail] using hraw
      rcases hdecomp with ⟨hcurrent, htail⟩
      cases H with
      | zero =>
          simpa using (le_of_not_gt hcurrent)
      | succ H =>
          have hHr' : H ≤ r := by omega
          have hmult0 : 0 ≤ ballotMultiplier
              (boolParityWord (r + 1) n 0) := by
            cases hbit : boolParityWord (r + 1) n 0 <;>
              norm_num [ballotMultiplier, hbit]
          have hchild := ih
            (n := shortcut n) (u := u)
            (z := z * ballotMultiplier (boolParityWord (r + 1) n 0))
            (mul_nonneg hz hmult0) htail H hHr'
          rw [ballotMultiplier_boolParityWord_zero] at hchild
          rw [oddCount_succ_shift]
          rw [pow_add, pow_succ]
          convert hchild using 1 <;> ring

/-- A crossing of the recursive finite-word event is witnessed by an actual
prefix of the corresponding shortcut parity word. -/
theorem exists_multiplicative_prefix_gt_of_crosses :
    ∀ {r n : ℕ} {u z : ℝ},
      crossesMultiplicativeFrom u r z (boolParityWord r n) →
      ∃ H : ℕ, H ≤ r ∧
        u < z * ((3 : ℝ) ^ oddCount n H / (2 : ℝ) ^ H) := by
  intro r
  induction r with
  | zero =>
      intro n u z hcross
      refine ⟨0, by omega, ?_⟩
      simpa [crossesMultiplicativeFrom] using hcross
  | succ r ih =>
      intro n u z hcross
      have hdecomp :
          u < z ∨
            crossesMultiplicativeFrom u r
              (z * ballotMultiplier (boolParityWord (r + 1) n 0))
              (boolParityWord r (shortcut n)) := by
        have hraw :
            u < z ∨
              crossesMultiplicativeFrom u r
                (z * ballotMultiplier (boolParityWord (r + 1) n 0))
                (fun i => boolParityWord (r + 1) n i.succ) := by
          simpa [crossesMultiplicativeFrom] using hcross
        simpa [boolParityWord_tail] using hraw
      rcases hdecomp with hcurrent | htail
      · exact ⟨0, by omega, by simpa using hcurrent⟩
      · obtain ⟨H, hHr, hchild⟩ := ih htail
        refine ⟨H + 1, by omega, ?_⟩
        rw [ballotMultiplier_boolParityWord_zero] at hchild
        rw [oddCount_succ_shift, pow_add, pow_succ]
        convert hchild using 1 <;> ring

/-- The pure multiplicative part of the affine Collatz iterate is a lower
bound for the actual shortcut state. -/
theorem pure_multiplicative_le_orbit (n j : ℕ) :
    ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) ≤
      (orbit j n : ℝ) := by
  rw [exact_affine_iterate_real]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _hi => by positivity)

/-- Residues whose finite Collatz multiplicative word crosses `u`. -/
noncomputable def multiplicativeHitResidues (M : ℕ) (u : ℝ) :
    Finset (Fin (2 ^ M)) := by
  classical
  exact Finset.univ.filter fun x =>
    crossesMultiplicativeFrom u M 1 (boolParityCode M x)

/-- Exact parity restriction from multiplicative-hit residues to Boolean
words. -/
noncomputable def multiplicativeHitResidueEquiv (M : ℕ) (u : ℝ) :
    {x : Fin (2 ^ M) //
      crossesMultiplicativeFrom u M 1 (boolParityCode M x)} ≃
      {v : Fin M → Bool // crossesMultiplicativeFrom u M 1 v} :=
  (boolParityEquiv M).subtypeEquiv (fun x => by
    rw [boolParityEquiv_apply])

theorem card_multiplicativeHitResidues (M : ℕ) (u : ℝ) :
    (multiplicativeHitResidues M u).card =
      multiplicativeHitCount u M 1 := by
  classical
  unfold multiplicativeHitResidues multiplicativeHitCount
  rw [← Fintype.card_subtype (fun x : Fin (2 ^ M) =>
        crossesMultiplicativeFrom u M 1 (boolParityCode M x)),
      ← Fintype.card_subtype (crossesMultiplicativeFrom u M 1)]
  exact Fintype.card_congr (multiplicativeHitResidueEquiv M u)

/-- The exact dyadic-shell event corresponding to the finite multiplicative
hit. -/
noncomputable def shellMultiplicativeHit (M : ℕ) (u : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    crossesMultiplicativeFrom u M 1 (boolParityWord M n)

theorem card_shellMultiplicativeHit (M : ℕ) (u : ℝ) :
    (shellMultiplicativeHit M u).card = multiplicativeHitCount u M 1 := by
  classical
  have heq : shellMultiplicativeHit M u =
      (dyadicShell M).filter fun n =>
        (⟨n % (2 ^ M), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
          Fin (2 ^ M)) ∈ multiplicativeHitResidues M u := by
    ext n
    simp only [shellMultiplicativeHit, multiplicativeHitResidues,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => by
      rw [boolParityCode_eq_word, boolParityWord_mod])
  rw [heq, card_dyadicShell_filter_mod_mem,
    card_multiplicativeHitResidues]

theorem normalized_card_shellMultiplicativeHit_le_inv
    {u : ℝ} (hu : 0 < u) (M : ℕ) :
    ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ≤ u⁻¹ := by
  rw [card_shellMultiplicativeHit]
  exact normalized_multiplicativeHitCount_le_inv hu M

/-- The finite reciprocal maximum theorem transfers without loss to a
complete dyadic shell.  This is the shell form of the lower and upper bounds
used by the height obstruction. -/
theorem normalized_card_shellMultiplicativeHit_reciprocal
    {u : ℝ} (hu : 1 ≤ u) {M : ℕ} (hM : 0 < M)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (M : ℝ) * Real.log 3) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (M : ℝ)) ≤
      ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ∧
    ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ≤ u⁻¹ := by
  rw [card_shellMultiplicativeHit]
  exact reciprocal_finite_multiplicative_maximum hu hM hlog

/-- Membership in the shell multiplicative-hit event forces an actual
shortcut prefix above the corresponding relative-height ceiling. -/
theorem exists_orbit_gt_mul_of_mem_shellMultiplicativeHit
    {M n : ℕ} {u : ℝ} (hn : n ∈ shellMultiplicativeHit M u) :
    ∃ j : ℕ, j ≤ M ∧ u * (n : ℝ) < (orbit j n : ℝ) := by
  classical
  have hnFilter := Finset.mem_filter.mp hn
  have hnShell : n ∈ dyadicShell M := hnFilter.1
  have hcross :
      crossesMultiplicativeFrom u M 1 (boolParityWord M n) := hnFilter.2
  obtain ⟨j, hjM, hj⟩ :=
    exists_multiplicative_prefix_gt_of_crosses hcross
  have hnPosNat : 0 < n := by
    have hnLower : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
    exact (pow_pos (by omega) M).trans_le hnLower
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have hscaled := mul_lt_mul_of_pos_right hj hnPos
  have hscaled' :
      u * (n : ℝ) <
        ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) := by
    simpa using hscaled
  exact ⟨j, hjM, hscaled'.trans_le (pure_multiplicative_le_orbit n j)⟩

/-- The quarter-threshold normalization used by the manuscript contributes
the explicit shell exception `4/R`. -/
theorem normalized_card_shellMultiplicativeHit_quarter_le
    {R : ℝ} (hR : 0 < R) (M : ℕ) :
    ((shellMultiplicativeHit M (R / 4)).card : ℝ) /
        (2 : ℝ) ^ M ≤ 4 / R := by
  have h := normalized_card_shellMultiplicativeHit_le_inv
    (u := R / 4) (by positivity) M
  calc
    _ ≤ (R / 4)⁻¹ := h
    _ = 4 / R := by field_simp

/-- Outside the finite-word hit event, every shortcut prefix up to the shell
rank is bounded by twice the prescribed multiplicative threshold. -/
theorem orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
    {M n : ℕ} {u : ℝ}
    (hn : n ∈ dyadicShell M) (hnGood : n ∉ shellMultiplicativeHit M u)
    {j : ℕ} (hj : j ≤ M) :
    (orbit j n : ℝ) < 2 * u * n := by
  have hsafe :
      ¬crossesMultiplicativeFrom u M 1 (boolParityWord M n) := by
    simpa [shellMultiplicativeHit, hn] using hnGood
  have hmult := multiplicative_prefix_le_of_not_crosses
    (z := 1) (by norm_num) hsafe j hj
  have hscaled := orbit_scaled_lt_two_mul_parity hn hj
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have hscaledR :
      (2 : ℝ) ^ j * (orbit j n : ℝ) <
        2 * (3 : ℝ) ^ oddCount n j * (n : ℝ) := by
    exact_mod_cast hscaled
  have hFn :
      ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) ≤
        u * (n : ℝ) := by
    have hF : (3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j ≤ u := by
      simpa using hmult
    gcongr
  apply lt_of_mul_lt_mul_left (a := (2 : ℝ) ^ j) _ hpow.le
  calc
    (2 : ℝ) ^ j * (orbit j n : ℝ) <
        2 * (3 : ℝ) ^ oddCount n j * (n : ℝ) := hscaledR
    _ = (2 : ℝ) ^ j *
        (2 * (((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) *
          (n : ℝ))) := by field_simp
    _ ≤ (2 : ℝ) ^ j * (2 * (u * (n : ℝ))) := by gcongr
    _ = (2 : ℝ) ^ j * (2 * u * n) := by ring

/-- Every raw iterate through a shortcut prefix is either a shortcut state or
the single doubled intermediate state following an odd shortcut source. -/
theorem rawOrbit_le_two_mul_of_shortcut_prefix_le
    {n k : ℕ} {C : ℝ}
    (hshortcut : ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ C) :
    ∀ i : ℕ, i ≤ rawTime n k → (rawOrbit i n : ℝ) ≤ 2 * C := by
  induction k with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by simpa [rawTime] using hi
      subst i
      have hnC := hshortcut 0 (by omega)
      simp [orbit_zero] at hnC
      have hC0 : 0 ≤ C := (Nat.cast_nonneg n).trans hnC
      simp only [rawOrbit_zero]
      linarith
  | succ k ih =>
      have hprev : ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ C :=
        fun j hj => hshortcut j (hj.trans (Nat.le_succ k))
      have hIH := ih hprev
      intro i hi
      by_cases hiprev : i ≤ rawTime n k
      · exact hIH i hiprev
      · let q := i - rawTime n k
        have hiForm : i = q + rawTime n k := by
          dsimp [q]
          omega
        have hqPos : 0 < q := by dsimp [q]; omega
        have hrawBase : rawOrbit (rawTime n k) n = orbit k n :=
          rawOrbit_rawTime_eq_orbit n k
        rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
        · have hbit : (parityBit n k : ℕ) = 0 := by
            simpa [parityBit] using heven
          have htimeSucc : rawTime n (k + 1) = rawTime n k + 1 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hq : q = 1 := by
            rw [htimeSucc] at hi
            dsimp [q]
            omega
          rw [hiForm, rawOrbit_add, hrawBase, hq, rawOrbit_succ,
            rawOrbit_zero, rawCollatz_eq_shortcut_of_even heven, ← orbit_succ]
          have hnext := hshortcut (k + 1) (by omega)
          have hC0 : 0 ≤ C := (Nat.cast_nonneg (orbit (k + 1) n)).trans hnext
          linarith
        · have hbit : (parityBit n k : ℕ) = 1 := by
            simpa [parityBit] using hodd
          have htimeSucc : rawTime n (k + 1) = rawTime n k + 2 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hqLe : q ≤ 2 := by
            rw [htimeSucc] at hi
            dsimp [q]
            omega
          have hnext := hshortcut (k + 1) (by omega)
          have hC0 : 0 ≤ C := (Nat.cast_nonneg (orbit (k + 1) n)).trans hnext
          have hqCases : q = 1 ∨ q = 2 := by omega
          rcases hqCases with hq | hq
          · rw [hiForm, hq, rawOrbit_add, hrawBase, rawOrbit_succ,
              rawOrbit_zero, rawCollatz_of_odd hodd]
            calc
              ((3 * orbit k n + 1 : ℕ) : ℝ) =
                  (2 : ℝ) * (orbit (k + 1) n : ℝ) := by
                exact_mod_cast (show 3 * orbit k n + 1 =
                  2 * orbit (k + 1) n by
                    rw [orbit_succ, shortcut_of_odd hodd]
                    omega)
              _ ≤ 2 * C :=
                mul_le_mul_of_nonneg_left hnext (by norm_num)
          · rw [hiForm, hq, rawOrbit_add, hrawBase,
              rawOrbit_two_eq_shortcut_of_odd hodd, ← orbit_succ]
            linarith

/-- The exact first-block height interface used by the strengthened shell
theorem. -/
theorem initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
    {M n : ℕ} {R : ℝ}
    (hn : n ∈ dyadicShell M)
    (hnGood : n ∉ shellMultiplicativeHit M (R / 4)) :
    (∀ j : ℕ, j ≤ M → (orbit j n : ℝ) < (n : ℝ) * R / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n M →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * R) := by
  have hshortcut : ∀ j : ℕ, j ≤ M →
      (orbit j n : ℝ) < (n : ℝ) * R / 2 := by
    intro j hj
    have h := orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
      hn hnGood hj
    convert h using 1 <;> ring
  refine ⟨hshortcut, ?_⟩
  intro i hi
  have hle : ∀ j : ℕ, j ≤ M →
      (orbit j n : ℝ) ≤ (n : ℝ) * R / 2 :=
    fun j hj => (hshortcut j hj).le
  have hraw := rawOrbit_le_two_mul_of_shortcut_prefix_le hle i hi
  convert hraw using 1 <;> ring

/-- Every prefix of one retained stopped block stays below the local
`1 + eta` power envelope. -/
theorem orbit_le_one_add_eta_of_le_stageLength
    {r eta : ℝ} (p : StageSetup r eta) {n j : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p)
    (hj : j ≤ stageLength p n) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + eta) := by
  by_cases hlarge : p.M0 ≤ Nat.log 2 n
  · have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW hlarge
    have hjlog : j ≤ Nat.log 2 n :=
      hj.trans (stageLength_le_log p hn hnW)
    have henv := (hgood j hjlog).2
    have hscale : centralOrbitScale j ≤ 1 := by
      rw [centralOrbitScale_eq_rho_pow]
      exact pow_le_one₀ rho_pos.le rho_lt_one.le
    exact henv.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hscale
          (Real.rpow_nonneg (by positivity) (1 + eta)))
  · have hlen : stageLength p n = 0 := by
      simp [stageLength, hlarge]
    have hj0 : j = 0 := by omega
    subst j
    rw [orbit_zero]
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (1 + eta) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [p.eta_pos])

/-- Raising one stopped endpoint to the local envelope exponent costs at
most two powers of the fixed startup constant. -/
theorem stageMap_rpow_one_add_eta_le
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    (stageMap p n : ℝ) ^ (1 + eta) ≤
      stageK p ^ 2 * (n : ℝ) ^ (1 + eta) := by
  have hstage := stageMap_le_power p hn hnW
  have hexp0 : 0 ≤ 1 + eta := by linarith [p.eta_pos]
  have hraise :
      (stageMap p n : ℝ) ^ (1 + eta) ≤
        (stageK p * (n : ℝ) ^ r) ^ (1 + eta) :=
    Real.rpow_le_rpow (by positivity) hstage hexp0
  have hKexp : stageK p ^ (1 + eta) ≤ stageK p ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (stageK_one_le p)
      (by linarith [p.eta_le_one])
  have hK : stageK p ^ (1 + eta) ≤ stageK p ^ 2 := by
    simpa [Real.rpow_two] using hKexp
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrexp : r * (1 + eta) ≤ 1 + eta := by
    nlinarith [p.r_lt_one.le, p.eta_pos]
  have hnPow : (n : ℝ) ^ (r * (1 + eta)) ≤
      (n : ℝ) ^ (1 + eta) :=
    Real.rpow_le_rpow_of_exponent_le hnOne hrexp
  calc
    (stageMap p n : ℝ) ^ (1 + eta) ≤
        (stageK p * (n : ℝ) ^ r) ^ (1 + eta) := hraise
    _ = stageK p ^ (1 + eta) *
        ((n : ℝ) ^ r) ^ (1 + eta) := by
      rw [Real.mul_rpow (stageK_pos p).le (by positivity)]
    _ = stageK p ^ (1 + eta) *
        (n : ℝ) ^ (r * (1 + eta)) := by
      rw [← Real.rpow_mul (by positivity)]
    _ ≤ stageK p ^ 2 * (n : ℝ) ^ (1 + eta) :=
      mul_le_mul hK hnPow (by positivity) (by positivity)

/-- Coarse all-prefix bootstrap envelope.  It deliberately keeps the
startup loss as `stageK^(2R)`; this becomes only polynomial on the scheduled
depth and is absorbed below. -/
theorem orbit_le_stageClock_ceiling
    {r eta : ℝ} (p : StageSetup r eta) {R n j : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R)
    (hj : j ≤ stageClock p R n) :
    (orbit j n : ℝ) ≤
      stageK p ^ (2 * R) * (n : ℝ) ^ (1 + eta) := by
  induction R generalizing n j with
  | zero =>
      have hj0 : j = 0 := by simpa using hj
      subst j
      rw [orbit_zero]
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc
        (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ (n : ℝ) ^ (1 + eta) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [p.eta_pos])
        _ = stageK p ^ (2 * 0) * (n : ℝ) ^ (1 + eta) := by simp
  | succ R ih =>
      rw [bootstrapSet_succ] at hnSet
      have hnW : n ∈ extendedWindow p := hnSet.1
      have hmapSet : stageMap p n ∈ bootstrapSet p R := hnSet.2
      by_cases hjlen : j ≤ stageLength p n
      · have hblock := orbit_le_one_add_eta_of_le_stageLength p hn hnW hjlen
        have hfactor : (1 : ℝ) ≤ stageK p ^ (2 * (R + 1)) :=
          one_le_pow₀ (stageK_one_le p)
        exact hblock.trans (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hfactor
              (Real.rpow_nonneg (by positivity) (1 + eta)))
      · let q := j - stageLength p n
        have hjform : j = stageLength p n + q := by
          dsimp [q]
          omega
        have hqclock : q ≤ stageClock p R (stageMap p n) := by
          rw [stageClock_succ] at hj
          dsimp [q]
          omega
        have hmapPos : 0 < stageMap p n := by
          rw [stageMap_is_actual]
          exact orbit_pos hn _
        have hIH := ih hmapPos hmapSet hqclock
        have hmapPow := stageMap_rpow_one_add_eta_le p hn hnW
        rw [hjform, add_comm, orbit_add, ← stageMap_is_actual]
        calc
          (orbit q (stageMap p n) : ℝ) ≤
              stageK p ^ (2 * R) *
                (stageMap p n : ℝ) ^ (1 + eta) := hIH
          _ ≤ stageK p ^ (2 * R) *
                (stageK p ^ 2 * (n : ℝ) ^ (1 + eta)) :=
            mul_le_mul_of_nonneg_left hmapPow
              (pow_nonneg (stageK_pos p).le _)
          _ = stageK p ^ (2 * (R + 1)) *
                (n : ℝ) ^ (1 + eta) := by
            rw [show 2 * (R + 1) = 2 * R + 2 by omega, pow_add]
            ring

/-- On the logarithmic stage schedule, the fixed startup factor in the
all-prefix envelope is swallowed by every strict exponent margin
`eta < beta`. -/
theorem eventuallyShellOrbitCeiling
    {r eta omega beta : ℝ} (p : StageSetup r eta)
    (homega : 0 < omega) (hetaBeta : eta < beta) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      ∀ j : ℕ, j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  let A := 2 * omega * Real.log (stageK p)
  let c := (beta - eta) * Real.log 2 / 2
  have hlogK0 : 0 ≤ Real.log (stageK p) :=
    Real.log_nonneg (stageK_one_le p)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos
      (mul_pos (sub_pos.mpr hetaBeta) (Real.log_pos (by norm_num)))
      (by norm_num)
  have hscalarReal := eventuallyLogAddRpowLe
    (A := A) (C := 0) (c := c) (a := (1 / 2 : ℝ)) (delta := 0)
    hA (by norm_num) hc (by norm_num) (by norm_num)
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hscalar := hxT.eventually hscalarReal
  filter_upwards [hscalar, eventually_ge_atTop (4 : ℕ)] with M hsc hM
  intro n hn hnshell hnboot j hj
  let R := stageCount omega M
  let x : ℝ := (M : ℝ) + 4
  have hx : 0 < x := by dsimp [x]; positivity
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by dsimp [x]; linarith)
  have hsc' : A * Real.log x ≤ c * x := by
    simpa [x] using hsc
  have hxM : x ≤ 2 * (M : ℝ) := by
    dsimp [x]
    exact_mod_cast (by omega : M + 4 ≤ 2 * M)
  have hlinear : A * Real.log x ≤
      (beta - eta) * (M : ℝ) * Real.log 2 := by
    calc
      A * Real.log x ≤ c * x := hsc'
      _ ≤ c * (2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hxM hc.le
      _ = (beta - eta) * (M : ℝ) * Real.log 2 := by
        dsimp [c]
        ring
  have hR := stageCount_le homega.le M
  have hRlog : (2 * R : ℕ) * Real.log (stageK p) ≤
      A * Real.log x := by
    have htwoLogK : 0 ≤ 2 * Real.log (stageK p) :=
      mul_nonneg (by norm_num) hlogK0
    have hmul := mul_le_mul_of_nonneg_right hR htwoLogK
    dsimp [R, A, x] at hmul ⊢
    push_cast at hmul ⊢
    nlinarith
  have hlowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnshell).1
  have hlowerCast : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast hlowerNat
  have hlogLower : (M : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)
      hlowerCast
    rw [Real.log_pow] at h
    exact h
  have hmargin : 0 ≤ beta - eta := sub_nonneg.mpr hetaBeta.le
  have hexponent : (2 * R : ℕ) * Real.log (stageK p) ≤
      (beta - eta) * Real.log n := by
    calc
      (2 * R : ℕ) * Real.log (stageK p) ≤ A * Real.log x := hRlog
      _ ≤ (beta - eta) * (M : ℝ) * Real.log 2 := hlinear
      _ ≤ (beta - eta) * Real.log n := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hlogLower hmargin)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor : stageK p ^ (2 * R) ≤ (n : ℝ) ^ (beta - eta) := by
    rw [← Real.exp_log (pow_pos (stageK_pos p) (2 * R)), Real.log_pow,
      Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.2
    push_cast
    simpa [mul_comm] using hexponent
  have hpath := orbit_le_stageClock_ceiling p hn hnboot hj
  calc
    (orbit j n : ℝ) ≤
        stageK p ^ (2 * R) * (n : ℝ) ^ (1 + eta) := hpath
    _ ≤ (n : ℝ) ^ (beta - eta) * (n : ℝ) ^ (1 + eta) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (1 + beta) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring

/-- One density-one set and one witness simultaneously satisfy the shortcut
clock, the stretched-log landing, and the intermediate-orbit ceiling through
that witness. -/
theorem firstPassageLinearTransportOrbitCeiling
    {delta beta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hbeta : 0 < beta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ k : ℕ,
              (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
                (orbit k n : ℝ) ≤
                  Real.exp ((Real.log n) ^ (1 - delta)) ∧
                ∀ j : ℕ, j ≤ k →
                  (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  let h : HeadlineScalars delta :=
    Classical.choice (exists_headlineScalars hdelta0 hdelta1)
  let eta := min ((h.r - a0) / 2) (beta / 2)
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact lt_min (by linarith [h.a0_lt_r]) (by linarith)
  have hetaGap : eta < h.r - a0 := by
    have hle : eta ≤ (h.r - a0) / 2 := min_le_left _ _
    dsimp only [eta] at hle ⊢
    linarith [h.a0_lt_r]
  have hetaBeta : eta < beta := by
    have hle : eta ≤ beta / 2 := min_le_right _ _
    dsimp only [eta] at hle ⊢
    linarith
  let p : StageSetup h.r eta :=
    Classical.choice (exists_stageSetup h.a0_lt_r h.r_lt_one
      heta0 hetaGap)
  let Dc := quadraticWindowDensityRate eta
  have hDc0 : 0 < Dc := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_pos
  have hDc1 : Dc ≤ 1 := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_le_one
  have hchiDc : h.chi * Dc < 1 := by
    have hprod : h.chi * Dc ≤ h.chi * 1 :=
      mul_le_mul_of_nonneg_left hDc1 h.chi_pos.le
    nlinarith [h.chi_lt_r.trans h.r_lt_one]
  have hdensity : densityGamma h.omega h.chi < 1 := by
    simpa [densityGamma, one_div] using h.density_compat
  have hdescent : delta < descentAlpha h.omega h.r := by
    simpa [descentAlpha, one_div] using h.descent_compat
  let S := assembledBootstrap p h.omega
  have hSdense : NaturalDensityOne S :=
    assembledBootstrap_naturalDensityOne_of_vanish p h.omega
      (shellBootstrapRatioTendstoZero p h.chi_pos h.chi_lt_r
        h.chi_le_one hDc0 hDc1 le_rfl hchiDc h.omega_pos hdensity)
  have hlandingM := eventuallyShellLanding p h.omega_pos hdelta1 hdescent
  have hclockM := eventuallyShellClockLt6953 p h.r_lt_clock h.omega_pos
  have hceilingM := eventuallyShellOrbitCeiling p h.omega_pos hetaBeta
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageOrbit p (stageCount h.omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageClock p (stageCount h.omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  have hceiling := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      ∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) hceilingM
  refine ⟨S, hSdense, ?_⟩
  filter_upwards [hlanding, hclock, hceiling,
    eventually_gt_atTop (0 : ℕ)] with n hnlanding hnclock hnceiling hnpos hnS
  have hnboot : n ∈ bootstrapSet p
      (stageCount h.omega (Nat.log 2 n)) := by
    exact hnS
  let k := stageClock p (stageCount h.omega (Nat.log 2 n)) n
  refine ⟨k, hnclock hnpos hnboot, ?_, hnceiling hnpos hnboot⟩
  rw [← stageOrbit_eq_orbit_stageClock]
  exact hnlanding hnpos hnboot

end

end FirstPassageLinearTransport
