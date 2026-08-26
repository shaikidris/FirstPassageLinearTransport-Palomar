/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TimeoutFirstBad
import FirstPassageLinearTransport.MovingSharpTail

/-!
# Sharp timeout terminal profile

The timeout target has no dyadic-endpoint atom.  Its rankwise density is the
sharp entropy tail alone, and support-sensitive transport leaves exactly the
`sqrt L * exp (-b L)` terminal factor.
-/

namespace FirstPassageLinearTransport

open scoped BigOperators Real

noncomputable section

/-- Real rankwise density after timeout transport. -/
theorem timeoutFirstBadSourcesAtRank_density_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S p : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (hpM : p < M)
    (hsmall : ((((p + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget :
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤ d) :
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) * d := by
  have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hcardQ := timeoutFirstBadSourcesAtRank_card_le
    (S := S) hrStar hStarHi hStarLo hM hp hnextPos hnextLt hpM hsmall
  have hcard :
      ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) ≤
        ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
          (1 + 3 * (((p + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ p *
          ((timeoutLandingBad K₀ L p).card : ℝ) := by
    exact_mod_cast hcardQ
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hmult := rank_transport_multiplier_le hrR p
  have hTimes0 : 0 ≤
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) := by positivity
  calc
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
          (1 + 3 * (((p + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
            (2 : ℝ) ^ M / (2 : ℝ) ^ p *
          ((timeoutLandingBad K₀ L p).card : ℝ)) /
            (2 : ℝ) ^ M := div_le_div_of_nonneg_right hcard hpowM.le
    _ = ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
        (1 + 3 * (((p + 2 : ℕ) : ℝ) / (rStar : ℝ))) *
        (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) := by
      field_simp
    _ ≤ ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
        ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) *
        (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) := by
      have := hmult
      gcongr
    _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) * d := by
      have hH0 : 0 ≤ H := hTimes0.trans hTimes
      have hC : 0 ≤ 1 + 6 / (rStar : ℝ) := by positivity
      have hp0 : 0 ≤ ((p + 1 : ℕ) : ℝ) := by positivity
      have hT0 : 0 ≤
          ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p := by positivity
      calc
        ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) *
            ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) *
            (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) ≤
          H * ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) *
            (((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p) := by
          gcongr
        _ ≤ H * ((1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ)) * d := by
          gcongr
        _ = _ := by ring


/-- Canonical form of the sharp timeout sum.  It is intentionally stated
with the same series constant as the moving endpoint scalar assembly; the
unused dyadic summand only enlarges that constant. -/
theorem timeout_low_firstBad_sharp_sum_canonical_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 2 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ p ∈ Finset.Icc (L + 1) S,
      ((((p + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H C b₀ b : ℝ}
    (hTimes : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        (C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hC : 0 ≤ C) (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ∑ p ∈ Finset.Icc (L + 1) S,
        ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) *
        exactSharpCriticalLowSeriesConstant b₀ C *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
  have hterm : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * C *
          (((p + 1 : ℕ) : ℝ) /
            Real.sqrt ((p - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := by
    intro p hpI
    have hpI' := Finset.mem_Icc.mp hpI
    have hp1 : 1 ≤ p := by omega
    have hpM : p < M := hpI'.2.trans_lt hSM
    have hbase := timeoutFirstBadSourcesAtRank_density_le
      (S := S) hrStar hStarHi hStarLo hM hp1
      (hnextPos p hpI) (hnextLt p hpI) hpM (hsmall p hpI)
      (hTimes p hpI) (hTarget p hpI)
    calc
      _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) *
          ((C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := hbase
      _ = _ := by ring
  have htail := sharp_entropy_tail_exact_rate_Icc_le hb₀ hb₀b
    (show 2 ≤ L + 1 by omega) hLS
  have htail' :
      ∑ p ∈ Finset.Icc (L + 1) S,
          ((p + 1 : ℕ) : ℝ) / Real.sqrt ((p - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ))) ≤
        3 * Real.sqrt ((L : ℝ) + 1) *
          Real.exp (-(b * (((L + 1) - 1 : ℕ) : ℝ))) *
            weightedTailConstant b₀ (b₀ / 2) := by
    simpa [Nat.cast_add, Nat.cast_one] using htail
  have hconst : 3 * C * weightedTailConstant b₀ (b₀ / 2) ≤
      exactSharpCriticalLowSeriesConstant b₀ C := by
    unfold exactSharpCriticalLowSeriesConstant
    have hle := le_max_right
      (weightedTailConstant (Real.log 2) (Real.log 2 / 2))
      (3 * C * weightedTailConstant b₀ (b₀ / 2))
    linarith
  have hH0 : 0 ≤ H := by
    have hcard0 : 0 ≤
        ((timeoutFeasibleTimes P K₀ L M S (L + 1)).card : ℝ) := by positivity
    exact hcard0.trans
      (hTimes (L + 1) (Finset.mem_Icc.mpr ⟨le_rfl, hLS⟩))
  have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
  have hcoef0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) * C := by positivity
  calc
    _ ≤ ∑ p ∈ Finset.Icc (L + 1) S,
        H * (1 + 6 / (rStar : ℝ)) * C *
          (((p + 1 : ℕ) : ℝ) / Real.sqrt ((p - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) :=
      Finset.sum_le_sum hterm
    _ = H * (1 + 6 / (rStar : ℝ)) * C *
        (∑ p ∈ Finset.Icc (L + 1) S,
          ((p + 1 : ℕ) : ℝ) / Real.sqrt ((p - 1 : ℕ) : ℝ) *
            Real.exp (-(b * ((p - 1 : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ H * (1 + 6 / (rStar : ℝ)) * C *
        (3 * Real.sqrt (L + 1) *
          Real.exp (-(b * (((L + 1) - 1 : ℕ) : ℝ))) *
            weightedTailConstant b₀ (b₀ / 2)) :=
      mul_le_mul_of_nonneg_left htail' hcoef0
    _ = H * (1 + 6 / (rStar : ℝ)) *
        (3 * C * weightedTailConstant b₀ (b₀ / 2)) *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
      rw [show L + 1 - 1 = L by omega]
      ring
    _ ≤ H * (1 + 6 / (rStar : ℝ)) *
        exactSharpCriticalLowSeriesConstant b₀ C *
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
      have hfactor0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) := by positivity
      have htail0 : 0 ≤ Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ))) := by
        positivity
      gcongr
    _ = _ := by ring

end

end FirstPassageLinearTransport
