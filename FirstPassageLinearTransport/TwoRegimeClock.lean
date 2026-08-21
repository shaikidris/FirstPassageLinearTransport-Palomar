/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.TwoRegimeRun

/-!
# Two-regime geometric clock

The potential below pays the remaining high-rank geometric series and, once
needed, the complete low-rank geometric series.  Its one-step decrease gives
the exact clock bound from the manuscript without counting stages.
-/

namespace FirstPassageLinearTransport

noncomputable section

/-- Remaining clock potential at rank `q`. -/
def twoRegimeClockPotential (rHi rLo : ℝ) (S q : ℕ) : ℝ :=
  if S ≤ q then
    (q : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo)
  else
    (q : ℝ) / (1 - rLo)

theorem twoRegimeClockPotential_nonneg
    {rHi rLo : ℝ} (hrHi : rHi < 1) (hrLo : rLo < 1)
    (S q : ℕ) :
    0 ≤ twoRegimeClockPotential rHi rLo S q := by
  have hdHi : 0 < 1 - rHi := sub_pos.mpr hrHi
  have hdLo : 0 < 1 - rLo := sub_pos.mpr hrLo
  unfold twoRegimeClockPotential
  split_ifs
  · exact add_nonneg
      (div_nonneg (Nat.cast_nonneg q) hdHi.le)
      (div_nonneg (Nat.cast_nonneg S) hdLo.le)
  · exact div_nonneg (Nat.cast_nonneg q) hdLo.le

/-- One rank step decreases the clock potential by at least the local time.
The active contraction is selected by the parent rank `m`. -/
theorem twoRegimeClockPotential_step
    {rHi rLo : ℝ} {S qPrev m h q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (hmPrev : m ≤ qPrev) (hhm : h ≤ m)
    (hcontract :
      if S ≤ m then (q : ℝ) ≤ rHi * (m : ℝ)
      else (q : ℝ) ≤ rLo * (m : ℝ)) :
    (h : ℝ) + twoRegimeClockPotential rHi rLo S q ≤
      twoRegimeClockPotential rHi rLo S qPrev := by
  have hdHi : 0 < 1 - rHi := sub_pos.mpr hrHi1
  have hdLo : 0 < 1 - rLo := sub_pos.mpr hrLo1
  have hhmR : (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhm
  have hmPrevR : (m : ℝ) ≤ (qPrev : ℝ) := by exact_mod_cast hmPrev
  by_cases hqHigh : S ≤ q
  · have hmHigh : S ≤ m := by
      by_contra hmHigh
      have hactive : (q : ℝ) ≤ rLo * (m : ℝ) := by
        simpa [hmHigh] using hcontract
      have hrmul : rLo * (m : ℝ) ≤ (m : ℝ) := by
        nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
      have hqm : q ≤ m := by exact_mod_cast hactive.trans hrmul
      omega
    have hactive : (q : ℝ) ≤ rHi * (m : ℝ) := by
      simpa [hmHigh] using hcontract
    have hrmul : rHi * (m : ℝ) ≤ (m : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
    have hqm : q ≤ m := by exact_mod_cast hactive.trans hrmul
    have hprevHigh : S ≤ qPrev := hqHigh.trans (hqm.trans hmPrev)
    unfold twoRegimeClockPotential
    rw [if_pos hqHigh, if_pos hprevHigh]
    have hlocal : (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
        (m : ℝ) / (1 - rHi) := by
      calc
        (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
            (m : ℝ) + (rHi * (m : ℝ)) / (1 - rHi) :=
          add_le_add hhmR ((div_le_div_iff_of_pos_right hdHi).2 hactive)
        _ = (m : ℝ) / (1 - rHi) := by
          field_simp [hdHi.ne']
          ring
    have hmono : (m : ℝ) / (1 - rHi) ≤
        (qPrev : ℝ) / (1 - rHi) :=
      (div_le_div_iff_of_pos_right hdHi).2 hmPrevR
    linarith
  · have hqLow : q < S := Nat.lt_of_not_ge hqHigh
    by_cases hprevHigh : S ≤ qPrev
    · unfold twoRegimeClockPotential
      rw [if_neg hqHigh, if_pos hprevHigh]
      have htime : (h : ℝ) ≤ (qPrev : ℝ) / (1 - rHi) := by
        have hmq : (m : ℝ) ≤ (qPrev : ℝ) := hmPrevR
        have hqdiv : (qPrev : ℝ) ≤ (qPrev : ℝ) / (1 - rHi) := by
          apply (le_div_iff₀ hdHi).2
          nlinarith [show (0 : ℝ) ≤ (qPrev : ℝ) from Nat.cast_nonneg qPrev]
        exact hhmR.trans (hmq.trans hqdiv)
      have hqS : (q : ℝ) / (1 - rLo) ≤
          (S : ℝ) / (1 - rLo) :=
        (div_le_div_iff_of_pos_right hdLo).2 (by exact_mod_cast hqLow.le)
      linarith
    · have hprevLow : qPrev < S := Nat.lt_of_not_ge hprevHigh
      have hmLow : ¬ S ≤ m := by omega
      have hactive : (q : ℝ) ≤ rLo * (m : ℝ) := by
        simpa [hmLow] using hcontract
      unfold twoRegimeClockPotential
      rw [if_neg hqHigh, if_neg hprevHigh]
      have hlocal : (h : ℝ) + (q : ℝ) / (1 - rLo) ≤
          (m : ℝ) / (1 - rLo) := by
        calc
          (h : ℝ) + (q : ℝ) / (1 - rLo) ≤
              (m : ℝ) + (rLo * (m : ℝ)) / (1 - rLo) :=
            add_le_add hhmR ((div_le_div_iff_of_pos_right hdLo).2 hactive)
          _ = (m : ℝ) / (1 - rLo) := by
            field_simp [hdLo.ne']
            ring
      have hmono : (m : ℝ) / (1 - rLo) ≤
          (qPrev : ℝ) / (1 - rLo) :=
        (div_le_div_iff_of_pos_right hdLo).2 hmPrevR
      exact hlocal.trans hmono

/-- Rank/time data of a two-regime stopped path. -/
inductive TwoRegimeRankTrace
    (rHi rLo : ℝ) (S M : ℕ) : ℕ → ℕ → Prop
  | first {h q : ℕ}
      (hhM : h ≤ M)
      (hq : (q : ℝ) ≤ rHi * (M : ℝ)) :
      TwoRegimeRankTrace rHi rLo S M h q
  | next {elapsed qPrev m h q : ℕ}
      (htrace : TwoRegimeRankTrace rHi rLo S M elapsed qPrev)
      (hmPrev : m ≤ qPrev) (hhm : h ≤ m)
      (hq : if S ≤ m then (q : ℝ) ≤ rHi * (m : ℝ)
        else (q : ℝ) ≤ rLo * (m : ℝ)) :
      TwoRegimeRankTrace rHi rLo S M (elapsed + h) q

/-- Potential invariant for the complete two-regime trace. -/
theorem TwoRegimeRankTrace.elapsed_add_potential_le
    {rHi rLo : ℝ} {S M elapsed q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (htrace : TwoRegimeRankTrace rHi rLo S M elapsed q) :
    (elapsed : ℝ) + twoRegimeClockPotential rHi rLo S q ≤
      (M : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo) := by
  induction htrace with
  | @first h q hhM hq =>
      have hdHi : 0 < 1 - rHi := sub_pos.mpr hrHi1
      have hdLo : 0 < 1 - rLo := sub_pos.mpr hrLo1
      have hhMR : (h : ℝ) ≤ (M : ℝ) := by exact_mod_cast hhM
      by_cases hqHigh : S ≤ q
      · unfold twoRegimeClockPotential
        rw [if_pos hqHigh]
        have hlocal : (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
            (M : ℝ) / (1 - rHi) := by
          calc
            (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
                (M : ℝ) + (rHi * (M : ℝ)) / (1 - rHi) :=
              add_le_add hhMR ((div_le_div_iff_of_pos_right hdHi).2 hq)
            _ = (M : ℝ) / (1 - rHi) := by
              field_simp [hdHi.ne']
              ring
        linarith
      · unfold twoRegimeClockPotential
        rw [if_neg hqHigh]
        have htime : (h : ℝ) ≤ (M : ℝ) / (1 - rHi) := by
          have hMdiv : (M : ℝ) ≤ (M : ℝ) / (1 - rHi) := by
            apply (le_div_iff₀ hdHi).2
            nlinarith [show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M]
          exact hhMR.trans hMdiv
        have hqS : (q : ℝ) / (1 - rLo) ≤
            (S : ℝ) / (1 - rLo) :=
          (div_le_div_iff_of_pos_right hdLo).2 (by
            exact_mod_cast (Nat.lt_of_not_ge hqHigh).le)
        linarith
  | @next elapsed qPrev m h q htrace hmPrev hhm hq ih =>
      have hstep := twoRegimeClockPotential_step
        hrHi0 hrHi1 hrLo1 hmPrev hhm hq
      push_cast
      linarith

/-- The complete two-regime shortcut time is bounded by the two geometric
rank budgets. -/
theorem TwoRegimeRankTrace.elapsed_le
    {rHi rLo : ℝ} {S M elapsed q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (htrace : TwoRegimeRankTrace rHi rLo S M elapsed q) :
    (elapsed : ℝ) ≤
      (M : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo) := by
  have hmain := htrace.elapsed_add_potential_le
    hrHi0 hrHi1 hrLo1
  have hpot := twoRegimeClockPotential_nonneg hrHi1 hrLo1 S q
  linarith

/-- Canonical natural-number clock for the complete two-regime run.  The
ceiling is taken only after the high- and low-rank geometric budgets have
been added. -/
noncomputable def twoRegimeHorizon
    (rHi rLo : ℚ) (S M : ℕ) : ℕ :=
  ⌈((M : ℝ) / (1 - (rHi : ℝ)) +
      (S : ℝ) / (1 - (rLo : ℝ)))⌉₊

/-- The real geometric budget lies below its canonical natural ceiling. -/
theorem twoRegimeHorizon_lower
    (rHi rLo : ℚ) (S M : ℕ) :
    (M : ℝ) / (1 - (rHi : ℝ)) +
        (S : ℝ) / (1 - (rLo : ℝ)) ≤
      (twoRegimeHorizon rHi rLo S M : ℝ) := by
  exact Nat.le_ceil _

end

end FirstPassageLinearTransport
