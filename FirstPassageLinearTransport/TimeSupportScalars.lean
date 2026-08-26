/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import FirstPassageLinearTransport.ShrinkingSchedules

/-!
# Shared feasible-time scalar constants

This module contains only the scalar constant shared by the canonical timeout
assembly and the optional all-prefix moving route.  Keeping it separate avoids
pulling the latter route's time-support theorems into the canonical `Main`
dependency cone.
-/

namespace FirstPassageLinearTransport

open scoped Real

noncomputable section

/-- Explicit constant used in the eventual moving and timeout feasible-time
support estimates. -/
def movingTimeSupportConstant
    (P : ShrinkingBarrierRunData) (C : ℝ) : ℝ :=
  2 + 2 / driftGap *
    ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
      (C + 5) ^ 2)

end

end FirstPassageLinearTransport
