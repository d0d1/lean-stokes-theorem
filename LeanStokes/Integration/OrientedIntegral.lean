/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Integration.FormIntegral

/-!
# Oriented Integration of Differential Forms

This file defines oriented integration, where the sign of the integral
depends on the choice of orientation.

## Main definitions

* `DiffForm.orientedIntegral` — integral with a sign determined by orientation
-/

noncomputable section

open MeasureTheory Topology Filter Set

namespace DiffForm

variable {d : ℕ}

/-- Oriented integration: the integral of a top-form with a sign factor.
The sign encodes orientation: +1 for the standard orientation, -1 for reversed. -/
def orientedIntegral (ω : DiffForm d d) (S : Set (ℝSpace d)) (sgn : ℝ) : ℝ :=
  sgn * integral ω S

/-- Oriented integral with positive orientation equals the plain integral. -/
theorem orientedIntegral_one (ω : DiffForm d d) (S : Set (ℝSpace d)) :
    orientedIntegral ω S 1 = integral ω S := by
  simp [orientedIntegral]

/-- Oriented integral with negative orientation negates the plain integral. -/
theorem orientedIntegral_neg_one (ω : DiffForm d d) (S : Set (ℝSpace d)) :
    orientedIntegral ω S (-1) = -(integral ω S) := by
  simp [orientedIntegral]

end DiffForm

end
