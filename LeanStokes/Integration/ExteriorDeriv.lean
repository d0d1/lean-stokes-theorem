/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.ExteriorDeriv
import LeanStokes.Integration.FormIntegral

/-!
# Integration Congruence for Exterior Derivatives

This module contains integration-level consequences of local congruence for
exterior derivatives.  It is kept in the integration layer so the differential
form layer does not depend on form integration.
-/

noncomputable section

open Topology Filter Set MeasureTheory
open scoped Topology

namespace DiffForm

variable {n : ℕ}

/-- Integrals of exterior derivatives agree when the original forms agree in a neighborhood of
every point of the measurable integration set. -/
theorem integral_extd_congr_of_eventuallyEq_on
    (ω₁ ω₂ : DiffForm (n + 1) n) {S : Set (ℝSpace (n + 1))}
    (hS : MeasurableSet S) (h : ∀ x ∈ S, ω₁ =ᶠ[𝓝 x] ω₂) :
    integral (extd ω₁) S = integral (extd ω₂) S :=
  integral_congr (extd ω₁) (extd ω₂) hS
    (extd_congr_on_of_eventuallyEq h)

end DiffForm

end
