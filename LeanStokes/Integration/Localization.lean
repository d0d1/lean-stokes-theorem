/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Localization
import LeanStokes.Integration.ExteriorDeriv

/-!
# Integration of Localized Form Sums

This module records integration-level consequences of finite localization
identities.  It does not prove a product rule for exterior derivatives; it uses
neighborhood equality of the localized sum with the original form.
-/

noncomputable section

open Topology Filter Set MeasureTheory
open scoped BigOperators Topology

namespace DiffForm

variable {n : ℕ}

/-- If scalar weights sum to one in a neighborhood of every point of `S`, then the integral over
`S` of the exterior derivative of the localized finite sum agrees with the integral of `dω`. -/
theorem integral_extd_finset_sum_fsmul_eq_integral_extd_of_sum_eventuallyEq_one
    {ι : Type*} (s : Finset ι) (f : ι → ℝSpace (n + 1) → ℝ)
    (ω : DiffForm (n + 1) n) {S : Set (ℝSpace (n + 1))}
    (hS : MeasurableSet S)
    (h : ∀ x ∈ S, (fun y => ∑ i ∈ s, f i y) =ᶠ[𝓝 x] fun _ => 1) :
    integral (extd (∑ i ∈ s, fsmul (f i) ω)) S = integral (extd ω) S :=
  integral_extd_congr_of_eventuallyEq_on
    (∑ i ∈ s, fsmul (f i) ω) ω hS
    (finset_sum_fsmul_eventuallyEq_on_of_sum_eventuallyEq_one s f ω h)

end DiffForm

end
