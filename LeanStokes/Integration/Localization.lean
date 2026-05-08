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

/-- If the scalar factor is locally zero at a point, then the exterior derivative of the localized
form is zero there.  This uses locality of `d`, not a product rule. -/
theorem extd_fsmul_eq_zero_of_left_eventuallyEq_zero {d k : ℕ}
    {f : ℝSpace d → ℝ} {ω : DiffForm d k} {x : ℝSpace d}
    (hf : f =ᶠ[𝓝 x] fun _ => 0) :
    extd (fsmul f ω) x = 0 := by
  have hform : fsmul f ω =ᶠ[𝓝 x] (0 : DiffForm d k) :=
    fsmul_eventuallyEq_zero_of_left_eventuallyEq_zero hf
  simpa using extd_congr_of_eventuallyEq hform

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

/-- The integral of the exterior derivative of a finite sum of localized forms is the finite sum of
the integrals of the exterior derivatives of the localized forms.  This is only finite linearity of
`d`; it does not expand `d(f • ω)`. -/
theorem integral_extd_finset_sum_fsmul_eq_finset_sum_integral_extd_fsmul
    {ι : Type*} (s : Finset ι) (f : ι → ℝSpace (n + 1) → ℝ)
    (ω : DiffForm (n + 1) n) {S : Set (ℝSpace (n + 1))}
    (hS : MeasurableSet S)
    (hdiff : ∀ i ∈ s, Differentiable ℝ (fsmul (f i) ω))
    (hint : ∀ i ∈ s,
      IntegrableOn (topCoeff (extd (fsmul (f i) ω))) S volume) :
    integral (extd (∑ i ∈ s, fsmul (f i) ω)) S =
      ∑ i ∈ s, integral (extd (fsmul (f i) ω)) S := by
  have hcongr :
      integral (extd (∑ i ∈ s, fsmul (f i) ω)) S =
        integral (∑ i ∈ s, extd (fsmul (f i) ω)) S := by
    exact integral_congr
      (extd (∑ i ∈ s, fsmul (f i) ω))
      (∑ i ∈ s, extd (fsmul (f i) ω)) hS
      (fun x _ => by
        simpa using
          extd_finset_sum (x := x) s (fun i => fsmul (f i) ω)
            (fun i hi => hdiff i hi x))
  rw [hcongr]
  exact integral_finset_sum s (fun i => extd (fsmul (f i) ω)) S hint

/-- If scalar weights form a local partition of unity on `S`, then the finite sum of the localized
exterior-derivative integrals equals the integral of `dω` on `S`.  This combines finite linearity of
`d` with neighborhood equality of `Σᵢ fᵢ • ω` and `ω`; it does not use a product rule. -/
theorem finset_sum_integral_extd_fsmul_eq_integral_extd_of_sum_eventuallyEq_one
    {ι : Type*} (s : Finset ι) (f : ι → ℝSpace (n + 1) → ℝ)
    (ω : DiffForm (n + 1) n) {S : Set (ℝSpace (n + 1))}
    (hS : MeasurableSet S)
    (hdiff : ∀ i ∈ s, Differentiable ℝ (fsmul (f i) ω))
    (hint : ∀ i ∈ s,
      IntegrableOn (topCoeff (extd (fsmul (f i) ω))) S volume)
    (h : ∀ x ∈ S, (fun y => ∑ i ∈ s, f i y) =ᶠ[𝓝 x] fun _ => 1) :
    (∑ i ∈ s, integral (extd (fsmul (f i) ω)) S) = integral (extd ω) S := by
  rw [← integral_extd_finset_sum_fsmul_eq_finset_sum_integral_extd_fsmul
    s f ω hS hdiff hint]
  exact integral_extd_finset_sum_fsmul_eq_integral_extd_of_sum_eventuallyEq_one s f ω hS h

/-- Restrict the integral of `d(f • ω)` from `S` to `U` when `U ⊆ S` and the scalar factor is
locally zero at every point of `S \ U`.  This is the support restriction needed for localized
Stokes assembly and does not expand `d(f • ω)`. -/
theorem integral_extd_fsmul_eq_integral_extd_fsmul_of_subset_of_left_eventuallyEq_zero_off
    (f : ℝSpace (n + 1) → ℝ) (ω : DiffForm (n + 1) n)
    {S U : Set (ℝSpace (n + 1))}
    (hS : MeasurableSet S) (hU : MeasurableSet U) (hsub : U ⊆ S)
    (hoff : ∀ x ∈ S, x ∉ U → f =ᶠ[𝓝 x] fun _ => 0) :
    integral (extd (fsmul f ω)) S = integral (extd (fsmul f ω)) U :=
  integral_eq_integral_of_subset_of_eq_zero_on_diff (extd (fsmul f ω)) hS hU hsub
    (fun x hxS hxU => extd_fsmul_eq_zero_of_left_eventuallyEq_zero (hoff x hxS hxU))

end DiffForm

end
