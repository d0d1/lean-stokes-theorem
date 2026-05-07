/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.SmoothDomain
import LeanStokes.Integration.FormIntegral

/-!
# Domain Integrals

This module defines ambient top-form integration over the compact carrier of a
regular sublevel domain.  It does not define boundary integration,
chart-independent manifold integration, localization, or any Stokes theorem.
-/

noncomputable section

open MeasureTheory Topology Filter Set MeasureTheory.Measure
open scoped ENNReal BigOperators

namespace SmoothDomain

variable {d : ℕ}

/-- Ambient integral of a top form over the compact carrier of a smooth regular sublevel domain. -/
def domainIntegral (M : SmoothDomain d) (η : DiffForm d d) : ℝ :=
  DiffForm.integral η M.carrier

@[simp] theorem domainIntegral_eq_integral (M : SmoothDomain d) (η : DiffForm d d) :
    M.domainIntegral η = DiffForm.integral η M.carrier :=
  rfl

/-- A continuous top coefficient on the compact carrier is integrable there. -/
theorem integrableOn_topCoeff_carrier_of_continuousOn (M : SmoothDomain d)
    {η : DiffForm d d} (hη : ContinuousOn (DiffForm.topCoeff η) M.carrier) :
    IntegrableOn (DiffForm.topCoeff η) M.carrier volume :=
  DiffForm.integrableOn_topCoeff_of_isCompact hη M.carrier_isCompact

/-- A globally continuous top coefficient is integrable on the compact carrier. -/
theorem integrableOn_topCoeff_carrier_of_continuous (M : SmoothDomain d)
    {η : DiffForm d d} (hη : Continuous (DiffForm.topCoeff η)) :
    IntegrableOn (DiffForm.topCoeff η) M.carrier volume :=
  M.integrableOn_topCoeff_carrier_of_continuousOn hη.continuousOn

/-- Domain integration is additive when both top coefficients are integrable on the carrier. -/
theorem domainIntegral_add (M : SmoothDomain d) (η₁ η₂ : DiffForm d d)
    (h₁ : IntegrableOn (DiffForm.topCoeff η₁) M.carrier volume)
    (h₂ : IntegrableOn (DiffForm.topCoeff η₂) M.carrier volume) :
    M.domainIntegral (η₁ + η₂) = M.domainIntegral η₁ + M.domainIntegral η₂ := by
  simpa [domainIntegral] using DiffForm.integral_add η₁ η₂ M.carrier h₁ h₂

/-- Constant scalar multiplication factors out of domain integration. -/
theorem domainIntegral_smul (M : SmoothDomain d) (c : ℝ) (η : DiffForm d d) :
    M.domainIntegral (c • η) = c * M.domainIntegral η := by
  simpa [domainIntegral] using DiffForm.integral_smul c η M.carrier

/-- Domain integration commutes with finite sums when every top coefficient is integrable on the
carrier. -/
theorem domainIntegral_finset_sum {ι : Type*} (M : SmoothDomain d) (s : Finset ι)
    (η : ι → DiffForm d d)
    (hη : ∀ i ∈ s, IntegrableOn (DiffForm.topCoeff (η i)) M.carrier volume) :
    M.domainIntegral (∑ i ∈ s, η i) = ∑ i ∈ s, M.domainIntegral (η i) := by
  simpa [domainIntegral] using DiffForm.integral_finset_sum s η M.carrier hη

end SmoothDomain

end
