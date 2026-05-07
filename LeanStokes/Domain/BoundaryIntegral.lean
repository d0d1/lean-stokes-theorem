/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryOrient
import LeanStokes.DiffForm.Localization
import LeanStokes.DiffForm.Pullback
import LeanStokes.Integration.OrientedIntegral

/-!
# Boundary Integral Model

This module defines only the standard first-coordinate half-space boundary
model.  It records the integral sign convention used as the target model for
later boundary charts; it does not define chart-independent integration over an
arbitrary regular sublevel-domain boundary.
-/

noncomputable section

open MeasureTheory Topology Filter Set
open scoped BigOperators

namespace SmoothDomain

/-- Pull back an ambient `n`-form on `ℝ^(n+1)` to the standard boundary face
`{x₀ = 0}` of the half-space model. -/
def halfSpaceBoundaryPullback (n : ℕ) (ω : DiffForm (n + 1) n) : DiffForm n n :=
  DiffForm.pullback (halfSpaceBoundaryParam n) ω

/-- Pulling a pulled-back form to the model boundary is the same as pulling back along the
composite boundary parametrization. -/
theorem halfSpaceBoundaryPullback_pullback {m : ℕ}
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    (hf : Differentiable ℝ f) :
    halfSpaceBoundaryPullback n (DiffForm.pullback f ω) =
      DiffForm.pullback (f ∘ halfSpaceBoundaryParam n) ω := by
  simpa [halfSpaceBoundaryPullback] using
    DiffForm.pullback_comp f (halfSpaceBoundaryParam n) ω hf
      (halfSpaceBoundaryParam n).differentiable

/-- Pullback to the model boundary commutes with finite sums. -/
theorem halfSpaceBoundaryPullback_finset_sum {ι : Type*} (s : Finset ι)
    (ω : ι → DiffForm (n + 1) n) :
    halfSpaceBoundaryPullback n (∑ i ∈ s, ω i) =
      ∑ i ∈ s, halfSpaceBoundaryPullback n (ω i) := by
  funext y
  ext v
  simp [halfSpaceBoundaryPullback, DiffForm.pullback]

/-- Pullback to the model boundary commutes with scalar localization, with the scalar restricted
to the boundary parametrization. -/
theorem halfSpaceBoundaryPullback_fsmul
    (χ : ℝSpace (n + 1) → ℝ) (ω : DiffForm (n + 1) n) :
    halfSpaceBoundaryPullback n (DiffForm.fsmul χ ω) =
      DiffForm.fsmul (χ ∘ halfSpaceBoundaryParam n) (halfSpaceBoundaryPullback n ω) := by
  funext y
  ext v
  simp [halfSpaceBoundaryPullback, DiffForm.pullback, DiffForm.fsmul, Function.comp_def]

/-- Integral over the standard boundary face of `HalfSpace (n+1) = {x₀ ≥ 0}`.

The sign is `-1` because the outward normal is `-e₀`; hence the standard tangent
coordinate frame `(e₁, …, eₙ)` is negative relative to the induced boundary
orientation. -/
def halfSpaceBoundaryIntegral (n : ℕ) (ω : DiffForm (n + 1) n) (S : Set (ℝSpace n)) :
    ℝ :=
  DiffForm.orientedIntegral (halfSpaceBoundaryPullback n ω) S (-1)

/-- The top coefficient of the model boundary pullback is ambient evaluation on
the standard tangent frame of the boundary face. -/
theorem topCoeff_halfSpaceBoundaryPullback (n : ℕ) (ω : DiffForm (n + 1) n)
    (y : ℝSpace n) :
    DiffForm.topCoeff (halfSpaceBoundaryPullback n ω) y =
      ω (halfSpaceBoundaryParam n y) (halfSpaceBoundaryFrame n) := by
  unfold halfSpaceBoundaryPullback DiffForm.topCoeff DiffForm.pullback DiffForm.stdBasis
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  exact fderiv_halfSpaceBoundaryParam_stdBasis n y i

/-- The model boundary integral is the negative of the plain top-form integral
of the pulled-back form. -/
theorem halfSpaceBoundaryIntegral_eq_neg (n : ℕ) (ω : DiffForm (n + 1) n)
    (S : Set (ℝSpace n)) :
    halfSpaceBoundaryIntegral n ω S =
      -DiffForm.integral (halfSpaceBoundaryPullback n ω) S := by
  simp [halfSpaceBoundaryIntegral, DiffForm.orientedIntegral]

/-- Boundary integral of a pulled-back form, written as the negative plain integral of the
direct pullback along the composite boundary parametrization. -/
theorem halfSpaceBoundaryIntegral_pullback_eq_neg_integral_pullback_comp {m : ℕ}
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    (S : Set (ℝSpace n)) (hf : Differentiable ℝ f) :
    halfSpaceBoundaryIntegral n (DiffForm.pullback f ω) S =
      -DiffForm.integral (DiffForm.pullback (f ∘ halfSpaceBoundaryParam n) ω) S := by
  rw [halfSpaceBoundaryIntegral_eq_neg, halfSpaceBoundaryPullback_pullback f ω hf]

/-- Boundary integral of a pulled-back form, requiring differentiability of the outer map only at
the boundary-parametrized points of the measurable integration set. -/
theorem halfSpaceBoundaryIntegral_pullback_eq_neg_integral_pullback_comp_on {m : ℕ}
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    {S : Set (ℝSpace n)} (hS : MeasurableSet S)
    (hf : ∀ y ∈ S, DifferentiableAt ℝ f (halfSpaceBoundaryParam n y)) :
    halfSpaceBoundaryIntegral n (DiffForm.pullback f ω) S =
      -DiffForm.integral (DiffForm.pullback (f ∘ halfSpaceBoundaryParam n) ω) S := by
  rw [halfSpaceBoundaryIntegral_eq_neg]
  congr 1
  exact DiffForm.integral_congr
    (halfSpaceBoundaryPullback n (DiffForm.pullback f ω))
    (DiffForm.pullback (f ∘ halfSpaceBoundaryParam n) ω) hS
    (fun y hy =>
      DiffForm.pullback_comp_apply f (halfSpaceBoundaryParam n) ω
        (hf y hy) ((halfSpaceBoundaryParam n).differentiableAt))

/-- Pullback to the model boundary commutes with scalar multiplication. -/
theorem halfSpaceBoundaryPullback_smul (n : ℕ) (c : ℝ) (ω : DiffForm (n + 1) n) :
    halfSpaceBoundaryPullback n (c • ω) = c • halfSpaceBoundaryPullback n ω := by
  funext y
  ext v
  simp [halfSpaceBoundaryPullback, DiffForm.pullback]

/-- Scalar multiplication factors out of the model boundary integral. -/
theorem halfSpaceBoundaryIntegral_smul (n : ℕ) (c : ℝ) (ω : DiffForm (n + 1) n)
    (S : Set (ℝSpace n)) :
    halfSpaceBoundaryIntegral n (c • ω) S = c * halfSpaceBoundaryIntegral n ω S := by
  simp [halfSpaceBoundaryIntegral_eq_neg, halfSpaceBoundaryPullback_smul, DiffForm.integral_smul]

/-- Model boundary integration commutes with finite sums, assuming each pulled-back top
coefficient is integrable on the coordinate set. -/
theorem halfSpaceBoundaryIntegral_finset_sum {ι : Type*} (s : Finset ι)
    (ω : ι → DiffForm (n + 1) n) (S : Set (ℝSpace n))
    (hω : ∀ i ∈ s,
      IntegrableOn (DiffForm.topCoeff (halfSpaceBoundaryPullback n (ω i))) S volume) :
    halfSpaceBoundaryIntegral n (∑ i ∈ s, ω i) S =
      ∑ i ∈ s, halfSpaceBoundaryIntegral n (ω i) S := by
  rw [halfSpaceBoundaryIntegral_eq_neg, halfSpaceBoundaryPullback_finset_sum,
    DiffForm.integral_finset_sum s (fun i => halfSpaceBoundaryPullback n (ω i)) S hω]
  simp [halfSpaceBoundaryIntegral_eq_neg, Finset.sum_neg_distrib]

end SmoothDomain

end
