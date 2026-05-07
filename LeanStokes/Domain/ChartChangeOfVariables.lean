/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryFlattening
import LeanStokes.Integration.Pullback

/-!
# Chart Change of Variables

This module specializes same-dimensional top-form change of variables to the
first-coordinate-facing boundary-flattening charts of a regular sublevel
domain.  The statements stay local to a measurable set contained in the chart
source; they do not define chart-independent integration.
-/

noncomputable section

open Set

namespace SmoothDomain

variable {d : ℕ}

/-- The first-coordinate-facing flattening map is differentiable everywhere. -/
theorem differentiableAt_halfSpaceFlatteningMap [NeZero d] (M : SmoothDomain d)
    (i : Fin d) (y : ℝSpace d) :
    DifferentiableAt ℝ (M.halfSpaceFlatteningMap i) y :=
  (M.hasFDerivAt_halfSpaceFlatteningMap i y).differentiableAt

/-- The first-coordinate-facing flattening map is injective on every subset of
the source of its local flattening chart. -/
theorem halfSpaceFlatteningMap_injOn_of_subset_source [NeZero d]
    (M : SmoothDomain d) (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    {U : Set (ℝSpace d)}
    (hU : U ⊆ (M.halfSpaceFlatteningChart i x h).source) :
    Set.InjOn (M.halfSpaceFlatteningMap i) U := by
  intro y hy z hz hyz
  let e := M.halfSpaceFlatteningChart i x h
  have hy_src : y ∈ e.source := hU hy
  have hz_src : z ∈ e.source := hU hz
  have hyz' : e y = e z := by
    simpa [e] using hyz
  calc
    y = e.symm (e y) := (e.left_inv hy_src).symm
    _ = e.symm (e z) := by rw [hyz']
    _ = z := e.left_inv hz_src

/-- Positive-Jacobian chart-local change of variables for top forms through a
first-coordinate-facing flattening map. -/
theorem integral_image_halfSpaceFlatteningMap_eq_integral_pullback_of_det_pos [NeZero d]
    (M : SmoothDomain d) (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    {U : Set (ℝSpace d)} (η : DiffForm d d)
    (hUmeas : MeasurableSet U)
    (hUsrc : U ⊆ (M.halfSpaceFlatteningChart i x h).source)
    (hdet : ∀ y ∈ U,
      0 < LinearMap.det
        (fderiv ℝ (M.halfSpaceFlatteningMap i) y : ℝSpace d →ₗ[ℝ] ℝSpace d)) :
    DiffForm.integral η (M.halfSpaceFlatteningMap i '' U) =
      DiffForm.integral (DiffForm.pullback (M.halfSpaceFlatteningMap i) η) U :=
  DiffForm.integral_image_eq_integral_pullback_of_det_nonneg_of_differentiableAt
    η hUmeas
    (fun y _ => M.differentiableAt_halfSpaceFlatteningMap i y)
    (M.halfSpaceFlatteningMap_injOn_of_subset_source i x h hUsrc)
    (fun y hy => le_of_lt (hdet y hy))

/-- Negative-Jacobian chart-local change of variables for top forms through a
first-coordinate-facing flattening map. -/
theorem integral_image_halfSpaceFlatteningMap_eq_neg_integral_pullback_of_det_neg [NeZero d]
    (M : SmoothDomain d) (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    {U : Set (ℝSpace d)} (η : DiffForm d d)
    (hUmeas : MeasurableSet U)
    (hUsrc : U ⊆ (M.halfSpaceFlatteningChart i x h).source)
    (hdet : ∀ y ∈ U,
      LinearMap.det
        (fderiv ℝ (M.halfSpaceFlatteningMap i) y : ℝSpace d →ₗ[ℝ] ℝSpace d) < 0) :
    DiffForm.integral η (M.halfSpaceFlatteningMap i '' U) =
      -DiffForm.integral (DiffForm.pullback (M.halfSpaceFlatteningMap i) η) U :=
  DiffForm.integral_image_eq_neg_integral_pullback_of_det_nonpos_of_differentiableAt
    η hUmeas
    (fun y _ => M.differentiableAt_halfSpaceFlatteningMap i y)
    (M.halfSpaceFlatteningMap_injOn_of_subset_source i x h hUsrc)
    (fun y hy => le_of_lt (hdet y hy))

end SmoothDomain

end
