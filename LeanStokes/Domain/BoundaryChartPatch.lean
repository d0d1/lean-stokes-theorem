/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.ChartChangeOfVariables
import LeanStokes.Domain.JacobianSign

/-!
# Boundary Chart Patches

This module packages the local data supplied by the boundary-flattening
construction: a boundary center point, a flattening coordinate, a chart-source
neighborhood, and a stable sign for the ambient Jacobian determinant.

The package is local.  It is not a global finite cover, a partition of unity, a
chart-independent boundary integral, or a Stokes theorem.
-/

noncomputable section

namespace SmoothDomain

open Set

variable {d : ℕ}

/-- A determinant-sign-stable local boundary-flattening chart patch centered at `x`. -/
structure BoundaryChartPatch [NeZero d] (M : SmoothDomain d) (x : ℝSpace d) where
  /-- The patch center is a boundary point. -/
  center_mem_boundary : x ∈ M.boundary
  /-- Coordinate selected by regularity of the defining function. -/
  i : Fin d
  /-- The selected partial derivative is nonzero at the center. -/
  h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0
  /-- Ambient neighborhood on which the chart source and determinant sign are controlled. -/
  U : Set (ℝSpace d)
  /-- The ambient neighborhood is open. -/
  isOpen_U : IsOpen U
  /-- The patch center lies in the neighborhood. -/
  center_mem_U : x ∈ U
  /-- The neighborhood lies in the local flattening chart source. -/
  subset_source : U ⊆ (M.halfSpaceFlatteningChart i x h).source
  /-- Stable sign branch for the ambient Jacobian determinant of `M.halfSpaceFlatteningMap i`. -/
  sign : JacobianSign
  /-- If the branch is positive, the ambient Jacobian determinant is positive throughout `U`. -/
  det_pos : sign = JacobianSign.pos → ∀ y ∈ U,
    0 < LinearMap.det
      (fderiv ℝ (M.halfSpaceFlatteningMap i) y : ℝSpace d →ₗ[ℝ] ℝSpace d)
  /-- If the branch is negative, the ambient Jacobian determinant is negative throughout `U`. -/
  det_neg : sign = JacobianSign.neg → ∀ y ∈ U,
    LinearMap.det
      (fderiv ℝ (M.halfSpaceFlatteningMap i) y : ℝSpace d →ₗ[ℝ] ℝSpace d) < 0

namespace BoundaryChartPatch

variable [NeZero d] {M : SmoothDomain d} {x : ℝSpace d}

/-- The ambient neighborhood of a boundary chart patch is measurable. -/
theorem measurableSet_U (P : BoundaryChartPatch M x) : MeasurableSet P.U :=
  P.isOpen_U.measurableSet

/-- The ambient Jacobian determinant of a patch is nonzero throughout its neighborhood. -/
theorem det_ne_zero (P : BoundaryChartPatch M x) {y : ℝSpace d} (hy : y ∈ P.U) :
    LinearMap.det
      (fderiv ℝ (M.halfSpaceFlatteningMap P.i) y : ℝSpace d →ₗ[ℝ] ℝSpace d) ≠ 0 := by
  cases hsign : P.sign with
  | pos =>
      exact ne_of_gt (P.det_pos hsign y hy)
  | neg =>
      exact ne_of_lt (P.det_neg hsign y hy)

/-- Top-form change of variables through a boundary chart patch on any measurable subset of the
certified patch neighborhood. -/
theorem integral_image_eq_domainSign_mul_integral_pullback_on (P : BoundaryChartPatch M x)
    {U : Set (ℝSpace d)} (hUmeas : MeasurableSet U) (hUsub : U ⊆ P.U)
    (η : DiffForm d d) :
    DiffForm.integral η (M.halfSpaceFlatteningMap P.i '' U) =
      P.sign.domainSign *
        DiffForm.integral (DiffForm.pullback (M.halfSpaceFlatteningMap P.i) η) U := by
  cases hsign : P.sign with
  | pos =>
      simpa [JacobianSign.domainSign, hsign] using
        M.integral_image_halfSpaceFlatteningMap_eq_integral_pullback_of_det_pos
          P.i x P.h η hUmeas (fun y hy => P.subset_source (hUsub hy))
          (fun y hy => P.det_pos hsign y (hUsub hy))
  | neg =>
      simpa [JacobianSign.domainSign, hsign] using
        M.integral_image_halfSpaceFlatteningMap_eq_neg_integral_pullback_of_det_neg
          P.i x P.h η hUmeas (fun y hy => P.subset_source (hUsub hy))
          (fun y hy => P.det_neg hsign y (hUsub hy))

/-- Top-form change of variables through a boundary chart patch, with the sign supplied by
the patch's determinant branch. -/
theorem integral_image_eq_domainSign_mul_integral_pullback (P : BoundaryChartPatch M x)
    (η : DiffForm d d) :
    DiffForm.integral η (M.halfSpaceFlatteningMap P.i '' P.U) =
      P.sign.domainSign *
        DiffForm.integral (DiffForm.pullback (M.halfSpaceFlatteningMap P.i) η) P.U :=
  P.integral_image_eq_domainSign_mul_integral_pullback_on P.measurableSet_U
    (fun _ hy => hy) η

end BoundaryChartPatch

/-- Every boundary point admits a determinant-sign-stable boundary chart patch. -/
theorem exists_boundaryChartPatch_at_boundary [NeZero d] (M : SmoothDomain d)
    {x : ℝSpace d} (hx : x ∈ M.boundary) :
    Nonempty (BoundaryChartPatch M x) := by
  rcases M.exists_halfSpaceFlatteningChart_det_sign_neighborhood_at_boundary hx with
    ⟨i, h, U, hUo, hxU, hUsrc, hsign⟩
  rcases hsign with hpos | hneg
  · exact ⟨{
      center_mem_boundary := hx
      i := i
      h := h
      U := U
      isOpen_U := hUo
      center_mem_U := hxU
      subset_source := hUsrc
      sign := JacobianSign.pos
      det_pos := fun _ => hpos
      det_neg := by
        intro hbad
        cases hbad }⟩
  · exact ⟨{
      center_mem_boundary := hx
      i := i
      h := h
      U := U
      isOpen_U := hUo
      center_mem_U := hxU
      subset_source := hUsrc
      sign := JacobianSign.neg
      det_pos := by
        intro hbad
        cases hbad
      det_neg := fun _ => hneg }⟩

end SmoothDomain

end
