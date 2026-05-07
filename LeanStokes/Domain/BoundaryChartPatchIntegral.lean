/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartIntegral
import LeanStokes.Domain.BoundaryChartPatch

/-!
# Boundary Chart Patch Integrals

This module specializes determinant-sign-stable boundary chart patches to the
codimension-one boundary coordinate model.  Its local coordinate domain is tied
to the patch neighborhood `P.U`, so the stored Jacobian sign branch is only used
where it is certified.

It does not define a chart-independent boundary integral, chart-transition
compatibility, a global finite cover, or a Stokes theorem.
-/

noncomputable section

namespace SmoothDomain
namespace BoundaryChartPatch

variable {n : ℕ} {M : SmoothDomain (n + 1)} {x : ℝSpace (n + 1)}

/-- Patch-local boundary coordinate domain: chart-valid coordinates whose parametrized boundary
points land in the determinant-sign-stable ambient patch neighborhood. -/
def localCoordDomain (P : BoundaryChartPatch M x) : Set (ℝSpace n) :=
  { y | y ∈ boundaryChartCoordDomain M P.i x P.h ∧
      boundaryChartParam M P.i x P.h y ∈ P.U }

/-- The patch-local coordinate domain is contained in the full chart coordinate domain. -/
theorem localCoordDomain_subset_coordDomain (P : BoundaryChartPatch M x) :
    P.localCoordDomain ⊆ boundaryChartCoordDomain M P.i x P.h := by
  intro y hy
  exact hy.1

/-- Coordinates in the patch-local coordinate domain parametrize boundary points inside `P.U`. -/
theorem boundaryChartParam_mem_U_of_mem_localCoordDomain (P : BoundaryChartPatch M x)
    {y : ℝSpace n} (hy : y ∈ P.localCoordDomain) :
    boundaryChartParam M P.i x P.h y ∈ P.U :=
  hy.2

/-- Coordinates in the patch-local coordinate domain parametrize points on `M.boundary`. -/
theorem boundaryChartParam_mem_boundary_of_mem_localCoordDomain (P : BoundaryChartPatch M x)
    {y : ℝSpace n} (hy : y ∈ P.localCoordDomain) :
    boundaryChartParam M P.i x P.h y ∈ M.boundary :=
  boundaryChartParam_mem_boundary M P.i x P.h (P.localCoordDomain_subset_coordDomain hy)

/-- Coordinate of the patch center in the local boundary chart. -/
def centerCoord (P : BoundaryChartPatch M x) : ℝSpace n :=
  halfSpaceBoundaryCoord n (M.halfSpaceFlatteningMap P.i x)

/-- The patch center coordinate belongs to the patch-local coordinate domain. -/
theorem centerCoord_mem_localCoordDomain (P : BoundaryChartPatch M x) :
    P.centerCoord ∈ P.localCoordDomain := by
  refine ⟨?_, ?_⟩
  · simpa [centerCoord] using
      halfSpaceBoundaryCoord_mem_boundaryChartCoordDomain_at_center
        M P.i x P.h P.center_mem_boundary
  · change boundaryChartParam M P.i x P.h
        (halfSpaceBoundaryCoord n (M.halfSpaceFlatteningMap P.i x)) ∈ P.U
    rw [boundaryChartParam_halfSpaceBoundaryCoord_at_center M P.i x P.h
      P.center_mem_boundary]
    exact P.center_mem_U

/-- The local boundary chart maps the patch center coordinate back to the patch center. -/
theorem boundaryChartParam_centerCoord (P : BoundaryChartPatch M x) :
    boundaryChartParam M P.i x P.h P.centerCoord = x := by
  simpa [centerCoord] using
    boundaryChartParam_halfSpaceBoundaryCoord_at_center M P.i x P.h P.center_mem_boundary

/-- Patch-local signed boundary integral over a coordinate set certified to lie in
`P.localCoordDomain`. -/
def localBoundaryIntegral (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    (S : Set (ℝSpace n)) (_hS : S ⊆ P.localCoordDomain) : ℝ :=
  boundaryChartIntegralWithSign P.sign M P.i x P.h ω S

/-- Scalar multiplication factors out of a patch-local signed boundary integral. -/
theorem localBoundaryIntegral_smul (P : BoundaryChartPatch M x) (c : ℝ)
    (ω : DiffForm (n + 1) n) (S : Set (ℝSpace n)) (hS : S ⊆ P.localCoordDomain) :
    P.localBoundaryIntegral (c • ω) S hS =
      c * P.localBoundaryIntegral ω S hS := by
  simpa [localBoundaryIntegral] using
    boundaryChartIntegralWithSign_smul P.sign M P.i x P.h c ω S

/-- Positive ambient Jacobian branch: the patch-local boundary sign is `-1`. -/
theorem localBoundaryIntegral_eq_neg_integral_of_sign_pos (P : BoundaryChartPatch M x)
    (hpos : P.sign = JacobianSign.pos) (ω : DiffForm (n + 1) n)
    (S : Set (ℝSpace n)) (hS : S ⊆ P.localCoordDomain) :
    P.localBoundaryIntegral ω S hS =
      -DiffForm.integral (boundaryChartPullback M P.i x P.h ω) S := by
  simp [localBoundaryIntegral, hpos]

/-- Negative ambient Jacobian branch: the induced boundary sign is reversed to `+1`. -/
theorem localBoundaryIntegral_eq_integral_of_sign_neg (P : BoundaryChartPatch M x)
    (hneg : P.sign = JacobianSign.neg) (ω : DiffForm (n + 1) n)
    (S : Set (ℝSpace n)) (hS : S ⊆ P.localCoordDomain) :
    P.localBoundaryIntegral ω S hS =
      DiffForm.integral (boundaryChartPullback M P.i x P.h ω) S := by
  simp [localBoundaryIntegral, hneg]

end BoundaryChartPatch
end SmoothDomain

end
