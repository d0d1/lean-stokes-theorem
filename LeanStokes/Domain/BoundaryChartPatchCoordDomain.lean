/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChart
import LeanStokes.Domain.BoundaryChartPatch

/-!
# Boundary Chart Patch Coordinate Domains

This module contains the coordinate-domain API for determinant-sign-stable
boundary chart patches.  It is deliberately below both patch-local boundary
integrals and patch smoothness, so those layers can share the same coordinate
domain without creating an integration dependency.
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

end BoundaryChartPatch
end SmoothDomain

end
