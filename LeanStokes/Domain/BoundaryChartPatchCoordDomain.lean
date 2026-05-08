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

open Set

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

/-- If a model half-space box lies in the certified inverse-chart patch, then its true boundary
tail lies in the patch-local boundary coordinate domain. -/
theorem tailBox_subset_localCoordDomain_of_model_box_subset
    (P : BoundaryChartPatch M x) (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hboxsub : Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U }) :
    Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
        (b ∘ Fin.succAbove (0 : Fin (n + 1))) ⊆ P.localCoordDomain := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  intro y hy
  let z : ℝSpace (n + 1) := halfSpaceBoundaryParam n y
  have hzbox : z ∈ Icc a b := by
    constructor
    · intro j
      cases j using Fin.cases with
      | zero =>
          simp [z, ha0]
      | succ i =>
          simpa [z, halfSpaceBoundaryParam] using hy.1 i
    · intro j
      cases j using Fin.cases with
      | zero =>
          have hle0 : a (0 : Fin (n + 1)) ≤ b (0 : Fin (n + 1)) := hle 0
          simpa [z, ha0] using hle0
      | succ i =>
          simpa [z, halfSpaceBoundaryParam] using hy.2 i
  have hzpatch := hboxsub hzbox
  refine ⟨?_, ?_⟩
  · simpa [boundaryChartCoordDomain, e, z] using hzpatch.1
  · simpa [boundaryChartParam, e, z] using hzpatch.2

/-- If a set in the certified patch has flattening image a model box, then that model box lies in
the certified inverse-chart patch. -/
theorem model_box_subset_patch_of_flattening_image_eq
    (P : BoundaryChartPatch M x) {U : Set (ℝSpace (n + 1))}
    {a b : ℝSpace (n + 1)}
    (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b) :
    Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U } := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  intro z hz
  have hzimg : z ∈ M.halfSpaceFlatteningMap P.i '' U := by
    simpa [himage] using hz
  rcases hzimg with ⟨y, hyU, rfl⟩
  have hyP : y ∈ P.U := hUsub hyU
  have hysrc : y ∈ e.source := P.subset_source hyP
  constructor
  · simpa [e] using e.map_source hysrc
  · have hleft : e.symm (e y) = y := e.left_inv hysrc
    have hleft' :
        (M.halfSpaceFlatteningChart P.i x P.h).symm
          (M.halfSpaceFlatteningMap P.i y) = y := by
      simpa [e] using hleft
    rw [hleft']
    exact hyP

/-- If a certified patch set has flattening image a model half-space box, then the true boundary
tail of that box lies in the patch-local boundary coordinate domain. -/
theorem tailBox_subset_localCoordDomain_of_flattening_image_eq
    (P : BoundaryChartPatch M x) {U : Set (ℝSpace (n + 1))}
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b) :
    Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
        (b ∘ Fin.succAbove (0 : Fin (n + 1))) ⊆ P.localCoordDomain :=
  P.tailBox_subset_localCoordDomain_of_model_box_subset a b hle ha0
    (P.model_box_subset_patch_of_flattening_image_eq hUsub himage)

end BoundaryChartPatch
end SmoothDomain

end
