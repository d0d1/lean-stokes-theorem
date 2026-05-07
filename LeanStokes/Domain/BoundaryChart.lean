/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryFlattening
import LeanStokes.Domain.BoundaryOrient
import LeanStokes.DiffForm.Pullback

/-!
# Boundary Charts

This module contains chart-local boundary parametrizations obtained by composing
the standard half-space boundary parametrization with the inverse of a local
boundary-flattening chart.  The parametrization has boundary semantics only on
its explicit coordinate domain, where the model boundary point belongs to the
chart target.

It does not define a chart-independent boundary integral or any local/global
Stokes theorem.
-/

noncomputable section

open Topology Filter Set

namespace SmoothDomain

variable {n : ℕ}

/-- Coordinate domain on which a local boundary chart is semantically valid. -/
def boundaryChartCoordDomain (M : SmoothDomain (n + 1)) (i : Fin (n + 1))
    (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) : Set (ℝSpace n) :=
  { y | halfSpaceBoundaryParam n y ∈ (M.halfSpaceFlatteningChart i x h).target }

/-- Local parametrization of the domain boundary through a half-space-flattening chart.

This is a total function because `OpenPartialHomeomorph.symm` is total, but its
boundary interpretation is only asserted on `boundaryChartCoordDomain`. -/
def boundaryChartParam (M : SmoothDomain (n + 1)) (i : Fin (n + 1))
    (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    ℝSpace n → ℝSpace (n + 1) :=
  fun y => (M.halfSpaceFlatteningChart i x h).symm (halfSpaceBoundaryParam n y)

/-- On the coordinate domain, the local boundary parametrization lands in the chart source. -/
theorem boundaryChartParam_mem_source (M : SmoothDomain (n + 1)) (i : Fin (n + 1))
    (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) {y : ℝSpace n}
    (hy : y ∈ boundaryChartCoordDomain M i x h) :
    boundaryChartParam M i x h y ∈ (M.halfSpaceFlatteningChart i x h).source := by
  simpa [boundaryChartParam, boundaryChartCoordDomain] using
    (M.halfSpaceFlatteningChart i x h).symm_mapsTo hy

/-- On the coordinate domain, the flattening chart sends the local parametrization back to the
standard model boundary point. -/
theorem halfSpaceFlatteningChart_boundaryChartParam (M : SmoothDomain (n + 1))
    (i : Fin (n + 1)) (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) {y : ℝSpace n}
    (hy : y ∈ boundaryChartCoordDomain M i x h) :
    M.halfSpaceFlatteningChart i x h (boundaryChartParam M i x h y) =
      halfSpaceBoundaryParam n y := by
  simpa [boundaryChartParam, boundaryChartCoordDomain] using
    (M.halfSpaceFlatteningChart i x h).right_inv hy

/-- On the coordinate domain, the local boundary parametrization lands in `M.boundary`. -/
theorem boundaryChartParam_mem_boundary (M : SmoothDomain (n + 1)) (i : Fin (n + 1))
    (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) {y : ℝSpace n}
    (hy : y ∈ boundaryChartCoordDomain M i x h) :
    boundaryChartParam M i x h y ∈ M.boundary := by
  rw [M.mem_boundary_iff_halfSpaceFlatteningChart_mem i x h]
  rw [halfSpaceFlatteningChart_boundaryChartParam M i x h hy]
  exact halfSpaceBoundaryParam_mem_boundary n y

/-- Raw pullback of a boundary form through a local boundary chart.

The pullback is a total differential form because `DiffForm.pullback` is total;
its boundary-chart semantics are intended only on `boundaryChartCoordDomain`. -/
def boundaryChartPullback (M : SmoothDomain (n + 1)) (i : Fin (n + 1))
    (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) (ω : DiffForm (n + 1) n) :
    DiffForm n n :=
  DiffForm.pullback (boundaryChartParam M i x h) ω

end SmoothDomain

end
