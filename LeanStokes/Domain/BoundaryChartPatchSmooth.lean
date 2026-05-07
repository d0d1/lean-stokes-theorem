/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatchCoordDomain

/-!
# Boundary Chart Patch Smoothness

This module records pointwise smoothness of patch-local boundary
parametrizations on their certified coordinate domains.  The statements are
local smoothness facts for chart infrastructure; they do not assert chart-local
Stokes, change of variables, localization, or global domain Stokes.
-/

noncomputable section

namespace SmoothDomain
namespace BoundaryChartPatch

variable {n : ℕ} {M : SmoothDomain (n + 1)} {x : ℝSpace (n + 1)}

/-- The local boundary parametrization of a determinant-sign-stable patch is smooth at every
coordinate whose parametrized point lies in the certified patch neighborhood. -/
theorem contDiffAt_boundaryChartParam (P : BoundaryChartPatch M x)
    {y : ℝSpace n} (hy : y ∈ P.localCoordDomain) :
    ContDiffAt ℝ ⊤ (boundaryChartParam M P.i x P.h) y := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  let z : ℝSpace (n + 1) := halfSpaceBoundaryParam n y
  let p : ℝSpace (n + 1) := boundaryChartParam M P.i x P.h y
  have hz : z ∈ e.target := by
    simpa [z, e] using hy.1
  have hp : p ∈ P.U := by
    simpa [p] using hy.2
  let L : ℝSpace (n + 1) ≃L[ℝ] ℝSpace (n + 1) :=
    (fderiv ℝ (M.halfSpaceFlatteningMap P.i) p).toContinuousLinearEquivOfDetNeZero
      (P.det_ne_zero hp)
  have hp_eq : p = e.symm z := by
    simp [p, z, e, boundaryChartParam]
  have hderiv0 : HasFDerivAt (M.halfSpaceFlatteningMap P.i)
      (fderiv ℝ (M.halfSpaceFlatteningMap P.i) p) p := by
    rw [M.fderiv_halfSpaceFlatteningMap P.i p]
    exact M.hasFDerivAt_halfSpaceFlatteningMap P.i p
  have hderiv : HasFDerivAt e (L : ℝSpace (n + 1) →L[ℝ] ℝSpace (n + 1)) (e.symm z) := by
    rw [← hp_eq]
    simpa [e, L] using hderiv0
  have hsmooth : ContDiffAt ℝ ⊤ e (e.symm z) := by
    simpa [e] using (M.contDiff_halfSpaceFlatteningMap P.i).contDiffAt
  have hsymm : ContDiffAt ℝ ⊤ e.symm z :=
    e.contDiffAt_symm hz hderiv hsmooth
  have hparam : ContDiffAt ℝ ⊤
      (halfSpaceBoundaryParam n : ℝSpace n → ℝSpace (n + 1)) y :=
    (halfSpaceBoundaryParam n).contDiff.contDiffAt
  simpa [boundaryChartParam, e] using hsymm.comp y hparam

end BoundaryChartPatch
end SmoothDomain

end
