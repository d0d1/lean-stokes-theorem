/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartIntegral
import LeanStokes.Domain.BoundaryChartPatchCoordDomain

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
