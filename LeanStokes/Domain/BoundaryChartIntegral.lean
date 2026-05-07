/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChart
import LeanStokes.Domain.JacobianSign
import LeanStokes.Integration.FormIntegral

/-!
# Local Boundary Chart Integrals

This module records the two local orientation branches for integrating an
ambient boundary form through one boundary-flattening chart.  The branch is the
sign of the ambient Jacobian determinant of `M.halfSpaceFlatteningMap i`; it is
not an arbitrary real sign.

The definitions are local to an explicit coordinate set.  They do not define a
chart-independent boundary integral, chart-transition compatibility, or a
local/global Stokes theorem.
-/

noncomputable section

namespace SmoothDomain

variable {n : ℕ}

/-- Pullback through a local boundary chart commutes with scalar multiplication. -/
theorem boundaryChartPullback_smul (M : SmoothDomain (n + 1)) (i : Fin (n + 1))
    (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    (c : ℝ) (ω : DiffForm (n + 1) n) :
    boundaryChartPullback M i x h (c • ω) =
      c • boundaryChartPullback M i x h ω := by
  funext y
  ext v
  simp [boundaryChartPullback, DiffForm.pullback]

/-- Local boundary integral through one chart, with a discrete determinant-sign branch.

Meaningful geometric uses should take the coordinate set inside
`boundaryChartCoordDomain M i x h` and pair `σ` with a proof that the ambient
Jacobian determinant of `M.halfSpaceFlatteningMap i` has the corresponding sign
on the associated chart-source neighborhood. -/
def boundaryChartIntegralWithSign (σ : JacobianSign)
    (M : SmoothDomain (n + 1)) (i : Fin (n + 1)) (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    (ω : DiffForm (n + 1) n) (S : Set (ℝSpace n)) : ℝ :=
  σ.boundarySign * DiffForm.integral (boundaryChartPullback M i x h ω) S

/-- Positive ambient Jacobian branch: the upper-half-space boundary sign is `-1`. -/
@[simp] theorem boundaryChartIntegralWithSign_pos
    (M : SmoothDomain (n + 1)) (i : Fin (n + 1)) (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    (ω : DiffForm (n + 1) n) (S : Set (ℝSpace n)) :
    boundaryChartIntegralWithSign JacobianSign.pos M i x h ω S =
      -DiffForm.integral (boundaryChartPullback M i x h ω) S := by
  simp [boundaryChartIntegralWithSign]

/-- Negative ambient Jacobian branch: the induced boundary sign is reversed. -/
@[simp] theorem boundaryChartIntegralWithSign_neg
    (M : SmoothDomain (n + 1)) (i : Fin (n + 1)) (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    (ω : DiffForm (n + 1) n) (S : Set (ℝSpace n)) :
    boundaryChartIntegralWithSign JacobianSign.neg M i x h ω S =
      DiffForm.integral (boundaryChartPullback M i x h ω) S := by
  simp [boundaryChartIntegralWithSign]

/-- Scalar multiplication factors out of a local signed boundary chart integral. -/
theorem boundaryChartIntegralWithSign_smul (σ : JacobianSign)
    (M : SmoothDomain (n + 1)) (i : Fin (n + 1)) (x : ℝSpace (n + 1))
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0)
    (c : ℝ) (ω : DiffForm (n + 1) n) (S : Set (ℝSpace n)) :
    boundaryChartIntegralWithSign σ M i x h (c • ω) S =
      c * boundaryChartIntegralWithSign σ M i x h ω S := by
  rw [boundaryChartIntegralWithSign, boundaryChartPullback_smul, DiffForm.integral_smul,
    boundaryChartIntegralWithSign]
  ring

end SmoothDomain

end
