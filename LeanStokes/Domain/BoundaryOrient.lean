/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.HalfSpace
import LeanStokes.Domain.SmoothDomain
import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.StdBasis

/-!
# Boundary Orientation

Foundational orientation conventions for regular sublevel domains.

This file records the ambient standard orientation, the outward conormal
`dφ`, the tangent hyperplane `ker dφ`, and the full ambient frame used in the
first-coordinate half-space model.  Boundary integration and chart-transition
orientation are built in later modules.
-/

noncomputable section

open Topology Filter Set

namespace SmoothDomain

variable {d : ℕ} (M : SmoothDomain d)

/-- The standard basis of the ambient Euclidean coordinate space. -/
def ambientBasis (d : ℕ) : Module.Basis (Fin d) ℝ (ℝSpace d) :=
  Pi.basisFun ℝ (Fin d)

/-- The ambient standard orientation induced by `Pi.basisFun`. -/
def ambientOrientation (d : ℕ) : Orientation ℝ (ℝSpace d) (Fin d) :=
  (ambientBasis d).orientation

/-- The outward conormal covector `dφ`.

For `M = {x | φ x ≤ 0}`, this covector points outward in the conormal sense. -/
def outwardConormal (x : ℝSpace d) : ℝSpace d →L[ℝ] ℝ :=
  fderiv ℝ M.φ x

/-- The tangent hyperplane to the boundary model at `x`, defined as `ker dφ`. -/
def boundaryTangentSpace (x : ℝSpace d) : Submodule ℝ (ℝSpace d) :=
  LinearMap.ker (M.outwardConormal x : ℝSpace d →ₗ[ℝ] ℝ)

theorem mem_boundaryTangentSpace_iff (x v : ℝSpace d) :
    v ∈ M.boundaryTangentSpace x ↔ M.outwardConormal x v = 0 :=
  Iff.rfl

/-- Regularity says the outward conormal is nonzero at boundary points. -/
theorem outwardConormal_ne_zero_at_boundary {x : ℝSpace d} (hx : x ∈ M.boundary) :
    M.outwardConormal x ≠ 0 :=
  M.regular x hx

/-- The full ambient frame `(-e₀, e₁, …)` used for the upper half-space model `{x₀ ≥ 0}`.

This is an ambient frame, not the boundary orientation itself.  It records the
outward-normal-first convention in the local model: for the upper half-space,
the outward normal is `-e₀`. -/
def halfSpaceOutwardFirstBasis [NeZero d] : Module.Basis (Fin d) ℝ (ℝSpace d) :=
  (ambientBasis d).unitsSMul (Function.update 1 (0 : Fin d) (-1))

@[simp] theorem halfSpaceOutwardFirstBasis_zero [NeZero d] :
    halfSpaceOutwardFirstBasis (d := d) (0 : Fin d) = -Pi.single (0 : Fin d) (1 : ℝ) := by
  rw [halfSpaceOutwardFirstBasis, Module.Basis.unitsSMul_apply]
  simp [ambientBasis]

@[simp] theorem halfSpaceOutwardFirstBasis_ne_zero [NeZero d] {j : Fin d} (hj : j ≠ 0) :
    halfSpaceOutwardFirstBasis (d := d) j = Pi.single j (1 : ℝ) := by
  rw [halfSpaceOutwardFirstBasis, Module.Basis.unitsSMul_apply]
  rw [Function.update_of_ne hj]
  simp [ambientBasis]

/-- The full ambient frame `(-e₀, e₁, …)` has the opposite orientation from the standard frame. -/
theorem halfSpaceOutwardFirstBasis_orientation [NeZero d] :
    (halfSpaceOutwardFirstBasis (d := d)).orientation = -ambientOrientation d := by
  simp [halfSpaceOutwardFirstBasis, ambientOrientation, ambientBasis]

end SmoothDomain

end
