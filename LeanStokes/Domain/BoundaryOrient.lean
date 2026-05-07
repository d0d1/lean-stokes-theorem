/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.HalfSpace
import LeanStokes.Domain.SmoothDomain
import Mathlib.Analysis.Calculus.FDeriv.Linear
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

/-- Parametrization of the boundary face `{x₀ = 0}` of `HalfSpace (n + 1)`. -/
def halfSpaceBoundaryParam (n : ℕ) : ℝSpace n →L[ℝ] ℝSpace (n + 1) :=
  ContinuousLinearMap.pi fun j => Fin.cases 0 (fun i : Fin n => ContinuousLinearMap.proj i) j

/-- Coordinate projection from the model boundary face to its tangent coordinates. -/
def halfSpaceBoundaryCoord (n : ℕ) : ℝSpace (n + 1) →L[ℝ] ℝSpace n :=
  ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj i.succ

@[simp] theorem halfSpaceBoundaryParam_apply_zero (n : ℕ) (y : ℝSpace n) :
    halfSpaceBoundaryParam n y (0 : Fin (n + 1)) = 0 := by
  simp [halfSpaceBoundaryParam]

@[simp] theorem halfSpaceBoundaryParam_apply_succ (n : ℕ) (y : ℝSpace n) (i : Fin n) :
    halfSpaceBoundaryParam n y i.succ = y i := by
  simp [halfSpaceBoundaryParam]

@[simp] theorem halfSpaceBoundaryCoord_apply (n : ℕ) (z : ℝSpace (n + 1)) (i : Fin n) :
    halfSpaceBoundaryCoord n z i = z i.succ := by
  simp [halfSpaceBoundaryCoord]

@[simp] theorem halfSpaceBoundaryCoord_halfSpaceBoundaryParam (n : ℕ) (y : ℝSpace n) :
    halfSpaceBoundaryCoord n (halfSpaceBoundaryParam n y) = y := by
  ext i
  simp

/-- On the model boundary face, boundary parametrization and coordinate projection are inverse. -/
theorem halfSpaceBoundaryParam_halfSpaceBoundaryCoord_of_mem_boundary (n : ℕ)
    {z : ℝSpace (n + 1)} (hz : z ∈ HalfSpaceBdry (n + 1)) :
    halfSpaceBoundaryParam n (halfSpaceBoundaryCoord n z) = z := by
  ext j
  cases j using Fin.cases with
  | zero =>
      have hz0 : z (0 : Fin (n + 1)) = 0 := by
        simpa [HalfSpaceBdry] using hz
      change (0 : ℝ) = z (0 : Fin (n + 1))
      exact hz0.symm
  | succ i =>
      simp

/-- The boundary parametrization lands in the boundary face. -/
theorem halfSpaceBoundaryParam_mem_boundary (n : ℕ) (y : ℝSpace n) :
    halfSpaceBoundaryParam n y ∈ HalfSpaceBdry (n + 1) := by
  simp [HalfSpaceBdry]

/-- The boundary parametrization lands in the closed half-space. -/
theorem halfSpaceBoundaryParam_mem_halfSpace (n : ℕ) (y : ℝSpace n) :
    halfSpaceBoundaryParam n y ∈ HalfSpace (n + 1) := by
  simp [HalfSpace]

/-- The standard tangent frame of the first-coordinate boundary face in ambient coordinates. -/
def halfSpaceBoundaryFrame (n : ℕ) (i : Fin n) : ℝSpace (n + 1) :=
  Pi.single i.succ (1 : ℝ)

@[simp] theorem halfSpaceBoundaryFrame_zero (n : ℕ) (i : Fin n) :
    halfSpaceBoundaryFrame n i (0 : Fin (n + 1)) = 0 := by
  simp [halfSpaceBoundaryFrame]

@[simp] theorem halfSpaceBoundaryFrame_succ (n : ℕ) (i k : Fin n) :
    halfSpaceBoundaryFrame n i k.succ = if k = i then 1 else 0 := by
  by_cases h : k = i
  · subst k
    simp [halfSpaceBoundaryFrame]
  · simp [halfSpaceBoundaryFrame, h]

@[simp] theorem halfSpaceBoundaryFrame_succ_self (n : ℕ) (i : Fin n) :
    halfSpaceBoundaryFrame n i i.succ = 1 := by
  simp

@[simp] theorem halfSpaceBoundaryFrame_succ_ne (n : ℕ) {i k : Fin n} (hki : k ≠ i) :
    halfSpaceBoundaryFrame n i k.succ = 0 := by
  simp [halfSpaceBoundaryFrame_succ, hki]

/-- The boundary tangent frame is the tail of the outward-first ambient frame. -/
theorem halfSpaceOutwardFirstBasis_succ (n : ℕ) (i : Fin n) :
    halfSpaceOutwardFirstBasis (d := n + 1) i.succ = halfSpaceBoundaryFrame n i := by
  rw [halfSpaceOutwardFirstBasis_ne_zero (j := i.succ) (Fin.succ_ne_zero i)]
  rfl

/-- The boundary parametrization has constant derivative equal to itself. -/
theorem fderiv_halfSpaceBoundaryParam (n : ℕ) (y : ℝSpace n) :
    fderiv ℝ (halfSpaceBoundaryParam n : ℝSpace n → ℝSpace (n + 1)) y =
      halfSpaceBoundaryParam n := by
  exact ContinuousLinearMap.fderiv (halfSpaceBoundaryParam n)

/-- The derivative of the boundary parametrization sends standard basis vectors to the boundary
tangent frame. -/
theorem fderiv_halfSpaceBoundaryParam_stdBasis (n : ℕ) (y : ℝSpace n) (i : Fin n) :
    fderiv ℝ (halfSpaceBoundaryParam n : ℝSpace n → ℝSpace (n + 1)) y
      (Pi.single i (1 : ℝ)) = halfSpaceBoundaryFrame n i := by
  rw [fderiv_halfSpaceBoundaryParam]
  ext j
  cases j using Fin.cases with
  | zero => simp [halfSpaceBoundaryFrame, halfSpaceBoundaryParam]
  | succ k =>
      change (Pi.single i (1 : ℝ) : Fin n → ℝ) k = halfSpaceBoundaryFrame n i k.succ
      rw [halfSpaceBoundaryFrame_succ]
      by_cases h : k = i <;> simp [Pi.single_apply, h]

/-- Boundary model orientation for the upper half-space.

For `HalfSpace (n + 1) = {x₀ ≥ 0}`, the outward normal is `-e₀`; hence the standard tangent
coordinate frame `(e₁, …, eₙ)` is negative relative to the outward-normal-first convention. -/
def halfSpaceBoundaryModelOrientation (n : ℕ) : Orientation ℝ (ℝSpace n) (Fin n) :=
  -ambientOrientation n

@[simp] theorem halfSpaceBoundaryModelOrientation_eq (n : ℕ) :
    halfSpaceBoundaryModelOrientation n = -ambientOrientation n :=
  rfl

end SmoothDomain

end
