/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.SmoothDomain
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Boundary Flattening Coordinates

For a regular sublevel domain `M = {x | M.φ x ≤ 0}`, replacing one coordinate by
`-M.φ` sends the carrier condition to an upper half-space condition in that
coordinate.  The local diffeomorphism and determinant API built on this map is
developed separately.
-/

noncomputable section

open Topology Filter Set

namespace SmoothDomain

variable {d : ℕ} (M : SmoothDomain d)

/-- Coordinate replacement map used for local boundary flattening.

The chosen coordinate is `-φ`, so `φ ≤ 0` becomes the upper-half-space condition
`0 ≤ coord`.  Other coordinates are unchanged. -/
def flatteningMap (i : Fin d) : ℝSpace d → ℝSpace d :=
  fun x j => if j = i then -M.φ x else x j

@[simp] theorem flatteningMap_apply_self (i : Fin d) (x : ℝSpace d) :
    M.flatteningMap i x i = -M.φ x := by
  simp [flatteningMap]

@[simp] theorem flatteningMap_apply_ne {i j : Fin d} (hji : j ≠ i) (x : ℝSpace d) :
    M.flatteningMap i x j = x j := by
  simp [flatteningMap, hji]

/-- The carrier condition is the nonnegative condition on the replaced coordinate. -/
theorem mem_carrier_iff_flatteningMap_coord_nonneg (i : Fin d) (x : ℝSpace d) :
    x ∈ M.carrier ↔ 0 ≤ M.flatteningMap i x i := by
  simp [carrier]

/-- The boundary condition is the zero condition on the replaced coordinate. -/
theorem mem_boundary_iff_flatteningMap_coord_eq_zero (i : Fin d) (x : ℝSpace d) :
    x ∈ M.boundary ↔ M.flatteningMap i x i = 0 := by
  simp [boundary]

/-- The strict interior condition is the positive condition on the replaced coordinate. -/
theorem mem_int_iff_flatteningMap_coord_pos (i : Fin d) (x : ℝSpace d) :
    x ∈ M.int ↔ 0 < M.flatteningMap i x i := by
  simp [int]

/-- The coordinate replacement map is smooth. -/
theorem contDiff_flatteningMap (i : Fin d) :
    ContDiff ℝ ⊤ (M.flatteningMap i) := by
  apply contDiff_pi'
  intro j
  by_cases hji : j = i
  · subst j
    simpa [flatteningMap] using M.smooth_φ.neg
  · simpa [flatteningMap, hji] using
      ((contDiff_apply ℝ ℝ j) : ContDiff ℝ ⊤ fun x : ℝSpace d => x j)

/-- Derivative of the coordinate replacement map. -/
theorem fderiv_flatteningMap (i : Fin d) (x : ℝSpace d) :
    fderiv ℝ (M.flatteningMap i) x =
      ContinuousLinearMap.pi (fun j : Fin d =>
        if j = i then -fderiv ℝ M.φ x else ContinuousLinearMap.proj j) := by
  rw [fderiv_pi]
  · ext v j
    by_cases hji : j = i
    · subst j
      simp [flatteningMap]
    · have hproj :
          fderiv ℝ (fun x : ℝSpace d => x j) x = ContinuousLinearMap.proj j := by
        exact (ContinuousLinearMap.fderiv
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) (x := x))
      simp [flatteningMap, hji, hproj]
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [flatteningMap] using
        (M.smooth_φ.differentiable (by simp)).differentiableAt.neg
    · simpa [flatteningMap, hji] using
        ((contDiff_apply ℝ ℝ j).differentiable
          (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt

/-- Matrix of the flattening derivative in the standard basis.

It is the identity matrix with the selected row replaced by the row of `-dφ`. -/
theorem toMatrix_fderiv_flatteningMap (i : Fin d) (x : ℝSpace d) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
      (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) =
    Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) i
      (fun k => -fderiv ℝ M.φ x ((Pi.basisFun ℝ (Fin d)) k)) := by
  ext j k
  rw [LinearMap.toMatrix_apply]
  rw [M.fderiv_flatteningMap]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji, Matrix.one_apply, Pi.single_apply]

/-- The determinant of the flattening derivative is the negative selected partial derivative. -/
theorem det_fderiv_flatteningMap (i : Fin d) (x : ℝSpace d) :
    LinearMap.det (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) =
      -fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) := by
  let b : Module.Basis (Fin d) ℝ (ℝSpace d) := Pi.basisFun ℝ (Fin d)
  rw [← LinearMap.det_toMatrix b
    (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d)]
  rw [M.toMatrix_fderiv_flatteningMap]
  let row : Fin d → ℝ := fun k => -fderiv ℝ M.φ x (b k)
  have hrow : row = ∑ k, row k • (1 : Matrix (Fin d) (Fin d) ℝ) k := by
    ext k
    simp [row, Matrix.one_apply]
  change (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) i row).det =
    -fderiv ℝ M.φ x (Pi.single i (1 : ℝ))
  rw [hrow]
  rw [Matrix.det_updateRow_sum]
  simp [row, b]

/-- The flattening derivative has nonzero determinant when the selected partial derivative is
nonzero. -/
theorem det_fderiv_flatteningMap_ne_zero (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    LinearMap.det (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) ≠ 0 := by
  rw [M.det_fderiv_flatteningMap]
  exact neg_ne_zero.mpr h

/-- Nonvanishing determinant of the flattening derivative is equivalent to the selected partial
derivative being nonzero. -/
theorem det_fderiv_flatteningMap_ne_zero_iff (i : Fin d) (x : ℝSpace d) :
    LinearMap.det (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) ≠ 0 ↔
      fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0 := by
  rw [M.det_fderiv_flatteningMap]
  exact neg_ne_zero

/-- The continuous linear equivalence supplied by a flattening derivative whose selected partial
derivative is nonzero. -/
def flatteningFDerivEquiv (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    ℝSpace d ≃L[ℝ] ℝSpace d :=
  (fderiv ℝ (M.flatteningMap i) x).toContinuousLinearEquivOfDetNeZero
    (by simpa using M.det_fderiv_flatteningMap_ne_zero i x h)

@[simp] theorem coe_flatteningFDerivEquiv (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    (M.flatteningFDerivEquiv i x h : ℝSpace d →L[ℝ] ℝSpace d) =
      fderiv ℝ (M.flatteningMap i) x := by
  simp [flatteningFDerivEquiv]

/-- At every boundary point, some standard coordinate has nonzero derivative. -/
theorem exists_nonzero_fderiv_stdBasis {x : ℝSpace d} (hx : x ∈ M.boundary) :
    ∃ i : Fin d, fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0 := by
  by_contra h
  apply M.regular x hx
  push Not at h
  apply ContinuousLinearMap.ext
  intro v
  calc
    fderiv ℝ M.φ x v =
        fderiv ℝ M.φ x
          (∑ i, ((Pi.basisFun ℝ (Fin d)).repr v) i • (Pi.basisFun ℝ (Fin d)) i) := by
      rw [(Pi.basisFun ℝ (Fin d)).sum_repr v]
    _ = ∑ i, ((Pi.basisFun ℝ (Fin d)).repr v) i •
          fderiv ℝ M.φ x ((Pi.basisFun ℝ (Fin d)) i) := by
      simp [map_sum]
    _ = 0 := by
      simp [h]

end SmoothDomain

end
