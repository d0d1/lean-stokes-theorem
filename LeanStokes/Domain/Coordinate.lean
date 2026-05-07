/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.HalfSpace
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Coordinate Permutations

Reusable coordinate permutations for Euclidean spaces `Fin d → ℝ`.
-/

noncomputable section

open Topology Filter Set

namespace Coordinate

variable {d : ℕ}

/-- Swap coordinate `i` with coordinate `0`.

The determinant of this coordinate permutation is `1` when `i = 0` and `-1` otherwise; later
orientation-sensitive APIs must account for this sign explicitly. -/
def moveToZero [NeZero d] (i : Fin d) : ℝSpace d ≃L[ℝ] ℝSpace d where
  toFun x j := x ((Equiv.swap (0 : Fin d) i) j)
  invFun x j := x ((Equiv.swap (0 : Fin d) i) j)
  left_inv x := by
    ext j
    simp [Equiv.swap_apply_self]
  right_inv x := by
    ext j
    simp [Equiv.swap_apply_self]
  map_add' x y := by
    ext j
    rfl
  map_smul' c x := by
    ext j
    rfl
  continuous_toFun := by
    exact continuous_pi fun j => continuous_apply ((Equiv.swap (0 : Fin d) i) j)
  continuous_invFun := by
    exact continuous_pi fun j => continuous_apply ((Equiv.swap (0 : Fin d) i) j)

@[simp] theorem moveToZero_apply [NeZero d] (i j : Fin d) (x : ℝSpace d) :
    moveToZero i x j = x ((Equiv.swap (0 : Fin d) i) j) :=
  rfl

@[simp] theorem moveToZero_zero [NeZero d] (i : Fin d) (x : ℝSpace d) :
    moveToZero i x (0 : Fin d) = x i := by
  simp [moveToZero]

/-- The coordinate swap as a global homeomorphism. -/
def moveToZeroHomeomorph [NeZero d] (i : Fin d) : ℝSpace d ≃ₜ ℝSpace d :=
  (moveToZero i).toHomeomorph

@[simp] theorem moveToZeroHomeomorph_apply [NeZero d] (i j : Fin d) (x : ℝSpace d) :
    moveToZeroHomeomorph i x j = x ((Equiv.swap (0 : Fin d) i) j) :=
  rfl

/-- Matrix of the coordinate swap in the standard basis. -/
theorem toMatrix_moveToZero [NeZero d] (i : Fin d) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
      (moveToZero i : ℝSpace d →ₗ[ℝ] ℝSpace d) =
    (Equiv.swap (0 : Fin d) i).permMatrix ℝ := by
  ext j k
  rw [LinearMap.toMatrix_apply]
  by_cases h : (Equiv.swap (0 : Fin d) i) j = k
  · simp [moveToZero, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, Pi.single_apply, h]
  · simp [moveToZero, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, Pi.single_apply, h]

/-- Determinant of the coordinate swap. -/
theorem det_moveToZero [NeZero d] (i : Fin d) :
    LinearMap.det (moveToZero i : ℝSpace d →ₗ[ℝ] ℝSpace d) =
      (Equiv.Perm.sign (Equiv.swap (0 : Fin d) i) : ℝ) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin d))
    (moveToZero i : ℝSpace d →ₗ[ℝ] ℝSpace d)]
  rw [toMatrix_moveToZero]
  exact Matrix.det_permutation (R := ℝ) (Equiv.swap (0 : Fin d) i)

/-- The coordinate swap has nonzero determinant. -/
theorem det_moveToZero_ne_zero [NeZero d] (i : Fin d) :
    LinearMap.det (moveToZero i : ℝSpace d →ₗ[ℝ] ℝSpace d) ≠ 0 := by
  rw [det_moveToZero]
  by_cases hi : (0 : Fin d) = i
  · simp [hi]
  · simp [Equiv.Perm.sign_swap hi]

/-- Moving coordinate `i` to coordinate `0` converts `0 ≤ x i` to the standard half-space. -/
theorem mem_halfSpace_moveToZero_iff_coord_nonneg [NeZero d] (i : Fin d) (x : ℝSpace d) :
    moveToZero i x ∈ HalfSpace d ↔ 0 ≤ x i := by
  simp [HalfSpace]

/-- Moving coordinate `i` to coordinate `0` converts `x i = 0` to the standard boundary face. -/
theorem mem_halfSpaceBdry_moveToZero_iff_coord_eq_zero [NeZero d] (i : Fin d)
    (x : ℝSpace d) :
    moveToZero i x ∈ HalfSpaceBdry d ↔ x i = 0 := by
  simp [HalfSpaceBdry]

/-- Moving coordinate `i` to coordinate `0` converts `0 < x i` to the standard open half-space. -/
theorem mem_halfSpaceOpen_moveToZero_iff_coord_pos [NeZero d] (i : Fin d) (x : ℝSpace d) :
    moveToZero i x ∈ HalfSpaceOpen d ↔ 0 < x i := by
  simp [HalfSpaceOpen]

end Coordinate

end
