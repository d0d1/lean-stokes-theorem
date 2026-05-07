/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.HalfSpace
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
