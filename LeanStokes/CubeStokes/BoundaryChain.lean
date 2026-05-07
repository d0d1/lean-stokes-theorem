/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.BdryOp

/-!
# Cubical Boundary Chain Operator and ∂² = 0

We prove the fundamental property of cubical homology: ∂² = 0 (the boundary
of a boundary is zero). This is formalized at the level of signed face operations.

## Mathematical background

For a box B in ℝⁿ⁺³, the boundary ∂B is a signed sum of 2(n+3) faces.
The double boundary ∂²B involves codimension-2 faces, each appearing via
two paths (two different orderings of face projections). The face-of-face
identity shows these paths give the same geometric face, and the sign
cancellation lemma shows the signs are opposite, so ∂²B = 0.

## Main results

* `CubeStokes.double_boundary_cancels`: Signs cancel for codim-2 face pairs.
* `CubeStokes.double_boundary_same_face`: Geometry matches for codim-2 paths.
* `CubeStokes.bdry_sq_zero_combined`: ∂² = 0 (geometry + signs combined).
* `CubeStokes.boundary_squared_zero`: Net coefficient is zero for each codim-2 face.
-/

open Set Finset MeasureTheory Filter Function Fin
open scoped Topology

noncomputable section

namespace CubeStokes

/-- The signed coefficient of a face in the boundary formula:
    `(-1)^(i + ε)` where `i` is the direction and `ε` is the side (0=lo, 1=hi). -/
def faceCoeff (i : Fin (k + 1)) (ε : Bool) : ℤ :=
  (-1) ^ (i.val + ε.toNat)

/-- The signed coefficient equals bdrySign. -/
theorem faceCoeff_eq_bdrySign (i : Fin (k + 1)) (ε : Bool) :
    faceCoeff i ε = bdrySign i ε := rfl

/-- The total signed weight of a codimension-2 face in the double boundary.
    For any pair of directions (i, j) and sides (ε, η), the two paths to reach
    the same codimension-2 face give opposite signs, hence cancel. -/
theorem double_boundary_cancels (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (ε η : Bool) :
    faceCoeff i ε * faceCoeff j η +
    faceCoeff (i.succAbove j) η * faceCoeff (j.predAbove i) ε = 0 := by
  unfold faceCoeff
  exact bdry_sq_sign_cancel n i j ε η

/-- The face geometry: the two paths to a codimension-2 face give the same box.
    `face_j(face_i(B)) = face_{predAbove j i}(face_{succAbove i j}(B))` -/
theorem double_boundary_same_face (n : ℕ) (B : CubicalBox (n + 2))
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    faceBox (faceBox B i) j = faceBox (faceBox B (i.succAbove j)) (j.predAbove i) := by
  unfold faceBox
  congr 1
  · funext k; exact faceBox_faceBox_lo B i j k
  · funext k; exact faceBox_faceBox_hi B i j k

/-- **∂² = 0**: For each codimension-2 face in the double boundary of a box,
    the geometric faces match and the signed coefficients cancel. -/
theorem bdry_sq_zero_combined (n : ℕ) (B : CubicalBox (n + 2))
    (i : Fin (n + 3)) (j : Fin (n + 2)) (ε η : Bool) :
    faceBox (faceBox B i) j = faceBox (faceBox B (i.succAbove j)) (j.predAbove i) ∧
    faceCoeff i ε * faceCoeff j η +
      faceCoeff (i.succAbove j) η * faceCoeff (j.predAbove i) ε = 0 :=
  ⟨double_boundary_same_face n B i j, double_boundary_cancels n i j ε η⟩

/-- ∂² = 0 restated using bdrySign2 for compatibility. -/
theorem boundary_squared_zero (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (ε η : Bool) :
    bdrySign2 i ε j η + bdrySign2 (i.succAbove j) η (j.predAbove i) ε = 0 :=
  bdry_sq_sign_cancel n i j ε η

/-- The double boundary formula: the composite sign for path 1 equals the
    negation of the composite sign for path 2. -/
theorem double_boundary_sign_neg (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (ε η : Bool) :
    bdrySign2 i ε j η = -(bdrySign2 (i.succAbove j) η (j.predAbove i) ε) := by
  linarith [bdry_sq_sign_cancel n i j ε η]

end CubeStokes
end
