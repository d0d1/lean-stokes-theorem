/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Chains
import Mathlib.Data.Fin.SuccPred

/-!
# Face Structure for Cubical Boxes

Defines the face operator on cubical boxes and proves the face-composition identity
that underlies ∂² = 0 in cubical homology.

## Main definitions

* `CubeStokes.faceBox`: The i-th face of a box (projection away from coordinate i).

## Main results

* `CubeStokes.faceBox_faceBox_lo/hi`: Face-of-face identity using
  `Fin.succAbove_succAbove_succAbove_predAbove`.
* `CubeStokes.faceBox_Icc`: Face box Icc equals projected Icc.
* `CubeStokes.num_faces`: A box in ℝⁿ⁺² has 2(n+2) faces.

## Mathematical significance

The face-of-face identity states that for a box B in ℝⁿ⁺³:
  `face j (face i B) = face (predAbove j i) (face (succAbove i j) B)`

This pairing is exactly what produces sign cancellation in ∂², since each
codimension-2 face appears as both `face j (face i B)` and
`face (predAbove j i) (face (succAbove i j) B)` with opposite orientations.
-/

open Set Finset MeasureTheory Filter Function Fin
open scoped Topology

noncomputable section

namespace CubeStokes

/-- The i-th face of a box B : CubicalBox (n+1). Projects away coordinate i,
giving a box in one fewer dimension. For B ⊂ ℝⁿ⁺², `faceBox B i` is the
projection onto the hyperplane perpendicular to coordinate i. -/
def faceBox (B : CubicalBox (n + 1)) (i : Fin (n + 2)) : CubicalBox n where
  lo := B.lo ∘ Fin.succAbove i
  hi := B.hi ∘ Fin.succAbove i
  le := fun j => B.le (Fin.succAbove i j)

@[simp]
theorem faceBox_lo (B : CubicalBox (n + 1)) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (faceBox B i).lo j = B.lo (Fin.succAbove i j) := rfl

@[simp]
theorem faceBox_hi (B : CubicalBox (n + 1)) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (faceBox B i).hi j = B.hi (Fin.succAbove i j) := rfl

/-- Face-of-face identity (lo component):
`(face j ∘ face i)(B).lo k = (face (predAbove j i) ∘ face (succAbove i j))(B).lo k`

Uses `Fin.succAbove_succAbove_succAbove_predAbove` from mathlib. -/
theorem faceBox_faceBox_lo (B : CubicalBox (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2))
    (k : Fin (n + 1)) :
    (faceBox (faceBox B i) j).lo k =
    (faceBox (faceBox B (i.succAbove j)) (j.predAbove i)).lo k := by
  simp only [faceBox_lo, Function.comp]
  congr 1
  exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm

/-- Face-of-face identity (hi component). -/
theorem faceBox_faceBox_hi (B : CubicalBox (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2))
    (k : Fin (n + 1)) :
    (faceBox (faceBox B i) j).hi k =
    (faceBox (faceBox B (i.succAbove j)) (j.predAbove i)).hi k := by
  simp only [faceBox_hi, Function.comp]
  congr 1
  exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm

/-- A box in ℝⁿ⁺² has `2(n+2)` faces (upper and lower at each of `n+2` coordinates). -/
theorem num_faces (n : ℕ) : 2 * (n + 2) = Fintype.card (Fin (n + 2) × Bool) := by
  simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring

/-- The Icc region of a face box equals the projected Icc of the original box. -/
theorem faceBox_Icc (B : CubicalBox (n + 1)) (i : Fin (n + 2)) :
    Icc (faceBox B i).lo (faceBox B i).hi =
    Icc (B.lo ∘ Fin.succAbove i) (B.hi ∘ Fin.succAbove i) := rfl

/-- Face box relates to bdryIntegral: the integration domain of the i-th face
in the boundary integral formula is exactly the Icc of faceBox B i. -/
theorem bdryIntegral_domain_eq_faceBox (B : CubicalBox (n + 1)) (i : Fin (n + 2)) :
    Icc (B.lo ∘ Fin.succAbove i) (B.hi ∘ Fin.succAbove i) =
    Icc (faceBox B i).lo (faceBox B i).hi := rfl

end CubeStokes
end
