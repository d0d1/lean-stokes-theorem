/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Bridge

/-!
# Face Pullback Interpretation

Proves that the boundary face-sum in `bdryIntegral` agrees with the evaluation
of the original mathlib form on each face via the face inclusion map.

For a mathlib n-form ω on ℝⁿ⁺¹, the pullback to the i-th face (at value c)
via the inclusion `ι_i^c(xh) = insertNth i c xh` gives:
  `(ι_i^c)* ω (xh)(ê₀, ..., ê_{n-1}) = ω(ι_i^c(xh))(e_{succAbove i 0}, ..., e_{succAbove i (n-1)})`

This equals `(toCoordNForm ω) i (insertNth i c xh)`, which is exactly what
appears in the boundary face-sum after accounting for the sign.

## Main results

* `CubeStokes.face_value_eq_toCoordNForm`: The value of a form on a face equals
  the extracted coordinate coefficient at the face point.
* `CubeStokes.bdryIntegral_eq_face_sum`: The boundary integral is a signed sum
  of coordinate coefficients evaluated on faces.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function VectorField
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- The value of a mathlib n-form ω on the i-th face at position c, evaluated on
the standard face basis, equals the i-th coordinate coefficient at the inserted point.

This justifies `toCoordNForm`: the coefficient function measures exactly what the
form evaluates to on each face of the box. -/
theorem face_value_eq_toCoordNForm
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (i : Fin (n + 1)) (c : ℝ) (xh : Fin n → ℝ) :
    ω (Fin.insertNth i c xh) (fun k => Pi.single (Fin.succAbove i k) 1)
    = toCoordNForm ω i (Fin.insertNth i c xh) := by
  rfl

/-- The boundary face-sum of `toCoordNForm ω` computes signed differences of
the form's face values. Specifically, `bdryIntegral (toCoordNForm ω) a b` equals
the sum over all faces of `(-1)^i` times the integral of `ω` on that face. -/
theorem bdryIntegral_toCoordNForm_eq
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (a b : Fin (n + 1) → ℝ) :
    bdryIntegral (toCoordNForm ω) a b =
    ∑ i : Fin (n + 1),
      ((∫ xh in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
          (-1 : ℝ) ^ (i : ℕ) * ω (Fin.insertNth i (b i) xh)
            (fun k => Pi.single (Fin.succAbove i k) 1)) -
       (∫ xh in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
          (-1 : ℝ) ^ (i : ℕ) * ω (Fin.insertNth i (a i) xh)
            (fun k => Pi.single (Fin.succAbove i k) 1))) := by
  unfold bdryIntegral signedCoeff toCoordNForm
  rfl

end CubeStokes

end
