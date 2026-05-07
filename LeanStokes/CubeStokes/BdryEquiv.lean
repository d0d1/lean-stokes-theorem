/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Defs

/-!
# Boundary integral reformulations

Shows that `bdryIntegral` (with signs inside integrals) equals the standard
mathematical expression with signs outside integrals.

## Main results

* `CubeStokes.bdryIntegral_eq`: Signs can be pulled outside the integrals.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- The boundary integral equals the standard signed face-sum formula.
By linearity of integration, `(-1)^i` can be factored outside each face integral. -/
theorem bdryIntegral_eq (ω : CoordNForm n) (a b : Fin (n + 1) → ℝ) :
    bdryIntegral ω a b =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) *
        ((∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            ω i (Fin.insertNth i (b i) x)) -
         (∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            ω i (Fin.insertNth i (a i) x))) := by
  unfold bdryIntegral signedCoeff
  congr 1; ext i
  simp only [integral_const_mul, mul_sub]

end CubeStokes

end
