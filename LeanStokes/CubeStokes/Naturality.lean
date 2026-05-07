/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Coefficient Precomposition by Linear Maps

For coordinate forms (represented as `Fin (n+1) → (Fin (n+1) → ℝ) → ℝ`),
we define precomposition by a continuous linear map: `(A · ω)_i(x) = ω_i(Ax)`.

**Important distinction**: This is coefficient-wise precomposition, NOT the true
pullback of differential forms (which would involve exterior powers of the derivative/
Jacobian and would mix coefficients). For the special case of endomorphisms of ℝⁿ⁺¹,
this is a meaningful operation that preserves smoothness and satisfies functoriality.

## Main results

* `CubeStokes.pullback`: Precomposition of a coordinate form by a continuous linear map.
* `CubeStokes.pullback_smooth`: Precomposition preserves smoothness.
* `CubeStokes.stokes_pullback`: Stokes holds for precomposed forms.
* `CubeStokes.pullback_comp`: Precomposition is functorial (contravariantly).
* `CubeStokes.pullback_id`: Precomposition by identity is identity.
* `CubeStokes.pullback_add`: Precomposition distributes over addition.
* `CubeStokes.pullback_smul`: Precomposition distributes over scalar multiplication.

## Limitations

This is NOT the true exterior-algebraic pullback `A*ω` which for a linear map
`A : ℝⁿ⁺¹ → ℝⁿ⁺¹` and an n-form would involve `det(A)` (or minors for k-forms).
Our operation makes sense for studying how coordinate forms transform under
affine substitutions but does not satisfy `d(A*ω) = A*(dω)` in general.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

variable {n : ℕ}

/-- The pullback of a coordinate form by a continuous linear map.
    `(A*ω) i x = ω i (A x)`. -/
def pullback (A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (ω : CoordNForm n) : CoordNForm n :=
  fun i x => ω i (A x)

/-- Pullback by a continuous linear map preserves smoothness. -/
theorem pullback_smooth (A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (ω : CoordNForm n) (hω : IsSmooth ω) :
    IsSmooth (pullback A ω) := by
  intro i
  exact _root_.ContDiff.comp (hω i) (ContinuousLinearMap.contDiff A)

/-- Stokes for a pulled-back form: if ω is smooth, then Stokes holds for
    `A*ω` on any box. -/
theorem stokes_pullback (A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (ω : CoordNForm n) (hω : IsSmooth ω) (a b : Fin (n + 1) → ℝ) (hab : a ≤ b) :
    boxIntegral (extDerivCoord (pullback A ω)) a b =
    bdryIntegral (pullback A ω) a b :=
  stokes_smooth a b hab (pullback A ω) (pullback_smooth A ω hω)

/-- Pullback is functorial: `A*(B*ω) = (B∘A)*ω`. -/
theorem pullback_comp (A B : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (ω : CoordNForm n) :
    pullback A (pullback B ω) = pullback (B.comp A) ω := by
  funext i x
  simp [pullback, ContinuousLinearMap.comp_apply]

/-- Pullback by identity is identity. -/
theorem pullback_id (ω : CoordNForm n) :
    pullback (ContinuousLinearMap.id ℝ _) ω = ω := by
  funext i x
  simp [pullback, ContinuousLinearMap.id_apply]

/-- The exterior derivative of a pulled-back form equals the pullback of the
    exterior derivative when the pullback is by the identity map. -/
theorem extDerivCoord_pullback_id (ω : CoordNForm n) :
    extDerivCoord (pullback (ContinuousLinearMap.id ℝ _) ω) = extDerivCoord ω := by
  rw [pullback_id]

/-- Pullback preserves the zero form. -/
theorem pullback_zero (A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) :
    pullback A (fun _ _ => 0 : CoordNForm n) = (fun _ _ => 0) := by
  funext i x
  simp [pullback]

/-- Pullback distributes over addition of forms. -/
theorem pullback_add (A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (ω η : CoordNForm n) :
    pullback A (fun i x => ω i x + η i x) =
    fun i x => pullback A ω i x + pullback A η i x := by
  funext i x
  simp [pullback]

/-- Pullback distributes over scalar multiplication of forms. -/
theorem pullback_smul (A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (c : ℝ) (ω : CoordNForm n) :
    pullback A (fun i x => c * ω i x) =
    fun i x => c * pullback A ω i x := by
  funext i x
  simp [pullback]

end CubeStokes

end
