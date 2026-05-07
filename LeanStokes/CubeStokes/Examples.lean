/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Smooth

/-!
# Concrete Examples of Cubical Stokes

Instantiates the Stokes identity for concrete forms: constant forms (dω = 0)
and the coordinate form in 1D (recovering FTC as d(x₀) = 1).

## Main results

* `CubeStokes.extDerivCoord_const_zero`: The exterior derivative of a constant form is zero.
* `CubeStokes.stokes_constant_form`: Stokes for a constant form: both sides are zero.
* `CubeStokes.extDerivCoord_coordForm1d`: d(x₀) = 1 in 1D.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

/-- A constant coordinate form: all components equal `c`. -/
def constForm (n : ℕ) (c : ℝ) : CoordNForm n :=
  fun _ _ => c

/-- A constant form is smooth. -/
theorem constForm_smooth (n : ℕ) (c : ℝ) : IsSmooth (constForm n c) := by
  intro i; exact contDiff_const

/-- The exterior derivative of a constant form is zero.
This is the coordinate analogue of d(constant) = 0. -/
theorem extDerivCoord_const_zero (n : ℕ) (c : ℝ) :
    extDerivCoord (constForm n c) = fun _ => 0 := by
  funext x
  simp only [extDerivCoord]
  apply Finset.sum_eq_zero
  intro i _
  change (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ (constForm n c i) x) (Pi.single i 1) = 0
  have h : constForm n c i = fun _ => c := rfl
  rw [h, fderiv_const_apply]
  simp

/-- Stokes for a constant form: the interior integral of dω = 0 is zero. -/
theorem stokes_constant_form (n : ℕ) (c : ℝ) (a b : Fin (n + 1) → ℝ) :
    boxIntegral (extDerivCoord (constForm n c)) a b = 0 := by
  rw [extDerivCoord_const_zero]
  simp [boxIntegral]

/-- Coordinate form in 1D: ω(i)(x) = x₀. -/
def coordForm1d : CoordNForm 0 :=
  fun _ (x : Fin 1 → ℝ) => x 0

/-- The coordinate form in 1D is smooth. -/
theorem coordForm1d_smooth : IsSmooth coordForm1d := by
  intro i
  have h : coordForm1d i = fun (x : Fin 1 → ℝ) => x 0 := rfl
  rw [h]
  exact (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 1) (φ := fun _ => ℝ) 0).contDiff

/-- d(x₀) = 1 in 1D: the exterior derivative of the coordinate form is constant 1.
This is the derivative computation underlying FTC. -/
theorem extDerivCoord_coordForm1d :
    extDerivCoord coordForm1d = fun _ => 1 := by
  funext x
  simp only [extDerivCoord]
  rw [show Finset.univ (α := Fin 1) = {(0 : Fin 1)} from rfl]
  simp only [Finset.sum_singleton, Fin.val_zero, pow_zero, one_mul]
  change (fderiv ℝ (coordForm1d 0) x) (Pi.single 0 1) = 1
  have h : coordForm1d 0 = fun (x : Fin 1 → ℝ) => x 0 := rfl
  rw [h]
  have hd : fderiv ℝ (fun (x : Fin 1 → ℝ) => x 0) x =
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 1) (φ := fun _ => ℝ) 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 1) (φ := fun _ => ℝ) 0).hasFDerivAt.fderiv
  rw [hd]
  simp [Pi.single, Function.update]

/-- Applying Stokes to the 1D coordinate form gives FTC. -/
theorem stokes_coordForm1d (a b : Fin 1 → ℝ) (hab : a ≤ b) :
    boxIntegral (extDerivCoord coordForm1d) a b =
    bdryIntegral coordForm1d a b :=
  stokes_smooth a b hab coordForm1d coordForm1d_smooth

end CubeStokes
end
