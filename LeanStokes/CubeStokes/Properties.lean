/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Smooth
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Properties of the Coordinate Exterior Derivative

Algebraic properties of `extDerivCoord` and `bdryIntegral`.

## Main results

* `CubeStokes.extDerivCoord_add`: Linearity of d (addition).
* `CubeStokes.extDerivCoord_smul`: Linearity of d (scalar multiplication).
* `CubeStokes.extDerivCoord_neg`: d(-ω) = -dω.
* `CubeStokes.extDerivCoord_zero`: d(0) = 0.
* `CubeStokes.bdryIntegral_zero`: ∫_{∂B} 0 = 0.
* `CubeStokes.stokes_smooth_add`: Stokes respects addition.
* `CubeStokes.stokes_smooth_smul`: Stokes respects scalar multiplication.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

variable {n : ℕ}

/-- Addition of coordinate forms. -/
def CoordNForm.add (ω η : CoordNForm n) : CoordNForm n :=
  fun i x => ω i x + η i x

/-- Scalar multiplication of coordinate forms. -/
def CoordNForm.smul (c : ℝ) (ω : CoordNForm n) : CoordNForm n :=
  fun i x => c * ω i x

/-- The zero form. -/
def CoordNForm.zero : CoordNForm n := fun _ _ => 0

/-- Negation of forms. -/
def CoordNForm.neg (ω : CoordNForm n) : CoordNForm n :=
  fun i x => -(ω i x)

/-- Linearity of the exterior derivative: `d(ω + η) = dω + dη`. -/
theorem extDerivCoord_add (ω η : CoordNForm n) (x : Fin (n + 1) → ℝ)
    (hω : ∀ i, DifferentiableAt ℝ (ω i) x)
    (hη : ∀ i, DifferentiableAt ℝ (η i) x) :
    extDerivCoord (CoordNForm.add ω η) x =
    extDerivCoord ω x + extDerivCoord η x := by
  unfold extDerivCoord CoordNForm.add
  simp_rw [show ∀ i, (fun y => ω i y + η i y) = (ω i + η i) from fun i => rfl]
  simp_rw [fderiv_add (hω _) (hη _)]
  simp [ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib]

/-- Linearity of the exterior derivative: `d(c · ω) = c · dω`. -/
theorem extDerivCoord_smul (c : ℝ) (ω : CoordNForm n) (x : Fin (n + 1) → ℝ)
    (hω : ∀ i, DifferentiableAt ℝ (ω i) x) :
    extDerivCoord (CoordNForm.smul c ω) x = c * extDerivCoord ω x := by
  unfold extDerivCoord CoordNForm.smul
  simp_rw [show ∀ i, (fun y => c * ω i y) = c • ω i from fun i => by ext; simp [smul_eq_mul]]
  simp_rw [fderiv_const_smul (hω _)]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- `d(0) = 0`. -/
theorem extDerivCoord_zero (x : Fin (n + 1) → ℝ) :
    extDerivCoord CoordNForm.zero x = 0 := by
  unfold extDerivCoord CoordNForm.zero
  simp [fderiv_const]

/-- `d(-ω) = -(dω)`. -/
theorem extDerivCoord_neg (ω : CoordNForm n) (x : Fin (n + 1) → ℝ)
    (hω : ∀ i, DifferentiableAt ℝ (ω i) x) :
    extDerivCoord (CoordNForm.neg ω) x = -(extDerivCoord ω x) := by
  unfold extDerivCoord CoordNForm.neg
  simp_rw [show ∀ i, (fun y => -(ω i y)) = fun y => (-1 : ℝ) * ω i y from
    fun i => by ext; ring]
  simp_rw [fderiv_const_mul (hω _)]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_neg_distrib,
    neg_mul, mul_assoc, mul_left_comm]

/-- Boundary integral of zero is zero. -/
theorem bdryIntegral_zero (a b : Fin (n + 1) → ℝ) :
    bdryIntegral CoordNForm.zero a b = 0 := by
  unfold bdryIntegral CoordNForm.zero signedCoeff
  simp

/-- Stokes respects addition: for smooth forms, d(ω+η) integrates correctly. -/
theorem stokes_smooth_add (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (ω η : CoordNForm n) (hω : IsSmooth ω) (hη : IsSmooth η) :
    boxIntegral (extDerivCoord (CoordNForm.add ω η)) a b =
    bdryIntegral (CoordNForm.add ω η) a b :=
  stokes_smooth a b hle (CoordNForm.add ω η) (fun i => (hω i).add (hη i))

/-- Stokes respects scalar multiplication. -/
theorem stokes_smooth_smul (c : ℝ) (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (ω : CoordNForm n) (hω : IsSmooth ω) :
    boxIntegral (extDerivCoord (CoordNForm.smul c ω)) a b =
    bdryIntegral (CoordNForm.smul c ω) a b :=
  stokes_smooth a b hle (CoordNForm.smul c ω) (fun i => ContDiff.mul contDiff_const (hω i))

/-- The box integral scales linearly with a constant factor. -/
theorem boxIntegral_smul (c : ℝ) (f : (Fin (n + 1) → ℝ) → ℝ) (a b : Fin (n + 1) → ℝ) :
    boxIntegral (fun x => c * f x) a b = c * boxIntegral f a b := by
  unfold boxIntegral
  exact integral_const_mul c f

end CubeStokes
end
