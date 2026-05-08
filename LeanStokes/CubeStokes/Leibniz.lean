/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Leibniz Rule for Coordinate Exterior Derivative

The Leibniz (product) rule for the coordinate exterior derivative:

  d(f · ω) = (df) · ω + f · dω

where f is a smooth scalar function and ω is a smooth coordinate n-form.
Here (df) · ω means the product of each partial derivative of f with the
corresponding component of ω, summed with appropriate signs.

## Main results

* `CubeStokes.extDerivCoord_smul_fun`: d(f·ω) in terms of derivatives of f and ω.
* `CubeStokes.extDerivCoord_product_rule`: The full product rule identity.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

/-- Scalar multiplication of a smooth function by a coordinate form: (f·ω)(i)(x) = f(x)·ω(i)(x). -/
def scalarMul (f : (Fin (n+1) → ℝ) → ℝ) (ω : CoordNForm n) : CoordNForm n :=
  fun i x => f x * ω i x

/-- scalarMul preserves smoothness when both f and ω are smooth. -/
theorem scalarMul_smooth {f : (Fin (n+1) → ℝ) → ℝ} {ω : CoordNForm n}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hω : IsSmooth ω) :
    IsSmooth (scalarMul f ω) := by
  intro i
  have : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * ω i x) := hf.mul (hω i)
  exact this

/-- The exterior derivative of a scalar product satisfies the Leibniz rule.
For smooth f and smooth ω:
  d(f·ω)(x) = ∑ᵢ (-1)ⁱ · [f'(x)(eᵢ) · ω(i)(x) + f(x) · ω'ᵢ(x)(eᵢ)]

This is the product rule d(f·ω) = df∧ω + f·dω in coordinates. -/
theorem extDerivCoord_scalarMul
    {f : (Fin (n+1) → ℝ) → ℝ} {ω : CoordNForm n}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hω : IsSmooth ω) (x : Fin (n+1) → ℝ) :
    extDerivCoord (scalarMul f ω) x =
    ∑ i : Fin (n+1), (-1 : ℝ) ^ (i : ℕ) *
      ((fderiv ℝ f x) (Pi.single i 1) * ω i x +
       f x * (fderiv ℝ (ω i) x) (Pi.single i 1)) := by
  simp only [extDerivCoord, scalarMul]
  congr 1
  ext i
  change (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ (fun x => f x * ω i x) x) (Pi.single i 1) = _
  have hfi : DifferentiableAt ℝ f x :=
    (hf.differentiable (by norm_num)).differentiableAt
  have hωi : DifferentiableAt ℝ (ω i) x :=
    ((hω i).differentiable (by norm_num)).differentiableAt
  have hprod : fderiv ℝ (fun x => f x * ω i x) x =
      f x • fderiv ℝ (ω i) x + ω i x • fderiv ℝ f x :=
    (hfi.hasFDerivAt.mul hωi.hasFDerivAt).fderiv
  rw [hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The Leibniz rule expressed as: d(f·ω) = f·dω + "gradient term".
The gradient term is ∑ᵢ (-1)ⁱ · (∂f/∂xᵢ) · ω(i). -/
theorem extDerivCoord_scalarMul_split
    {f : (Fin (n+1) → ℝ) → ℝ} {ω : CoordNForm n}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hω : IsSmooth ω) (x : Fin (n+1) → ℝ) :
    extDerivCoord (scalarMul f ω) x =
    f x * extDerivCoord ω x +
    ∑ i : Fin (n+1), (-1 : ℝ) ^ (i : ℕ) *
      ((fderiv ℝ f x) (Pi.single i 1) * ω i x) := by
  rw [extDerivCoord_scalarMul hf hω]
  simp only [extDerivCoord, signedCoeff]
  conv_rhs => rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  funext i
  ring

end CubeStokes
end
