/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Pullback
import LeanStokes.Integration.FormIntegral
import Mathlib.LinearAlgebra.Determinant

/-!
# Pullback and Top Coefficients

Relates the top coefficient of a pulled-back top form to the determinant of the
derivative.  This is the signed algebraic coefficient identity used later to
build oriented change-of-variables for form integrals.
-/

noncomputable section

open MeasureTheory Topology Filter Set MeasureTheory.Measure
open scoped ENNReal

namespace DiffForm

variable {d : ℕ}

/-- The project standard frame agrees with mathlib's `Pi.basisFun`. -/
@[simp] theorem stdBasis_eq_basisFun :
    stdBasis (d := d) = (Pi.basisFun ℝ (Fin d) : Fin d → ℝSpace d) := by
  ext i j
  change (Pi.single i (1 : ℝ) : Fin d → ℝ) j =
    (Pi.basisFun ℝ (Fin d) i : ℝSpace d) j
  simp

/-- Evaluating a top form after precomposition by a linear map multiplies the top coefficient by
the signed determinant of that linear map. -/
theorem topCoeff_compContinuousLinearMap
    (α : ℝSpace d [⋀^Fin d]→L[ℝ] ℝ) (L : ℝSpace d →L[ℝ] ℝSpace d) :
    α.compContinuousLinearMap L (stdBasis (d := d)) =
      LinearMap.det (L : ℝSpace d →ₗ[ℝ] ℝSpace d) * α (stdBasis (d := d)) := by
  let b : Module.Basis (Fin d) ℝ (ℝSpace d) := Pi.basisFun ℝ (Fin d)
  have hstd : stdBasis (d := d) = (b : Fin d → ℝSpace d) := by
    ext i j
    change (Pi.single i (1 : ℝ) : Fin d → ℝ) j =
      (Pi.basisFun ℝ (Fin d) i : ℝSpace d) j
    simp
  rw [hstd]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change α.toAlternatingMap ((L : ℝSpace d →ₗ[ℝ] ℝSpace d) ∘ (b : Fin d → ℝSpace d)) =
    LinearMap.det (L : ℝSpace d →ₗ[ℝ] ℝSpace d) *
      α.toAlternatingMap (b : Fin d → ℝSpace d)
  calc
    α.toAlternatingMap ((L : ℝSpace d →ₗ[ℝ] ℝSpace d) ∘ (b : Fin d → ℝSpace d))
        = (α.toAlternatingMap (b : Fin d → ℝSpace d) • b.det)
            ((L : ℝSpace d →ₗ[ℝ] ℝSpace d) ∘ (b : Fin d → ℝSpace d)) := by
          conv_lhs => rw [α.toAlternatingMap.eq_smul_basis_det b]
    _ = α.toAlternatingMap (b : Fin d → ℝSpace d) *
          b.det ((L : ℝSpace d →ₗ[ℝ] ℝSpace d) ∘ (b : Fin d → ℝSpace d)) := by
          rfl
    _ = α.toAlternatingMap (b : Fin d → ℝSpace d) *
          (LinearMap.det (L : ℝSpace d →ₗ[ℝ] ℝSpace d) *
            b.det (b : Fin d → ℝSpace d)) := by
          rw [Module.Basis.det_comp]
    _ = LinearMap.det (L : ℝSpace d →ₗ[ℝ] ℝSpace d) *
          α.toAlternatingMap (b : Fin d → ℝSpace d) := by
          simp [Module.Basis.det_self, mul_comm]

/-- Pointwise top-coefficient formula for same-dimensional pullback. -/
theorem topCoeff_pullback (f : ℝSpace d → ℝSpace d) (η : DiffForm d d)
    (x : ℝSpace d) :
    topCoeff (pullback f η) x =
      LinearMap.det (fderiv ℝ f x : ℝSpace d →ₗ[ℝ] ℝSpace d) * topCoeff η (f x) := by
  simpa [topCoeff, pullback] using
    topCoeff_compContinuousLinearMap (η (f x)) (fderiv ℝ f x)

end DiffForm

end
