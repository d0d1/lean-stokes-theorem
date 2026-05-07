/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Pullback
import LeanStokes.Integration.FormIntegral
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Function.Jacobian

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

/-- Change of variables for top-form integrals under a map whose global derivative agrees with
the within derivative on the source and has nonnegative determinant there. -/
theorem integral_image_eq_integral_pullback_of_det_nonneg
    {f : ℝSpace d → ℝSpace d} {s : Set (ℝSpace d)} (η : DiffForm d d)
    (hs : MeasurableSet s)
    (hfderiv : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x)
    (hf : Set.InjOn f s)
    (hdet : ∀ x ∈ s, 0 ≤ LinearMap.det (fderiv ℝ f x : ℝSpace d →ₗ[ℝ] ℝSpace d)) :
    integral η (f '' s) = integral (pullback f η) s := by
  unfold integral
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hs hfderiv hf]
  apply MeasureTheory.setIntegral_congr_fun hs
  intro x hx
  dsimp
  have hdet' : 0 ≤ (fderiv ℝ f x).det := by
    simpa using hdet x hx
  rw [abs_of_nonneg hdet']
  change (fderiv ℝ f x).det * topCoeff η (f x) = topCoeff (pullback f η) x
  rw [topCoeff_pullback]

/-- A differentiability-at version of
`integral_image_eq_integral_pullback_of_det_nonneg`. -/
theorem integral_image_eq_integral_pullback_of_det_nonneg_of_differentiableAt
    {f : ℝSpace d → ℝSpace d} {s : Set (ℝSpace d)} (η : DiffForm d d)
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hf : Set.InjOn f s)
    (hdet : ∀ x ∈ s, 0 ≤ LinearMap.det (fderiv ℝ f x : ℝSpace d →ₗ[ℝ] ℝSpace d)) :
    integral η (f '' s) = integral (pullback f η) s :=
  integral_image_eq_integral_pullback_of_det_nonneg η hs
    (fun x hx => (hf' x hx).hasFDerivAt.hasFDerivWithinAt) hf hdet

/-- Change of variables for top-form integrals under a map whose global derivative agrees with
the within derivative on the source and has nonpositive determinant there. -/
theorem integral_image_eq_neg_integral_pullback_of_det_nonpos
    {f : ℝSpace d → ℝSpace d} {s : Set (ℝSpace d)} (η : DiffForm d d)
    (hs : MeasurableSet s)
    (hfderiv : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x)
    (hf : Set.InjOn f s)
    (hdet : ∀ x ∈ s, LinearMap.det (fderiv ℝ f x : ℝSpace d →ₗ[ℝ] ℝSpace d) ≤ 0) :
    integral η (f '' s) = -integral (pullback f η) s := by
  unfold integral
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) hs hfderiv hf,
    ← MeasureTheory.integral_neg]
  apply MeasureTheory.setIntegral_congr_fun hs
  intro x hx
  dsimp
  have hdet' : (fderiv ℝ f x).det ≤ 0 := by
    simpa using hdet x hx
  rw [abs_of_nonpos hdet']
  change -(fderiv ℝ f x).det * topCoeff η (f x) =
    -topCoeff (pullback f η) x
  rw [topCoeff_pullback]
  ring

/-- A differentiability-at version of
`integral_image_eq_neg_integral_pullback_of_det_nonpos`. -/
theorem integral_image_eq_neg_integral_pullback_of_det_nonpos_of_differentiableAt
    {f : ℝSpace d → ℝSpace d} {s : Set (ℝSpace d)} (η : DiffForm d d)
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hf : Set.InjOn f s)
    (hdet : ∀ x ∈ s, LinearMap.det (fderiv ℝ f x : ℝSpace d →ₗ[ℝ] ℝSpace d) ≤ 0) :
    integral η (f '' s) = -integral (pullback f η) s :=
  integral_image_eq_neg_integral_pullback_of_det_nonpos η hs
    (fun x hx => (hf' x hx).hasFDerivAt.hasFDerivWithinAt) hf hdet

end DiffForm

end
