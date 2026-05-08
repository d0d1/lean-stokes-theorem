/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.Pullback
import LeanStokes.CubeStokes.Bridge
import LeanStokes.DiffForm.SmoothEval

/-!
# Smoothness of Pullback Forms

Proves that the pullback of a smooth differential form along a smooth singular cube
has smooth coordinate coefficients and is differentiable.

## Main results

* `contDiff_multilinearMap_apply_of_contDiff`: Evaluation of a smooth multilinear-map-valued
  function on smooth vector-valued functions is smooth.
* `pullbackForm_differentiable`: The pullback form is differentiable.
* `toCoordNForm_pullback_isSmooth`: The coordinate coefficients of the pullback form are smooth.

## Strategy

The generic smooth multilinear-evaluation helper lives in
`LeanStokes.DiffForm.SmoothEval`; this file keeps the singular-cube regularity
specializations.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace SingularCubeStokes

variable {d m : ℕ}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Compatibility alias for the generic smooth multilinear-evaluation helper. -/
theorem contDiff_multilinearMap_apply_of_contDiff (N : ℕ)
    (f : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin N => F) G)
    (g : Fin N → E → F)
    (hf : ContDiff 𝕜 (⊤ : ℕ∞) f) (hg : ∀ k, ContDiff 𝕜 (⊤ : ℕ∞) (g k)) :
    ContDiff 𝕜 (⊤ : ℕ∞) (fun x => (f x) (fun k => g k x)) :=
  DiffForm.contDiff_multilinearMap_apply_of_contDiff N f g hf hg

/-- The pullback form is differentiable: if ω is differentiable and σ is C^∞,
then `pullbackForm σ ω` is differentiable as a ContinuousAlternatingMap-valued function. -/
theorem pullbackForm_differentiable {n : ℕ} (σ : SmoothSingularCube d m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    Differentiable ℝ (pullbackForm σ ω) := by
  intro x
  unfold pullbackForm
  apply DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
  · exact ((hω.comp σ.smooth).differentiable
      (by simp)).differentiableAt
  · have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ σ.toFun) :=
      σ.smooth.fderiv_right (by simp)
    exact (hfderiv.differentiable (by simp)).differentiableAt

/-- Each coordinate coefficient of the pullback form is smooth.

The i-th coefficient is `fun x => ω(σ x)(fun k => fderiv ℝ σ x (eₖ))`.
This is proved using `contDiff_multilinearMap_apply_of_contDiff` by converting
the alternating map to a multilinear map and verifying smoothness of all components. -/
theorem toCoordNForm_pullback_isSmooth {n : ℕ} (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    CubeStokes.IsSmooth (CubeStokes.toCoordNForm (pullbackForm σ ω)) := by
  intro i
  -- The i-th coefficient is:
  -- fun x => (pullbackForm σ ω x)(fun k => Pi.single (Fin.succAbove i k) 1)
  -- = fun x => ω(σ x)(fun k => fderiv ℝ σ x (Pi.single (Fin.succAbove i k) 1))
  change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    (ω (σ.toFun x)) (fun k => fderiv ℝ σ.toFun x (Pi.single (Fin.succAbove i k) 1)))
  -- Convert to multilinear map evaluation
  have h_eq : (fun x => (ω (σ.toFun x)) (fun k =>
      fderiv ℝ σ.toFun x (Pi.single (Fin.succAbove i k) 1))) =
    (fun x => ((ω (σ.toFun x)).toContinuousMultilinearMap)
      (fun k => fderiv ℝ σ.toFun x (Pi.single (Fin.succAbove i k) 1))) := by
    ext x; rfl
  rw [h_eq]
  -- Apply the key helper lemma
  apply contDiff_multilinearMap_apply_of_contDiff n
  · -- f(x) = (ω(σ x)).toContinuousMultilinearMap is C^∞
    -- toContinuousMultilinearMapCLM is a CLM from alternating to multilinear maps
    exact (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
      ).contDiff.comp (hω.comp σ.smooth)
  · -- Each gₖ(x) = fderiv ℝ σ x (eₖ) is C^∞
    intro k
    have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ σ.toFun) :=
      σ.smooth.fderiv_right (by simp)
    exact hfderiv.clm_apply contDiff_const

end SingularCubeStokes

end
