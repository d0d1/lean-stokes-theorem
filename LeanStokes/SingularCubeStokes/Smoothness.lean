/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.Pullback
import LeanStokes.CubeStokes.Bridge
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

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

The key helper (`contDiff_multilinearMap_apply_of_contDiff`) uses induction on arity:
- Base (arity 0): evaluation at the unique empty tuple is a CLM → compose with smooth = smooth
- Step (arity N+1): curry the first argument via `continuousMultilinearCurryLeftEquiv`, use
  `ContDiff.clm_apply` for the curried step, then apply induction for the remaining arguments.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace SingularCubeStokes

variable {d m : ℕ}

section SmoothnessHelper

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Key smoothness lemma**: If `f` is a C^∞ function valued in continuous multilinear maps
of arity N, and each `gₖ` is a C^∞ function, then the pointwise evaluation
`x ↦ (f x)(g₀ x, g₁ x, ..., g_{N-1} x)` is C^∞.

Proof by induction on N using currying. -/
theorem contDiff_multilinearMap_apply_of_contDiff (N : ℕ)
    (f : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin N => F) G)
    (g : Fin N → E → F)
    (hf : ContDiff 𝕜 ⊤ f) (hg : ∀ k, ContDiff 𝕜 ⊤ (g k)) :
    ContDiff 𝕜 ⊤ (fun x => (f x) (fun k => g k x)) := by
  induction N with
  | zero =>
    -- For arity 0, (Fin 0 → F) is subsingleton, so (fun k => g k x) = default
    have h_eq : (fun x => (f x) (fun k : Fin 0 => g k x)) =
        (fun x => (f x) (Fin.elim0)) := by
      ext x; congr 1; exact Subsingleton.elim _ _
    rw [h_eq]
    -- (f x) Fin.elim0 is a CLM applied to f x
    exact (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 => F) G
      Fin.elim0).contDiff.comp hf
  | succ N ih =>
    -- Rewrite using Fin.cons: (fun k => g k x) = Fin.cons (g 0 x) (fun k => g (succ k) x)
    have h_eq : (fun x => (f x) (fun k => g k x)) =
        (fun x => (f x) (Fin.cons (g 0 x) (fun k => g (Fin.succ k) x))) := by
      ext x; congr 1; exact (Fin.cons_self_tail (fun k => g k x)).symm
    rw [h_eq]
    -- Use curryLeft: f(cons v₀ rest) = f.curryLeft(v₀)(rest)
    have h_curry : (fun x => (f x) (Fin.cons (g 0 x) (fun k => g (Fin.succ k) x))) =
        (fun x => ((f x).curryLeft (g 0 x)) (fun k => g (Fin.succ k) x)) := by
      ext x; rw [ContinuousMultilinearMap.curryLeft_apply]
    rw [h_curry]
    -- curryLeft is a linear isometric equiv, extract it as CLM
    set CL := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (N + 1) => F) G
      ).toContinuousLinearEquiv.toContinuousLinearMap
    -- CL ∘ f is smooth (CLM composed with smooth f)
    have hCLf : ContDiff 𝕜 ⊤ (fun x => CL (f x)) := CL.contDiff.comp hf
    -- h(x) := (f x).curryLeft (g 0 x) = (CL (f x)) (g 0 x) is smooth by clm_apply
    have h_clm_eq : (fun x => (f x).curryLeft (g 0 x)) = (fun x => (CL (f x)) (g 0 x)) := by
      rfl
    have hh : ContDiff 𝕜 ⊤ (fun x => (f x).curryLeft (g 0 x)) := by
      rw [h_clm_eq]; exact hCLf.clm_apply (hg 0)
    -- Apply induction hypothesis
    exact ih (fun x => (f x).curryLeft (g 0 x))
      (fun k => g (Fin.succ k)) hh (fun k => hg (Fin.succ k))

end SmoothnessHelper

/-- The pullback form is differentiable: if ω is differentiable and σ is C^∞,
then `pullbackForm σ ω` is differentiable as a ContinuousAlternatingMap-valued function. -/
theorem pullbackForm_differentiable {n : ℕ} (σ : SmoothSingularCube d m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ ⊤ ω) :
    Differentiable ℝ (pullbackForm σ ω) := by
  intro x
  unfold pullbackForm
  apply DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
  · exact ((hω.comp σ.smooth).differentiable
      (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt
  · have hfderiv : ContDiff ℝ ⊤ (fderiv ℝ σ.toFun) :=
      σ.smooth.fderiv_right (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
    exact (hfderiv.differentiable (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt

/-- Each coordinate coefficient of the pullback form is smooth.

The i-th coefficient is `fun x => ω(σ x)(fun k => fderiv ℝ σ x (eₖ))`.
This is proved using `contDiff_multilinearMap_apply_of_contDiff` by converting
the alternating map to a multilinear map and verifying smoothness of all components. -/
theorem toCoordNForm_pullback_isSmooth {n : ℕ} (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ ⊤ ω) :
    CubeStokes.IsSmooth (CubeStokes.toCoordNForm (pullbackForm σ ω)) := by
  intro i
  -- The i-th coefficient is:
  -- fun x => (pullbackForm σ ω x)(fun k => Pi.single (Fin.succAbove i k) 1)
  -- = fun x => ω(σ x)(fun k => fderiv ℝ σ x (Pi.single (Fin.succAbove i k) 1))
  change ContDiff ℝ ⊤ (fun x =>
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
    have hfderiv : ContDiff ℝ ⊤ (fderiv ℝ σ.toFun) :=
      σ.smooth.fderiv_right (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
    exact hfderiv.clm_apply contDiff_const

end SingularCubeStokes

end
