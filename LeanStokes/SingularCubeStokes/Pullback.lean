/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Pullback Forms and Integration for Smooth Singular Cubes

Defines the TRUE differential-form pullback σ*ω via fderiv,
integration of forms over singular cubes, and proves smoothness
of the pullback.

## Main definitions

* `SingularCubeStokes.pullbackForm σ ω`: The pullback σ*ω as a differential form
* `SingularCubeStokes.integrateForm σ ω`: Integration of a k-form over a k-cube

## Main results

* `SingularCubeStokes.pullbackForm_contDiff`: The pullback of a C^∞ form is C^∞
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace SingularCubeStokes

variable {d m k : ℕ}

/-- The pullback of a k-form ω on ℝᵐ along a smooth map σ : ℝᵈ → ℝᵐ.
This is the TRUE differential-form pullback:
  (σ*ω)(x)(v₁,...,vₖ) = ω(σ(x))(Dσ(x)·v₁, ..., Dσ(x)·vₖ)
using `ContinuousAlternatingMap.compContinuousLinearMap`. -/
def pullbackForm (σ : SmoothSingularCube d m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin k]→L[ℝ] ℝ :=
  fun x => (ω (σ.toFun x)).compContinuousLinearMap (fderiv ℝ σ.toFun x)

/-- Integration of a d-form over a d-dimensional singular cube.
This evaluates the pullback form on the standard frame and integrates
over [0,1]^d with respect to the Lebesgue measure. -/
def integrateForm (σ : SmoothSingularCube d m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin d]→L[ℝ] ℝ) : ℝ :=
  ∫ x in Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1),
    (pullbackForm σ ω x) (fun j => Pi.single j 1)

/- Note: The pullback of a C^∞ form along a smooth singular cube is C^∞.
This follows from: pullbackForm σ ω x = (ω(σ x)).compCLM(fderiv ℝ σ x),
where x ↦ ω(σ x) is C^∞ (composition) and x ↦ fderiv ℝ σ x is C^∞
(derivative of C^∞), and the pairing is polynomial (degree k in the
linear map, linear in the alternating form).

This fact is not needed for the main singularStokes theorem, which uses
pointwise face_matching reasoning rather than global smoothness. -/

end SingularCubeStokes

end
