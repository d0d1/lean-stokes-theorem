/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic

/-!
# Pullback of Differential Forms

Defines the Euclidean pullback of differential forms using mathlib's
`ContinuousAlternatingMap.compContinuousLinearMap`.
-/

noncomputable section

namespace DiffForm

variable {m n k : ℕ}

/-- Pull back a `k`-form on `ℝᵐ` along a map `f : ℝⁿ → ℝᵐ`.

At `x`, this is `(f^*η)_x = η_{f x} ∘ Df_x`.  The definition is algebraic in
`fderiv`; differentiability hypotheses are added to theorems that need semantic
smooth pullbacks. -/
def pullback (f : ℝSpace n → ℝSpace m) (η : DiffForm m k) : DiffForm n k :=
  fun x => (η (f x)).compContinuousLinearMap (fderiv ℝ f x)

@[simp] theorem pullback_apply (f : ℝSpace n → ℝSpace m) (η : DiffForm m k)
    (x : ℝSpace n) :
    pullback f η x = (η (f x)).compContinuousLinearMap (fderiv ℝ f x) :=
  rfl

/-- Pullback of a smooth differential form along a smooth map is differentiable as an
alternating-map-valued function. -/
theorem pullback_differentiable (f : ℝSpace n → ℝSpace m) (η : DiffForm m k)
    (hf : ContDiff ℝ ⊤ f) (hη : ContDiff ℝ ⊤ η) :
    Differentiable ℝ (pullback f η) := by
  intro x
  unfold pullback
  apply DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
  · exact ((hη.comp hf).differentiable
      (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt
  · have hfderiv : ContDiff ℝ ⊤ (fderiv ℝ f) :=
      hf.fderiv_right (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
    exact (hfderiv.differentiable
      (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt

end DiffForm

end
