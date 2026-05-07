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

open scoped Topology

namespace DiffForm

variable {m n k l : ℕ}

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

/-- Pointwise congruence for pullbacks.  Equality of map values alone is not sufficient:
`DiffForm.pullback` also depends on the total Fréchet derivative. -/
theorem pullback_congr_apply {f g : ℝSpace n → ℝSpace m} (η : DiffForm m k)
    {x : ℝSpace n}
    (hval : f x = g x) (hderiv : fderiv ℝ f x = fderiv ℝ g x) :
    pullback f η x = pullback g η x := by
  simp [pullback, hval, hderiv]

/-- Pullbacks agree on a set when both the maps and their total derivatives agree there. -/
theorem pullback_congr_on {f g : ℝSpace n → ℝSpace m} (η : DiffForm m k)
    {S : Set (ℝSpace n)}
    (hval : ∀ x ∈ S, f x = g x)
    (hderiv : ∀ x ∈ S, fderiv ℝ f x = fderiv ℝ g x) :
    ∀ x ∈ S, pullback f η x = pullback g η x := by
  intro x hx
  exact pullback_congr_apply η (hval x hx) (hderiv x hx)

/-- Pullbacks agree at a point when the maps agree in a neighborhood of that point. -/
theorem pullback_congr_of_eventuallyEq {f g : ℝSpace n → ℝSpace m}
    (η : DiffForm m k) {x : ℝSpace n} (h : f =ᶠ[𝓝 x] g) :
    pullback f η x = pullback g η x :=
  pullback_congr_apply η h.self_of_nhds h.fderiv_eq

/-- Pointwise composition law for differential-form pullback. -/
theorem pullback_comp_apply
    (f : ℝSpace m → ℝSpace n) (g : ℝSpace k → ℝSpace m)
    (η : DiffForm n l) {x : ℝSpace k}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    pullback g (pullback f η) x = pullback (f ∘ g) η x := by
  unfold pullback
  rw [fderiv_comp x hf hg]
  ext v
  simp [Function.comp_def]

/-- Composition law for differential-form pullback. -/
theorem pullback_comp
    (f : ℝSpace m → ℝSpace n) (g : ℝSpace k → ℝSpace m)
    (η : DiffForm n l)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pullback g (pullback f η) = pullback (f ∘ g) η := by
  funext x
  exact pullback_comp_apply f g η (hf (g x)) (hg x)

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
