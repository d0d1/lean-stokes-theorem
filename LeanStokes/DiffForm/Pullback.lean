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

end DiffForm

end
