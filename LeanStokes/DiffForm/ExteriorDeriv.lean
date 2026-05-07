/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic
import LeanStokes.DiffForm.Pullback

/-!
# Exterior Derivative

This file wraps mathlib's `extDeriv` for our `DiffForm` alias,
and provides the key properties needed for Stokes' theorem:

* `DiffForm.extd` — the exterior derivative of a form
* `DiffForm.extd_extd` — d ∘ d = 0
* Linearity of the exterior derivative

We rely entirely on mathlib's `extDeriv` and do not redefine it.
-/

noncomputable section

open Topology Filter Set

namespace DiffForm

variable {d n : ℕ} {x : ℝSpace d}

/-- The exterior derivative of a differential form, wrapping mathlib's `extDeriv`. -/
def extd (ω : DiffForm d n) : DiffForm d (n + 1) :=
  fun x => _root_.extDeriv ω x

/-- The exterior derivative within a set. -/
def extdWithin (ω : DiffForm d n) (s : Set (ℝSpace d)) :
    DiffForm d (n + 1) :=
  fun x => _root_.extDerivWithin ω s x

/-- d ∘ d = 0 for smooth forms. -/
theorem extd_extd (ω : DiffForm d n) (hω : IsSmooth ω) :
    extd (extd ω) = 0 := by
  unfold extd IsSmooth at *
  funext x
  have h : ContDiffAt ℝ ⊤ ω x := hω.contDiffAt
  exact _root_.extDeriv_extDeriv_apply h le_top

/-- Linearity: d(ω₁ + ω₂) = dω₁ + dω₂ for differentiable forms. -/
theorem extd_add (ω₁ ω₂ : DiffForm d n)
    (h₁ : DifferentiableAt ℝ ω₁ x) (h₂ : DifferentiableAt ℝ ω₂ x) :
    extd (ω₁ + ω₂) x = extd ω₁ x + extd ω₂ x := by
  unfold extd
  exact _root_.extDeriv_add h₁ h₂

/-- Linearity: d(c • ω) = c • dω. -/
theorem extd_smul (c : ℝ) (ω : DiffForm d n) :
    extd (c • ω) x = c • extd ω x := by
  unfold extd
  change _root_.extDeriv (fun y => c • ω y) x = c • _root_.extDeriv ω x
  exact _root_.extDeriv_smul c ω

/-- The exterior derivative commutes pointwise with pullback. -/
theorem extd_pullback_apply {m : ℕ} (f : ℝSpace m → ℝSpace d) (ω : DiffForm d n)
    (x : ℝSpace m)
    (hω : DifferentiableAt ℝ ω (f x))
    (hf : ContDiffAt ℝ ⊤ f x) :
    extd (pullback f ω) x = pullback f (extd ω) x := by
  unfold extd pullback
  exact _root_.extDeriv_pullback hω hf (by simp)

/-- The exterior derivative commutes with smooth pullback. -/
theorem extd_pullback {m : ℕ} (f : ℝSpace m → ℝSpace d) (ω : DiffForm d n)
    (hω : ContDiff ℝ ⊤ ω)
    (hf : ContDiff ℝ ⊤ f) :
    extd (pullback f ω) = pullback f (extd ω) := by
  funext x
  exact extd_pullback_apply f ω x
    ((hω.differentiable (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt)
    hf.contDiffAt

end DiffForm

end
