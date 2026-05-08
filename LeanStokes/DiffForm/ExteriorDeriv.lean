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
open scoped BigOperators Topology

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

@[simp] theorem extd_zero : extd (0 : DiffForm d n) = 0 := by
  funext x
  have h := extd_smul (x := x) (c := 0) (ω := (0 : DiffForm d n))
  simpa using h

/-- Linearity: exterior derivative commutes with finite sums of differentiable forms. -/
theorem extd_finset_sum {ι : Type*} (s : Finset ι) (ω : ι → DiffForm d n)
    (hω : ∀ i ∈ s, DifferentiableAt ℝ (ω i) x) :
    extd (∑ i ∈ s, ω i) x = ∑ i ∈ s, extd (ω i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      have ha_diff : DifferentiableAt ℝ (ω a) x := hω a (by simp)
      have hs_diff : DifferentiableAt ℝ (∑ i ∈ s, ω i) x :=
        DifferentiableAt.sum (fun i hi => hω i (by simp [hi]))
      have hrest : extd (∑ i ∈ s, ω i) x = ∑ i ∈ s, extd (ω i) x :=
        ih (fun i hi => hω i (by simp [hi]))
      rw [Finset.sum_insert ha, extd_add (ω a) (∑ i ∈ s, ω i) ha_diff hs_diff,
        hrest, Finset.sum_insert ha]

/-- Exterior derivatives agree at a point when the forms agree in a neighborhood of that point. -/
theorem extd_congr_of_eventuallyEq {ω₁ ω₂ : DiffForm d n} {x : ℝSpace d}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extd ω₁ x = extd ω₂ x := by
  unfold extd
  exact h.extDeriv_eq

/-- Exterior derivatives agree on a set when the forms agree in a neighborhood of every point of
that set. -/
theorem extd_congr_on_of_eventuallyEq {ω₁ ω₂ : DiffForm d n} {S : Set (ℝSpace d)}
    (h : ∀ x ∈ S, ω₁ =ᶠ[𝓝 x] ω₂) :
    ∀ x ∈ S, extd ω₁ x = extd ω₂ x := by
  intro x hx
  exact extd_congr_of_eventuallyEq (h x hx)

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
