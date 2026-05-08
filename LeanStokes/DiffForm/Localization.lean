/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Pullback
import LeanStokes.Integration.FormIntegral
import Mathlib.Topology.Algebra.Support

/-!
# Differential Form Localization

This module contains the pointwise scalar-function multiplication API needed for
localizing forms by bump functions and partitions of unity.  It does not prove
an exterior-derivative product rule or construct partitions of unity.
-/

noncomputable section

open Topology Filter Set
open scoped BigOperators Topology

namespace DiffForm

variable {d n : ℕ}

/-- Pointwise multiplication of a differential form by a scalar function. -/
def fsmul (f : ℝSpace d → ℝ) (ω : DiffForm d n) : DiffForm d n :=
  f • ω

@[simp] theorem fsmul_apply (f : ℝSpace d → ℝ) (ω : DiffForm d n) (x : ℝSpace d) :
    fsmul f ω x = f x • ω x :=
  rfl

@[simp] theorem fsmul_zero_left (ω : DiffForm d n) :
    fsmul (fun _ : ℝSpace d => 0) ω = 0 := by
  funext x
  simp [fsmul]

@[simp] theorem fsmul_one_left (ω : DiffForm d n) :
    fsmul (fun _ : ℝSpace d => 1) ω = ω := by
  funext x
  simp [fsmul]

@[simp] theorem fsmul_zero_right (f : ℝSpace d → ℝ) :
    fsmul f (0 : DiffForm d n) = 0 := by
  funext x
  simp [fsmul]

theorem fsmul_add_left (f g : ℝSpace d → ℝ) (ω : DiffForm d n) :
    fsmul (fun x => f x + g x) ω = fsmul f ω + fsmul g ω := by
  funext x
  simp [fsmul, add_smul]

theorem fsmul_add_right (f : ℝSpace d → ℝ) (ω₁ ω₂ : DiffForm d n) :
    fsmul f (ω₁ + ω₂) = fsmul f ω₁ + fsmul f ω₂ := by
  funext x
  simp [fsmul, smul_add]

/-- Multiplication by a finite sum of scalar functions is the finite sum of localized forms. -/
theorem fsmul_finset_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → ℝSpace d → ℝ) (ω : DiffForm d n) :
    fsmul (fun x => ∑ i ∈ s, f i x) ω = ∑ i ∈ s, fsmul (f i) ω := by
  funext x
  simp [fsmul, Finset.sum_smul]

/-- If a finite family of scalar functions sums to one on `U`, the corresponding localized forms
sum back to the original form on `U`. -/
theorem finset_sum_fsmul_eqOn_of_sum_eq_one {ι : Type*} (s : Finset ι)
    (f : ι → ℝSpace d → ℝ) (ω : DiffForm d n) {U : Set (ℝSpace d)}
    (h : ∀ x ∈ U, (∑ i ∈ s, f i x) = 1) :
    Set.EqOn (∑ i ∈ s, fsmul (f i) ω) ω U := by
  intro x hx
  rw [← congr_fun (fsmul_finset_sum_left s f ω) x]
  simp [fsmul, h x hx]

/-- If scalar weights sum to one in a neighborhood of `x`, the corresponding finite sum of
localized forms agrees with the original form in a neighborhood of `x`. -/
theorem finset_sum_fsmul_eventuallyEq_of_sum_eventuallyEq_one {ι : Type*} (s : Finset ι)
    (f : ι → ℝSpace d → ℝ) (ω : DiffForm d n) {x : ℝSpace d}
    (h : (fun y => ∑ i ∈ s, f i y) =ᶠ[𝓝 x] fun _ => 1) :
    (∑ i ∈ s, fsmul (f i) ω) =ᶠ[𝓝 x] ω := by
  filter_upwards [h] with y hy
  rw [← congr_fun (fsmul_finset_sum_left s f ω) y]
  simp [fsmul, hy]

/-- Setwise version of `finset_sum_fsmul_eventuallyEq_of_sum_eventuallyEq_one`. -/
theorem finset_sum_fsmul_eventuallyEq_on_of_sum_eventuallyEq_one {ι : Type*}
    (s : Finset ι) (f : ι → ℝSpace d → ℝ) (ω : DiffForm d n) {S : Set (ℝSpace d)}
    (h : ∀ x ∈ S, (fun y => ∑ i ∈ s, f i y) =ᶠ[𝓝 x] fun _ => 1) :
    ∀ x ∈ S, (∑ i ∈ s, fsmul (f i) ω) =ᶠ[𝓝 x] ω := by
  intro x hx
  exact finset_sum_fsmul_eventuallyEq_of_sum_eventuallyEq_one s f ω (h x hx)

/-- Scalar localization is zero at a point where the scalar function is zero. -/
theorem fsmul_eq_zero_of_left_eq_zero {f : ℝSpace d → ℝ} {ω : DiffForm d n}
    {x : ℝSpace d} (hf : f x = 0) :
    fsmul f ω x = 0 := by
  simp [fsmul, hf]

/-- If the scalar factor is locally zero, then the localized form is locally zero. -/
theorem fsmul_eventuallyEq_zero_of_left_eventuallyEq_zero
    {f : ℝSpace d → ℝ} {ω : DiffForm d n} {x : ℝSpace d}
    (hf : f =ᶠ[𝓝 x] fun _ => 0) :
    fsmul f ω =ᶠ[𝓝 x] (0 : DiffForm d n) := by
  filter_upwards [hf] with y hy
  exact fsmul_eq_zero_of_left_eq_zero (ω := ω) hy

/-- The support of a scalar-localized form is contained in the support of the scalar factor. -/
theorem support_fsmul_subset_left (f : ℝSpace d → ℝ) (ω : DiffForm d n) :
    Function.support (fsmul f ω) ⊆ Function.support f := by
  intro x hx
  by_contra hfx
  have hfzero : f x = 0 := by
    by_contra hfne
    exact hfx hfne
  exact hx (fsmul_eq_zero_of_left_eq_zero (ω := ω) hfzero)

/-- Disjointness of the scalar support from a set implies disjointness of the localized-form
support from that set. -/
theorem disjoint_support_fsmul_of_disjoint_support_left
    {f : ℝSpace d → ℝ} {ω : DiffForm d n} {T : Set (ℝSpace d)}
    (h : Disjoint (Function.support f) T) :
    Disjoint (Function.support (fsmul f ω)) T :=
  h.mono_left (support_fsmul_subset_left f ω)

/-- Pullback commutes with scalar localization, with the scalar pulled back as a function. -/
theorem pullback_fsmul {m d n : ℕ}
    (g : ℝSpace d → ℝSpace m) (f : ℝSpace m → ℝ) (ω : DiffForm m n) :
    pullback g (fsmul f ω) = fsmul (f ∘ g) (pullback g ω) := by
  funext x
  ext v
  simp [pullback, fsmul, Function.comp_def]

@[simp] theorem topCoeff_fsmul (f : ℝSpace d → ℝ) (ω : DiffForm d d) (x : ℝSpace d) :
    topCoeff (fsmul f ω) x = f x * topCoeff ω x := by
  simp [fsmul, topCoeff, smul_eq_mul]

/-- Pointwise scalar multiplication by a continuous scalar function preserves continuity of
forms. -/
theorem continuous_fsmul {f : ℝSpace d → ℝ} {ω : DiffForm d n}
    (hf : Continuous f) (hω : Continuous ω) :
    Continuous (fsmul f ω) := by
  simpa [fsmul] using hf.smul hω

/-- Pointwise scalar multiplication by a smooth scalar function preserves smoothness of forms. -/
theorem isSmooth_fsmul {f : ℝSpace d → ℝ} {ω : DiffForm d n}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hω : IsSmooth ω) :
    IsSmooth (fsmul f ω) := by
  simpa [IsSmooth, fsmul] using hf.smul hω

/-- If the scalar function has compact support, then its pointwise product with any form has
compact support. -/
theorem hasCompactSupport_fsmul_of_left {f : ℝSpace d → ℝ} {ω : DiffForm d n}
    (hf : _root_.HasCompactSupport f) :
    DiffForm.HasCompactSupport (fsmul f ω) := by
  simpa [fsmul, DiffForm.HasCompactSupport] using
    (_root_.HasCompactSupport.smul_right (f' := ω) hf)

/-- If the form has compact support, then multiplying it by any scalar function preserves compact
support. -/
theorem hasCompactSupport_fsmul_of_right {f : ℝSpace d → ℝ} {ω : DiffForm d n}
    (hω : DiffForm.HasCompactSupport ω) :
    DiffForm.HasCompactSupport (fsmul f ω) := by
  simpa [fsmul, DiffForm.HasCompactSupport] using
    (_root_.HasCompactSupport.smul_left (f := f) hω)

end DiffForm

end
