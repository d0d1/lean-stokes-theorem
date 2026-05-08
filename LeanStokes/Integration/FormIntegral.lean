/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Integration of Differential Forms

Defines integration of top-degree forms (n-forms on ℝⁿ) via Lebesgue measure.

## Main definitions

* `DiffForm.topCoeff` — extract scalar coefficient of a top-form
* `DiffForm.integral` — integral of a top-degree form over a measurable set
-/

noncomputable section

open MeasureTheory Topology Filter Set MeasureTheory.Measure
open scoped ENNReal BigOperators

namespace DiffForm

variable {d : ℕ}

/-- The standard basis of ℝᵈ as `Fin d → (Fin d → ℝ)`. -/
def stdBasis : Fin d → ℝSpace d :=
  fun i => Pi.single i 1

/-- Evaluate a top-degree form on the standard basis to get a scalar function.
This extracts the unique coefficient f such that ω = f · dx₁ ∧ ... ∧ dxₙ. -/
def topCoeff (ω : DiffForm d d) : ℝSpace d → ℝ :=
  fun x => ω x stdBasis

@[simp] theorem topCoeff_apply (ω : DiffForm d d) (x : ℝSpace d) :
    topCoeff ω x = ω x stdBasis :=
  rfl

@[simp] theorem topCoeff_add_apply (ω₁ ω₂ : DiffForm d d) (x : ℝSpace d) :
    topCoeff (ω₁ + ω₂) x = topCoeff ω₁ x + topCoeff ω₂ x := by
  simp [topCoeff]

@[simp] theorem topCoeff_smul_apply (c : ℝ) (ω : DiffForm d d) (x : ℝSpace d) :
    topCoeff (c • ω) x = c * topCoeff ω x := by
  simp [topCoeff, smul_eq_mul]

@[simp] theorem topCoeff_finset_sum {ι : Type*} (s : Finset ι)
    (ω : ι → DiffForm d d) (x : ℝSpace d) :
    topCoeff (∑ i ∈ s, ω i) x = ∑ i ∈ s, topCoeff (ω i) x := by
  simp [topCoeff]

/-- Evaluating a continuous top-degree form on the standard basis gives a continuous coefficient. -/
theorem continuous_topCoeff {ω : DiffForm d d} (hω : Continuous ω) :
    Continuous (topCoeff ω) := by
  simpa [topCoeff] using
    (ContinuousAlternatingMap.apply ℝ (ℝSpace d) ℝ (stdBasis (d := d))).continuous.comp hω

/-- A continuous top coefficient is integrable on a compact set. -/
theorem integrableOn_topCoeff_of_isCompact {ω : DiffForm d d} {S : Set (ℝSpace d)}
    (hω : ContinuousOn (topCoeff ω) S) (hS : IsCompact S) :
    IntegrableOn (topCoeff ω) S volume :=
  hω.integrableOn_compact hS

/-- Integration of a top-degree form over a measurable set S ⊆ ℝᵈ.
Defined as ∫ x in S, ω(x)(e₁,...,eₙ) dλ where λ is Lebesgue measure. -/
def integral (ω : DiffForm d d) (S : Set (ℝSpace d)) : ℝ :=
  ∫ x in S, topCoeff ω x ∂volume

/-- Top-form integrals agree when their scalar top coefficients agree on the measurable
integration set. -/
theorem integral_congr_topCoeff (ω₁ ω₂ : DiffForm d d) {S : Set (ℝSpace d)}
    (hS : MeasurableSet S)
    (h : ∀ x ∈ S, topCoeff ω₁ x = topCoeff ω₂ x) :
    integral ω₁ S = integral ω₂ S := by
  unfold integral
  exact MeasureTheory.setIntegral_congr_fun hS h

/-- Top-form integrals agree when the forms agree pointwise on the measurable integration set. -/
theorem integral_congr (ω₁ ω₂ : DiffForm d d) {S : Set (ℝSpace d)}
    (hS : MeasurableSet S) (h : ∀ x ∈ S, ω₁ x = ω₂ x) :
    integral ω₁ S = integral ω₂ S := by
  apply integral_congr_topCoeff ω₁ ω₂ hS
  intro x hx
  simp [topCoeff, h x hx]

/-- If a top form has zero top coefficient on `S \ T` and `T ⊆ S`, then its integral over `S`
equals its integral over `T`.  This is a set-integral restriction lemma and does not require a
separate integrability hypothesis. -/
theorem integral_eq_integral_of_subset_of_topCoeff_eq_zero_on_diff
    (ω : DiffForm d d) {S T : Set (ℝSpace d)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hsub : T ⊆ S)
    (hzero : ∀ x ∈ S, x ∉ T → topCoeff ω x = 0) :
    integral ω S = integral ω T := by
  unfold integral
  rw [← MeasureTheory.integral_indicator hS, ← MeasureTheory.integral_indicator hT]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hxT : x ∈ T
    · have hxS : x ∈ S := hsub hxT
      simp [indicator_of_mem hxS, indicator_of_mem hxT]
    · by_cases hxS : x ∈ S
      · have hz := hzero x hxS hxT
        rw [indicator_of_mem hxS, indicator_of_notMem hxT]
        simpa [topCoeff] using hz
      · simp [indicator_of_notMem hxS, indicator_of_notMem hxT]

/-- If a top form is zero on `S \ T` and `T ⊆ S`, then its integral over `S` equals its integral
over `T`. -/
theorem integral_eq_integral_of_subset_of_eq_zero_on_diff
    (ω : DiffForm d d) {S T : Set (ℝSpace d)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hsub : T ⊆ S)
    (hzero : ∀ x ∈ S, x ∉ T → ω x = 0) :
    integral ω S = integral ω T :=
  integral_eq_integral_of_subset_of_topCoeff_eq_zero_on_diff ω hS hT hsub
    (fun x hxS hxT => by simp [topCoeff, hzero x hxS hxT])

/-- Integration is linear: ∫(ω₁ + ω₂) = ∫ω₁ + ∫ω₂. -/
theorem integral_add (ω₁ ω₂ : DiffForm d d) (S : Set (ℝSpace d))
    (h₁ : IntegrableOn (topCoeff ω₁) S volume)
    (h₂ : IntegrableOn (topCoeff ω₂) S volume) :
    integral (ω₁ + ω₂) S = integral ω₁ S + integral ω₂ S := by
  simp only [integral, topCoeff, Pi.add_apply, ContinuousAlternatingMap.add_apply]
  exact MeasureTheory.integral_add h₁ h₂

/-- Integration is linear: ∫(c • ω) = c • ∫ω. -/
theorem integral_smul (c : ℝ) (ω : DiffForm d d) (S : Set (ℝSpace d)) :
    integral (c • ω) S = c * integral ω S := by
  simp only [integral, topCoeff, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact MeasureTheory.integral_smul c _

/-- Integration commutes with finite sums of top forms, under integrability of each coefficient on
the integration set. -/
theorem integral_finset_sum {ι : Type*} (s : Finset ι) (ω : ι → DiffForm d d)
    (S : Set (ℝSpace d))
    (hω : ∀ i ∈ s, IntegrableOn (topCoeff (ω i)) S volume) :
    integral (∑ i ∈ s, ω i) S = ∑ i ∈ s, integral (ω i) S := by
  simp only [integral, topCoeff_finset_sum]
  exact MeasureTheory.integral_finset_sum s hω

end DiffForm

end
