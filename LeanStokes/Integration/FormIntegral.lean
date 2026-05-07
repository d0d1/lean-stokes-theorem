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
open scoped ENNReal

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

end DiffForm

end
