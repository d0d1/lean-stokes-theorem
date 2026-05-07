/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
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

@[simp] theorem topCoeff_fsmul (f : ℝSpace d → ℝ) (ω : DiffForm d d) (x : ℝSpace d) :
    topCoeff (fsmul f ω) x = f x * topCoeff ω x := by
  simp [fsmul, topCoeff, smul_eq_mul]

/-- Pointwise scalar multiplication by a continuous scalar function preserves continuity of forms. -/
theorem continuous_fsmul {f : ℝSpace d → ℝ} {ω : DiffForm d n}
    (hf : Continuous f) (hω : Continuous ω) :
    Continuous (fsmul f ω) := by
  simpa [fsmul] using hf.smul hω

/-- Pointwise scalar multiplication by a smooth scalar function preserves smoothness of forms. -/
theorem isSmooth_fsmul {f : ℝSpace d → ℝ} {ω : DiffForm d n}
    (hf : ContDiff ℝ ⊤ f) (hω : IsSmooth ω) :
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
