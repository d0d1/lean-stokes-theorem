/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Bridge
import LeanStokes.DiffForm.Pullback
import LeanStokes.DiffForm.SmoothEval

/-!
# Smooth Coordinate Coefficients of Pullback Forms

This module proves the coordinate-coefficient smoothness of the project
pullback `DiffForm.pullback`.  It is a regularity bridge for applying the
split-hypothesis cubical Stokes theorem to pulled-back forms; it does not state
any Stokes theorem.
-/

noncomputable section

open scoped Topology

namespace CubeStokes

variable {m n : ℕ}

/-- Pulling back a smooth form along a smooth map has smooth coordinate coefficients. -/
theorem toCoordNForm_pullback_isSmooth
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    IsSmooth (toCoordNForm (DiffForm.pullback f ω)) := by
  intro i
  unfold DiffForm.pullback toCoordNForm
  change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    (ω (f x)) (fun k => fderiv ℝ f x (Pi.single (Fin.succAbove i k) 1)))
  have h_eq : (fun x =>
      (ω (f x)) (fun k => fderiv ℝ f x (Pi.single (Fin.succAbove i k) 1))) =
      (fun x => ((ω (f x)).toContinuousMultilinearMap)
        (fun k => fderiv ℝ f x (Pi.single (Fin.succAbove i k) 1))) := by
    ext x
    rfl
  rw [h_eq]
  apply DiffForm.contDiff_multilinearMap_apply_of_contDiff n
  · exact (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
      ).contDiff.comp (hω.comp hf)
  · intro k
    have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
      hf.fderiv_right (by simp)
    exact hfderiv.clm_apply contDiff_const

/-- Local coordinate-coefficient regularity of a pullback form.

Both hypotheses are ambient `ContDiffAt` assumptions at the relevant points.
For chart applications, membership in a chart target must first be converted
into such a pointwise ambient smoothness statement for the chosen representative
of the inverse chart. -/
theorem toCoordNForm_pullback_contDiffAt
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    {x : ℝSpace (n + 1)}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (hω : ContDiffAt ℝ (⊤ : ℕ∞) ω (f x))
    (i : Fin (n + 1)) :
    ContDiffAt ℝ (⊤ : ℕ∞) ((toCoordNForm (DiffForm.pullback f ω)) i) x := by
  unfold DiffForm.pullback toCoordNForm
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun x =>
    (ω (f x)) (fun k => fderiv ℝ f x (Pi.single (Fin.succAbove i k) 1))) x
  have h_eq : (fun x =>
      (ω (f x)) (fun k => fderiv ℝ f x (Pi.single (Fin.succAbove i k) 1))) =
      (fun x => ((ω (f x)).toContinuousMultilinearMap)
        (fun k => fderiv ℝ f x (Pi.single (Fin.succAbove i k) 1))) := by
    ext x
    rfl
  rw [h_eq]
  apply DiffForm.contDiffAt_multilinearMap_apply_of_contDiffAt n
  · exact (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
      ).contDiff.contDiffAt.comp x (hω.comp x hf)
  · intro k
    have hfderiv : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ f) x :=
      hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact hfderiv.clm_apply contDiffAt_const

end CubeStokes

end
