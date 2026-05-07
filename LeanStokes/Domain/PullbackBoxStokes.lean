/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.PullbackSmooth
import LeanStokes.Domain.BoxStokes
import LeanStokes.DiffForm.Localization

/-!
# Pullback Form Half-Space Box Stokes

This module applies local half-space box Stokes to smooth pullbacks.  It remains
local to boxes and keeps the explicit artificial-face vanishing hypothesis; it
does not state chart-local or global domain Stokes.
-/

noncomputable section

open Set

namespace CubeStokes

variable {m n : ℕ}

/-- Local half-space box Stokes for the pullback of a smooth form along a smooth map, under
explicit pointwise vanishing of all artificial box-face integrands of the pulled-back form. -/
theorem halfSpaceBoxStokes_pullback_of_vanishesOnArtificialFaces
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hf : ContDiff ℝ ⊤ f) (hω : ContDiff ℝ ⊤ ω)
    (hvanish : VanishesOnBoxArtificialFaces (DiffForm.pullback f ω) a b) :
    DiffForm.integral (DiffForm.pullback f (DiffForm.extd ω)) (Icc a b) =
      SmoothDomain.halfSpaceBoundaryIntegral n (DiffForm.pullback f ω)
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1)))) := by
  rw [← DiffForm.extd_pullback f ω hω hf]
  exact halfSpaceBoxStokes_of_vanishesOnArtificialFaces_of_differentiable
    (DiffForm.pullback f ω) a b hle ha0
    (DiffForm.pullback_differentiable f ω hf hω)
    (CubeStokes.toCoordNForm_pullback_isSmooth f ω hf hω)
    hvanish

/-- Local half-space box Stokes for a smooth pullback when the pulled-back form is pointwise
zero on every artificial face point-set. -/
theorem halfSpaceBoxStokes_pullback_of_eq_zero_on_boxArtificialFaces
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hf : ContDiff ℝ ⊤ f) (hω : ContDiff ℝ ⊤ ω)
    (hzero : ∀ y ∈ boxArtificialFaces a b, DiffForm.pullback f ω y = 0) :
    DiffForm.integral (DiffForm.pullback f (DiffForm.extd ω)) (Icc a b) =
      SmoothDomain.halfSpaceBoundaryIntegral n (DiffForm.pullback f ω)
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1)))) :=
  halfSpaceBoxStokes_pullback_of_vanishesOnArtificialFaces f ω a b hle ha0 hf hω
    (vanishesOnBoxArtificialFaces_of_eq_zero_on_boxArtificialFaces
      (DiffForm.pullback f ω) a b hzero)

/-- Local half-space box Stokes for a smooth pullback when the pulled-back form's pointwise
support is disjoint from every artificial face point-set. -/
theorem halfSpaceBoxStokes_pullback_of_disjoint_support_boxArtificialFaces
    (f : ℝSpace (n + 1) → ℝSpace m) (ω : DiffForm m n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hf : ContDiff ℝ ⊤ f) (hω : ContDiff ℝ ⊤ ω)
    (hdisj : Disjoint (Function.support (DiffForm.pullback f ω)) (boxArtificialFaces a b)) :
    DiffForm.integral (DiffForm.pullback f (DiffForm.extd ω)) (Icc a b) =
      SmoothDomain.halfSpaceBoundaryIntegral n (DiffForm.pullback f ω)
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1)))) :=
  halfSpaceBoxStokes_pullback_of_vanishesOnArtificialFaces f ω a b hle ha0 hf hω
    (vanishesOnBoxArtificialFaces_of_disjoint_support_boxArtificialFaces
      (DiffForm.pullback f ω) a b hdisj)

/-- Local half-space box Stokes for a localized pullback form when the pulled-back scalar support is
disjoint from the artificial box faces. -/
theorem halfSpaceBoxStokes_pullback_fsmul_of_disjoint_support_scalar_boxArtificialFaces
    (f : ℝSpace (n + 1) → ℝSpace m) (χ : ℝSpace m → ℝ) (ω : DiffForm m n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hf : ContDiff ℝ ⊤ f) (hχ : ContDiff ℝ ⊤ χ) (hω : ContDiff ℝ ⊤ ω)
    (hdisj : Disjoint (Function.support (χ ∘ f)) (boxArtificialFaces a b)) :
    DiffForm.integral (DiffForm.pullback f (DiffForm.extd (DiffForm.fsmul χ ω))) (Icc a b) =
      SmoothDomain.halfSpaceBoundaryIntegral n (DiffForm.pullback f (DiffForm.fsmul χ ω))
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1)))) := by
  have hχω : ContDiff ℝ ⊤ (DiffForm.fsmul χ ω) :=
    DiffForm.isSmooth_fsmul hχ hω
  have hdisj_form :
      Disjoint (Function.support (DiffForm.pullback f (DiffForm.fsmul χ ω)))
        (boxArtificialFaces a b) := by
    rw [DiffForm.pullback_fsmul]
    exact DiffForm.disjoint_support_fsmul_of_disjoint_support_left hdisj
  exact halfSpaceBoxStokes_pullback_of_disjoint_support_boxArtificialFaces
    f (DiffForm.fsmul χ ω) a b hle ha0 hf hχω hdisj_form

end CubeStokes

end
