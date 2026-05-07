/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.PullbackSmooth
import LeanStokes.Domain.BoxStokes

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

end CubeStokes

end
