/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Unified
import LeanStokes.DiffForm.ExteriorDeriv
import LeanStokes.Integration.FormIntegral

/-!
# Box Stokes in `DiffForm.integral` Vocabulary

This module restates the existing cubical Stokes theorem for full boxes using
the project `DiffForm.extd` and `DiffForm.integral` APIs on the bulk side.  It
does not define half-box Stokes, artificial-face vanishing, chart boundary
integrals, or domain Stokes.
-/

noncomputable section

open Set MeasureTheory

namespace CubeStokes

variable {n : ℕ}

/-- Box Stokes with the bulk side expressed as `DiffForm.integral (DiffForm.extd ω)`.

The boundary side is still the existing cubical coordinate-boundary integral; later local-domain
infrastructure can bridge that side to boundary charts under additional hypotheses. -/
theorem boxStokes_diffForm (ω : DiffForm (n + 1) n)
    (a b : ℝSpace (n + 1)) (hle : a ≤ b)
    (hω : ContDiff ℝ ⊤ ω) :
    DiffForm.integral (DiffForm.extd ω) (Icc a b) =
      CubeStokes.bdryIntegral (CubeStokes.toCoordNForm ω) a b := by
  simpa [DiffForm.integral, DiffForm.topCoeff, DiffForm.extd, DiffForm.stdBasis] using
    CubeStokes.stokes_extDeriv_smooth ω a b hle hω

end CubeStokes

end
