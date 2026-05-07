/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Unified
import LeanStokes.Domain.BoundaryIntegral
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

/-- Inserting zero in the first coordinate is the standard half-space boundary parametrization. -/
@[simp] theorem insertNth_zero_zero_eq_halfSpaceBoundaryParam (n : ℕ) (y : ℝSpace n) :
    Fin.insertNth (0 : Fin (n + 1)) (0 : ℝ) y =
      SmoothDomain.halfSpaceBoundaryParam n y := by
  ext j
  cases j using Fin.cases with
  | zero =>
      simp
  | succ k =>
      simp [SmoothDomain.halfSpaceBoundaryParam]

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

/-- The low `x₀ = 0` cubical face contribution is the standard half-space boundary integral.

This identifies only the true half-space boundary face of a box whose first lower coordinate is
zero.  The other box faces are artificial for local half-space Stokes and are not treated here. -/
theorem neg_lowFaceIntegral_zero_eq_halfSpaceBoundaryIntegral
    (ω : DiffForm (n + 1) n) (a b : ℝSpace (n + 1))
    (ha0 : a (0 : Fin (n + 1)) = 0) :
    - (∫ y in Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
                    (b ∘ Fin.succAbove (0 : Fin (n + 1))),
        CubeStokes.signedCoeff (CubeStokes.toCoordNForm ω) (0 : Fin (n + 1))
          (Fin.insertNth (0 : Fin (n + 1)) (a (0 : Fin (n + 1))) y)) =
      SmoothDomain.halfSpaceBoundaryIntegral n ω
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1)))) := by
  rw [SmoothDomain.halfSpaceBoundaryIntegral_eq_neg, DiffForm.integral]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro y _
  rw [SmoothDomain.topCoeff_halfSpaceBoundaryPullback]
  have hpoint : Fin.cons (0 : ℝ) y = SmoothDomain.halfSpaceBoundaryParam n y := by
    ext j
    cases j using Fin.cases with
    | zero =>
        simp [SmoothDomain.halfSpaceBoundaryParam]
    | succ k =>
        simp [SmoothDomain.halfSpaceBoundaryParam]
  have hframe :
      (fun k : Fin n => Pi.single k.succ (1 : ℝ)) =
        SmoothDomain.halfSpaceBoundaryFrame n := by
    funext k
    ext j
    cases j using Fin.cases with
    | zero =>
        simp [SmoothDomain.halfSpaceBoundaryFrame]
    | succ l =>
        simp [SmoothDomain.halfSpaceBoundaryFrame]
  simp [CubeStokes.signedCoeff, CubeStokes.toCoordNForm, ha0, hpoint, hframe]

end CubeStokes

end
