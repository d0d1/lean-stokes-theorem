/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatchModelIntegral
import LeanStokes.Domain.BoxStokes

/-!
# Boundary Chart Patch Stokes Bridges

This module combines half-space box Stokes in model coordinates with the
patch-local boundary integral bridge.  The theorem below is still an analytic
chart-symm box bridge: smoothness of the total model pullback and artificial-face
vanishing remain explicit hypotheses.  It does not define a chart-independent
boundary integral, solve localization, or prove global domain Stokes.
-/

noncomputable section

open Set MeasureTheory

namespace SmoothDomain
namespace BoundaryChartPatch

variable {n : ℕ} {M : SmoothDomain (n + 1)} {x : ℝSpace (n + 1)}

/-- Half-space box Stokes through an inverse boundary-flattening chart, with explicit analytic
regularity and artificial-face hypotheses for the model pullback form. -/
theorem halfSpaceBoxStokes_chart_symm_of_vanishesOnArtificialFaces_of_differentiable
    (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hω : ContDiff ℝ ⊤ ω)
    (hmodel_diff :
      Differentiable ℝ (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω))
    (hcoord : CubeStokes.IsSmooth (CubeStokes.toCoordNForm
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω)))
    (hdiffBox : ∀ z ∈ Icc a b,
      ContDiffAt ℝ ⊤ (M.halfSpaceFlatteningChart P.i x P.h).symm z)
    (hvanish : CubeStokes.VanishesOnBoxArtificialFaces
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω) a b)
    (hSsub :
      Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
          (b ∘ Fin.succAbove (0 : Fin (n + 1))) ⊆ P.localCoordDomain) :
    DiffForm.integral
        (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm (DiffForm.extd ω))
        (Icc a b) =
      P.sign.domainSign * P.localBoundaryIntegral ω
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1)))) hSsub := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  let S : Set (ℝSpace n) :=
    Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
        (b ∘ Fin.succAbove (0 : Fin (n + 1)))
  have hbulk :
      DiffForm.integral (DiffForm.pullback e.symm (DiffForm.extd ω)) (Icc a b) =
        DiffForm.integral (DiffForm.extd (DiffForm.pullback e.symm ω)) (Icc a b) := by
    exact DiffForm.integral_congr
      (DiffForm.pullback e.symm (DiffForm.extd ω))
      (DiffForm.extd (DiffForm.pullback e.symm ω)) measurableSet_Icc
      (fun z hz =>
        (DiffForm.extd_pullback_apply e.symm ω z
          ((hω.differentiable (by simp : (⊤ : WithTop ℕ∞) ≠ 0)) (e.symm z))
          (by simpa [e] using hdiffBox z hz)).symm)
  have hbox :
      DiffForm.integral (DiffForm.extd (DiffForm.pullback e.symm ω)) (Icc a b) =
        halfSpaceBoundaryIntegral n (DiffForm.pullback e.symm ω) S := by
    simpa [e, S] using
      CubeStokes.halfSpaceBoxStokes_of_vanishesOnArtificialFaces_of_differentiable
        (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω)
        a b hle ha0 hmodel_diff hcoord hvanish
  have hboundary :
      halfSpaceBoundaryIntegral n (DiffForm.pullback e.symm ω) S =
        P.sign.domainSign * P.localBoundaryIntegral ω S hSsub := by
    simpa [e, S] using
      P.halfSpaceBoundaryIntegral_pullback_chart_symm_eq_domainSign_mul_localBoundaryIntegral
        (ω := ω) (S := S) measurableSet_Icc hSsub
  rw [show (M.halfSpaceFlatteningChart P.i x P.h).symm = e.symm by rfl]
  rw [hbulk, hbox, hboundary]

end BoundaryChartPatch
end SmoothDomain

end
