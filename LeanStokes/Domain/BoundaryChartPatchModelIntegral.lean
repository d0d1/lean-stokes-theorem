/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatchIntegral
import LeanStokes.Domain.BoundaryChartPatchSmooth
import LeanStokes.Domain.BoundaryIntegral

/-!
# Boundary Chart Patch Model Integral Bridge

This module relates the standard half-space boundary model integral of the
inverse flattening chart to the patch-local signed boundary integral.  The bridge
is local to a certified coordinate set and does not assert chart-local Stokes,
chart-independent boundary integration, or a global domain theorem.
-/

noncomputable section

namespace SmoothDomain
namespace BoundaryChartPatch

variable {n : ℕ} {M : SmoothDomain (n + 1)} {x : ℝSpace (n + 1)}

/-- On a certified patch coordinate set, the model half-space boundary integral of the inverse
flattening-chart pullback agrees with the patch-local boundary integral up to the ambient
orientation sign of the flattening chart. -/
theorem halfSpaceBoundaryIntegral_pullback_chart_symm_eq_domainSign_mul_localBoundaryIntegral
    (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    {S : Set (ℝSpace n)} (hSmeas : MeasurableSet S) (hSsub : S ⊆ P.localCoordDomain) :
    halfSpaceBoundaryIntegral n
        (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω) S =
      P.sign.domainSign * P.localBoundaryIntegral ω S hSsub := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  have hdiff : ∀ y ∈ S, DifferentiableAt ℝ e.symm (halfSpaceBoundaryParam n y) := by
    intro y hy
    have hyP : y ∈ P.localCoordDomain := hSsub hy
    have hz : halfSpaceBoundaryParam n y ∈ e.target := by
      simpa [e, boundaryChartCoordDomain] using hyP.1
    have hp : e.symm (halfSpaceBoundaryParam n y) ∈ P.U := by
      simpa [e, boundaryChartParam] using hyP.2
    exact (P.contDiffAt_halfSpaceFlatteningChart_symm
      (by simpa [e] using hz) (by simpa [e] using hp)).differentiableAt
        (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hmodel :
      halfSpaceBoundaryIntegral n (DiffForm.pullback e.symm ω) S =
        -DiffForm.integral (DiffForm.pullback (e.symm ∘ halfSpaceBoundaryParam n) ω) S :=
    halfSpaceBoundaryIntegral_pullback_eq_neg_integral_pullback_comp_on
      e.symm ω hSmeas hdiff
  have hcomp :
      DiffForm.integral (DiffForm.pullback (e.symm ∘ halfSpaceBoundaryParam n) ω) S =
        DiffForm.integral (boundaryChartPullback M P.i x P.h ω) S := by
    have hfun :
        e.symm ∘ halfSpaceBoundaryParam n = boundaryChartParam M P.i x P.h := by
      funext y
      simp [e, boundaryChartParam]
    rw [hfun]
    rfl
  have hlocal :=
    P.localBoundaryIntegral_eq_neg_domainSign_integral_boundaryChartPullback ω S hSsub
  rw [show (M.halfSpaceFlatteningChart P.i x P.h).symm = e.symm by rfl]
  rw [hmodel, hcomp, hlocal]
  cases P.sign <;> simp [JacobianSign.domainSign]

end BoundaryChartPatch
end SmoothDomain

end
