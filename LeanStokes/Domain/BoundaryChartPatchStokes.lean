/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatchModelIntegral
import LeanStokes.CubeStokes.PullbackSmooth
import LeanStokes.Domain.BoxStokes
import LeanStokes.DiffForm.Localization

/-!
# Boundary Chart Patch Stokes Bridges

This module combines half-space box Stokes in model coordinates with the
patch-local boundary integral bridge.  The chart inverse is used only through
ambient `ContDiffAt` hypotheses on the model box; artificial-face vanishing
remains explicit.  It does not define a chart-independent boundary integral,
solve localization, or prove global domain Stokes.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace SmoothDomain
namespace BoundaryChartPatch

variable {n : ℕ} {M : SmoothDomain (n + 1)} {x : ℝSpace (n + 1)}

/-- Half-space box Stokes through an inverse boundary-flattening chart from local chart-inverse
smoothness on the model box and artificial-face vanishing for the model pullback form. -/
theorem halfSpaceBoxStokes_chart_symm_of_vanishesOnArtificialFaces_of_contDiffAt_box
    (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hdiffBox : ∀ z ∈ Icc a b,
      ContDiffAt ℝ (⊤ : ℕ∞) (M.halfSpaceFlatteningChart P.i x P.h).symm z)
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
          ((hω.differentiable (by simp)) (e.symm z))
          (by simpa [e] using hdiffBox z hz)).symm)
  have hbox :
      DiffForm.integral (DiffForm.extd (DiffForm.pullback e.symm ω)) (Icc a b) =
        halfSpaceBoundaryIntegral n (DiffForm.pullback e.symm ω) S := by
    have hmodel_diff_at :
        ∀ z ∈ Icc a b, DifferentiableAt ℝ (DiffForm.pullback e.symm ω) z := by
      intro z hz
      exact DiffForm.pullback_differentiableAt e.symm ω
        (hdiffBox z hz) hω.contDiffAt
    have hcoord :
        ∀ i, ∀ z ∈ Icc a b,
          ContDiffAt ℝ (⊤ : ℕ∞)
            ((CubeStokes.toCoordNForm (DiffForm.pullback e.symm ω)) i) z := by
      intro i z hz
      exact CubeStokes.toCoordNForm_pullback_contDiffAt e.symm ω
        (hdiffBox z hz) hω.contDiffAt i
    simpa [e, S] using
      CubeStokes.halfSpaceBoxStokes_of_diffAt_coordContDiffAt_box_of_vanishes
        (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω)
        a b hle ha0 (by simpa [e] using hmodel_diff_at)
        (by simpa [e] using hcoord) hvanish
  have hboundary :
      halfSpaceBoundaryIntegral n (DiffForm.pullback e.symm ω) S =
        P.sign.domainSign * P.localBoundaryIntegral ω S hSsub := by
    simpa [e, S] using
      P.halfSpaceBoundaryIntegral_pullback_chart_symm_eq_domainSign_mul_localBoundaryIntegral
        (ω := ω) (S := S) measurableSet_Icc hSsub
  rw [show (M.halfSpaceFlatteningChart P.i x P.h).symm = e.symm by rfl]
  rw [hbulk, hbox, hboundary]

/-- Half-space box Stokes through an inverse boundary-flattening chart, using full model-box
containment in the certified patch to discharge inverse-chart smoothness and boundary-coordinate
validity side conditions.  Artificial-face vanishing for the model pullback form
remains explicit. -/
theorem halfSpaceBoxStokes_chart_symm_of_vanishesOnArtificialFaces_of_model_box_subset
    (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hvanish : CubeStokes.VanishesOnBoxArtificialFaces
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω) a b)
    (hboxsub : Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U }) :
    DiffForm.integral
        (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm (DiffForm.extd ω))
        (Icc a b) =
      P.sign.domainSign * P.localBoundaryIntegral ω
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1))))
        (P.tailBox_subset_localCoordDomain_of_model_box_subset a b hle ha0 hboxsub) := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  have hdiffBox : ∀ z ∈ Icc a b, ContDiffAt ℝ (⊤ : ℕ∞) e.symm z := by
    intro z hz
    have hzpatch := hboxsub hz
    exact P.contDiffAt_halfSpaceFlatteningChart_symm
      (by simpa [e] using hzpatch.1) (by simpa [e] using hzpatch.2)
  let hSsub := P.tailBox_subset_localCoordDomain_of_model_box_subset a b hle ha0 hboxsub
  simpa [e, hSsub] using
    P.halfSpaceBoxStokes_chart_symm_of_vanishesOnArtificialFaces_of_contDiffAt_box
      ω a b hle ha0 hω (by simpa [e] using hdiffBox) hvanish hSsub

/-- Local Stokes on an original patch set whose flattening image is a model half-space box.

The theorem combines signed top-form change of variables, the model-box Stokes bridge, and the
local boundary chart integral.  It remains local to one certified patch and keeps the
artificial-face hypothesis for the model pullback explicit. -/
theorem integral_extd_eq_localBoundaryIntegral_of_flattening_image_eq_model_box
    (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    {U : Set (ℝSpace (n + 1))} (a b : ℝSpace (n + 1))
    (hUmeas : MeasurableSet U) (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b)
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hvanish : CubeStokes.VanishesOnBoxArtificialFaces
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω) a b) :
    DiffForm.integral (DiffForm.extd ω) U =
      P.localBoundaryIntegral ω
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1))))
        (P.tailBox_subset_localCoordDomain_of_flattening_image_eq a b hle ha0 hUsub himage) := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  let F : ℝSpace (n + 1) → ℝSpace (n + 1) := M.halfSpaceFlatteningMap P.i
  let η : DiffForm (n + 1) (n + 1) := DiffForm.pullback e.symm (DiffForm.extd ω)
  let S : Set (ℝSpace n) :=
    Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
        (b ∘ Fin.succAbove (0 : Fin (n + 1)))
  let hboxsub := P.model_box_subset_patch_of_flattening_image_eq hUsub himage
  let hSsub := P.tailBox_subset_localCoordDomain_of_model_box_subset a b hle ha0 hboxsub
  have hcov :
      DiffForm.integral η (Icc a b) =
        P.sign.domainSign * DiffForm.integral (DiffForm.pullback F η) U := by
    simpa [η, F, himage] using
      P.integral_image_eq_domainSign_mul_integral_pullback_on hUmeas hUsub η
  have hpull :
      DiffForm.integral (DiffForm.pullback F η) U =
        DiffForm.integral (DiffForm.extd ω) U := by
    exact DiffForm.integral_congr
      (DiffForm.pullback F η) (DiffForm.extd ω) hUmeas
      (fun y hy => by
        have hyP : y ∈ P.U := hUsub hy
        have hysrc : y ∈ e.source := P.subset_source hyP
        have htarget : F y ∈ e.target := by
          simpa [F, e] using e.map_source hysrc
        have hsymmU : e.symm (F y) ∈ P.U := by
          have hleft : e.symm (e y) = y := e.left_inv hysrc
          have hleft' : e.symm (F y) = y := by
            simpa [F, e] using hleft
          rw [hleft']
          exact hyP
        have hsymmdiff : DifferentiableAt ℝ e.symm (F y) :=
          (P.contDiffAt_halfSpaceFlatteningChart_symm
            (by simpa [F, e] using htarget) (by simpa [F, e] using hsymmU)
          ).differentiableAt (by simp)
        have hFdiff : DifferentiableAt ℝ F y := by
          simpa [F] using M.differentiableAt_halfSpaceFlatteningMap P.i y
        have hcomp :
            DiffForm.pullback F η y =
              DiffForm.pullback (e.symm ∘ F) (DiffForm.extd ω) y := by
          simpa [η] using
            DiffForm.pullback_comp_apply e.symm F (DiffForm.extd ω) hsymmdiff hFdiff
        have hevent : (e.symm ∘ F) =ᶠ[𝓝 y] id := by
          simpa [F, e, Function.comp_def] using e.eventually_left_inverse hysrc
        have hid :
            DiffForm.pullback (e.symm ∘ F) (DiffForm.extd ω) y =
              DiffForm.pullback id (DiffForm.extd ω) y :=
          DiffForm.pullback_congr_of_eventuallyEq (DiffForm.extd ω) hevent
        calc
          DiffForm.pullback F η y =
              DiffForm.pullback (e.symm ∘ F) (DiffForm.extd ω) y := hcomp
          _ = DiffForm.pullback id (DiffForm.extd ω) y := hid
          _ = DiffForm.extd ω y := by
              ext v
              simp [DiffForm.pullback])
  have hbox :
      DiffForm.integral η (Icc a b) =
        P.sign.domainSign * P.localBoundaryIntegral ω S hSsub := by
    simpa [η, e, S, hboxsub, hSsub] using
      P.halfSpaceBoxStokes_chart_symm_of_vanishesOnArtificialFaces_of_model_box_subset
        ω a b hle ha0 hω hvanish hboxsub
  have heq :
      P.sign.domainSign * DiffForm.integral (DiffForm.extd ω) U =
        P.sign.domainSign * P.localBoundaryIntegral ω S hSsub := by
    rw [← hpull, ← hcov, hbox]
  have hresult :
      DiffForm.integral (DiffForm.extd ω) U =
        P.localBoundaryIntegral ω S hSsub :=
    mul_left_cancel₀ (JacobianSign.domainSign_ne_zero P.sign) heq
  simpa [S, hSsub, hboxsub, tailBox_subset_localCoordDomain_of_flattening_image_eq] using hresult

/-- Local Stokes on an original patch set for a scalar-localized form.

The scalar support condition is stated in model coordinates, so it only discharges artificial-face
vanishing for the half-space box.  This theorem does not use an exterior-derivative product rule:
it applies the local theorem to the single form `χ • ω`. -/
theorem integral_extd_fsmul_eq_localBoundaryIntegral_of_box_of_disjoint_support_scalar
    (P : BoundaryChartPatch M x) (χ : ℝSpace (n + 1) → ℝ) (ω : DiffForm (n + 1) n)
    {U : Set (ℝSpace (n + 1))} (a b : ℝSpace (n + 1))
    (hUmeas : MeasurableSet U) (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b)
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hdisj : Disjoint
      (Function.support (χ ∘ (M.halfSpaceFlatteningChart P.i x P.h).symm))
      (CubeStokes.boxArtificialFaces a b)) :
    DiffForm.integral (DiffForm.extd (DiffForm.fsmul χ ω)) U =
      P.localBoundaryIntegral (DiffForm.fsmul χ ω)
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1))))
        (P.tailBox_subset_localCoordDomain_of_flattening_image_eq a b hle ha0 hUsub himage) := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  have hχω : ContDiff ℝ (⊤ : ℕ∞) (DiffForm.fsmul χ ω) :=
    DiffForm.isSmooth_fsmul hχ hω
  have hdisj_form :
      Disjoint
        (Function.support (DiffForm.pullback e.symm (DiffForm.fsmul χ ω)))
        (CubeStokes.boxArtificialFaces a b) := by
    rw [DiffForm.pullback_fsmul]
    exact DiffForm.disjoint_support_fsmul_of_disjoint_support_left
      (by simpa [e] using hdisj)
  have hvanish : CubeStokes.VanishesOnBoxArtificialFaces
      (DiffForm.pullback e.symm (DiffForm.fsmul χ ω)) a b :=
    CubeStokes.vanishesOnBoxArtificialFaces_of_disjoint_support_boxArtificialFaces
      (DiffForm.pullback e.symm (DiffForm.fsmul χ ω)) a b hdisj_form
  simpa [e] using
    P.integral_extd_eq_localBoundaryIntegral_of_flattening_image_eq_model_box
      (DiffForm.fsmul χ ω) a b hUmeas hUsub himage hle ha0 hχω
      (by simpa [e] using hvanish)

end BoundaryChartPatch
end SmoothDomain

end
