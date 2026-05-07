/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatchModelIntegral
import LeanStokes.Domain.BoxStokes
import LeanStokes.DiffForm.Localization

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
open scoped Topology

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

/-- If a model half-space box lies in the certified inverse-chart patch, then its true boundary
tail lies in the patch-local boundary coordinate domain. -/
theorem tailBox_subset_localCoordDomain_of_model_box_subset
    (P : BoundaryChartPatch M x) (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hboxsub : Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U }) :
    Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
        (b ∘ Fin.succAbove (0 : Fin (n + 1))) ⊆ P.localCoordDomain := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  intro y hy
  let z : ℝSpace (n + 1) := halfSpaceBoundaryParam n y
  have hzbox : z ∈ Icc a b := by
    constructor
    · intro j
      cases j using Fin.cases with
      | zero =>
          simp [z, ha0]
      | succ i =>
          simpa [z, halfSpaceBoundaryParam] using hy.1 i
    · intro j
      cases j using Fin.cases with
      | zero =>
          have hle0 : a (0 : Fin (n + 1)) ≤ b (0 : Fin (n + 1)) := hle 0
          simpa [z, ha0] using hle0
      | succ i =>
          simpa [z, halfSpaceBoundaryParam] using hy.2 i
  have hzpatch := hboxsub hzbox
  refine ⟨?_, ?_⟩
  · simpa [boundaryChartCoordDomain, e, z] using hzpatch.1
  · simpa [boundaryChartParam, e, z] using hzpatch.2

/-- Half-space box Stokes through an inverse boundary-flattening chart, using full model-box
containment in the certified patch to discharge the inverse-chart smoothness and boundary-coordinate
validity side conditions.  The analytic regularity and artificial-face hypotheses for the model
pullback form remain explicit. -/
theorem halfSpaceBoxStokes_chart_symm_of_vanishesOnArtificialFaces_of_model_box_subset
    (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hω : ContDiff ℝ ⊤ ω)
    (hmodel_diff :
      Differentiable ℝ (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω))
    (hcoord : CubeStokes.IsSmooth (CubeStokes.toCoordNForm
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω)))
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
  have hdiffBox : ∀ z ∈ Icc a b, ContDiffAt ℝ ⊤ e.symm z := by
    intro z hz
    have hzpatch := hboxsub hz
    exact P.contDiffAt_halfSpaceFlatteningChart_symm
      (by simpa [e] using hzpatch.1) (by simpa [e] using hzpatch.2)
  let hSsub := P.tailBox_subset_localCoordDomain_of_model_box_subset a b hle ha0 hboxsub
  simpa [e, hSsub] using
    P.halfSpaceBoxStokes_chart_symm_of_vanishesOnArtificialFaces_of_differentiable
      ω a b hle ha0 hω hmodel_diff hcoord
      (by simpa [e] using hdiffBox) hvanish hSsub

/-- If a set in the certified patch has flattening image a model box, then that model box lies in
the certified inverse-chart patch. -/
theorem model_box_subset_patch_of_flattening_image_eq
    (P : BoundaryChartPatch M x) {U : Set (ℝSpace (n + 1))}
    {a b : ℝSpace (n + 1)}
    (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b) :
    Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U } := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  intro z hz
  have hzimg : z ∈ M.halfSpaceFlatteningMap P.i '' U := by
    simpa [himage] using hz
  rcases hzimg with ⟨y, hyU, rfl⟩
  have hyP : y ∈ P.U := hUsub hyU
  have hysrc : y ∈ e.source := P.subset_source hyP
  constructor
  · simpa [e] using e.map_source hysrc
  · have hleft : e.symm (e y) = y := e.left_inv hysrc
    have hleft' :
        (M.halfSpaceFlatteningChart P.i x P.h).symm
          (M.halfSpaceFlatteningMap P.i y) = y := by
      simpa [e] using hleft
    rw [hleft']
    exact hyP

/-- If a certified patch set has flattening image a model half-space box, then the true boundary
tail of that box lies in the patch-local boundary coordinate domain. -/
theorem tailBox_subset_localCoordDomain_of_flattening_image_eq
    (P : BoundaryChartPatch M x) {U : Set (ℝSpace (n + 1))}
    (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b) :
    Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
        (b ∘ Fin.succAbove (0 : Fin (n + 1))) ⊆ P.localCoordDomain :=
  P.tailBox_subset_localCoordDomain_of_model_box_subset a b hle ha0
    (P.model_box_subset_patch_of_flattening_image_eq hUsub himage)

/-- Local Stokes on an original patch set whose flattening image is a model half-space box.

The theorem combines signed top-form change of variables, the model-box Stokes bridge, and the
local boundary chart integral.  It remains local to one certified patch and keeps the analytic
regularity and artificial-face hypotheses for the model pullback explicit. -/
theorem integral_extd_eq_localBoundaryIntegral_of_flattening_image_eq_model_box
    (P : BoundaryChartPatch M x) (ω : DiffForm (n + 1) n)
    {U : Set (ℝSpace (n + 1))} (a b : ℝSpace (n + 1))
    (hUmeas : MeasurableSet U) (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b)
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hω : ContDiff ℝ ⊤ ω)
    (hmodel_diff :
      Differentiable ℝ (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω))
    (hcoord : CubeStokes.IsSmooth (CubeStokes.toCoordNForm
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm ω)))
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
          ).differentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
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
        ω a b hle ha0 hω hmodel_diff hcoord hvanish hboxsub
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
theorem integral_extd_fsmul_eq_localBoundaryIntegral_of_flattening_image_eq_model_box_of_disjoint_support_scalar
    (P : BoundaryChartPatch M x) (χ : ℝSpace (n + 1) → ℝ) (ω : DiffForm (n + 1) n)
    {U : Set (ℝSpace (n + 1))} (a b : ℝSpace (n + 1))
    (hUmeas : MeasurableSet U) (hUsub : U ⊆ P.U)
    (himage : M.halfSpaceFlatteningMap P.i '' U = Icc a b)
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hχ : ContDiff ℝ ⊤ χ) (hω : ContDiff ℝ ⊤ ω)
    (hmodel_diff :
      Differentiable ℝ
        (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm (DiffForm.fsmul χ ω)))
    (hcoord : CubeStokes.IsSmooth (CubeStokes.toCoordNForm
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm
        (DiffForm.fsmul χ ω))))
    (hdisj : Disjoint
      (Function.support (χ ∘ (M.halfSpaceFlatteningChart P.i x P.h).symm))
      (CubeStokes.boxArtificialFaces a b)) :
    DiffForm.integral (DiffForm.extd (DiffForm.fsmul χ ω)) U =
      P.localBoundaryIntegral (DiffForm.fsmul χ ω)
        (Icc (a ∘ Fin.succAbove (0 : Fin (n + 1)))
             (b ∘ Fin.succAbove (0 : Fin (n + 1))))
        (P.tailBox_subset_localCoordDomain_of_flattening_image_eq a b hle ha0 hUsub himage) := by
  let e := M.halfSpaceFlatteningChart P.i x P.h
  have hχω : ContDiff ℝ ⊤ (DiffForm.fsmul χ ω) :=
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
      (by simpa [e] using hmodel_diff)
      (by simpa [e] using hcoord)
      (by simpa [e] using hvanish)

end BoundaryChartPatch
end SmoothDomain

end
