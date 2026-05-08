/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatchStokes
import LeanStokes.Domain.DomainIntegral
import LeanStokes.Domain.LocalBox
import LeanStokes.Domain.PartitionOfUnity
import LeanStokes.Integration.Localization

/-!
# Finite Localized Boundary Stokes Assembly

This module packages the data for a finite family of localized boundary-box
Stokes pieces and proves the finite summation theorem for that certified data.
The resulting boundary side is still a sum of patch-local boundary integrals; it
is not yet a chart-independent global boundary integral or the final compact
domain Stokes theorem.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology Manifold

namespace SmoothDomain

variable {n : ℕ}

/-- One certified scalar-localized boundary patch contribution to Stokes.

The fields are deliberately explicit: this structure records the hypotheses
needed to assemble local chart-box Stokes statements without claiming a product
rule, global chart smoothness, or chart-independent boundary integration. -/
structure BoundaryLocalizedStokesPiece (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) where
  /-- Boundary center of the certified chart patch. -/
  x : ℝSpace (n + 1)
  /-- Determinant-sign-stable boundary chart patch. -/
  P : BoundaryChartPatch M x
  /-- Scalar cutoff for this localized piece. -/
  χ : ℝSpace (n + 1) → ℝ
  /-- Original-side local set whose flattening image is a half-space box. -/
  U : Set (ℝSpace (n + 1))
  /-- Lower corner of the model half-space box. -/
  a : ℝSpace (n + 1)
  /-- Upper corner of the model half-space box. -/
  b : ℝSpace (n + 1)
  U_measurable : MeasurableSet U
  U_subset_patch : U ⊆ P.U
  U_subset_carrier : U ⊆ M.carrier
  flattening_image_eq_box : M.halfSpaceFlatteningMap P.i '' U = Icc a b
  box_le : a ≤ b
  box_zero_low : a (0 : Fin (n + 1)) = 0
  scalar_smooth : ContDiff ℝ ⊤ χ
  localized_differentiable : Differentiable ℝ (DiffForm.fsmul χ ω)
  localized_extd_integrable :
    IntegrableOn (DiffForm.topCoeff (DiffForm.extd (DiffForm.fsmul χ ω))) M.carrier volume
  model_pullback_differentiable :
    Differentiable ℝ
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm
        (DiffForm.fsmul χ ω))
  model_coord_smooth :
    CubeStokes.IsSmooth (CubeStokes.toCoordNForm
      (DiffForm.pullback (M.halfSpaceFlatteningChart P.i x P.h).symm
        (DiffForm.fsmul χ ω)))
  scalar_support_disjoint_artificial :
    Disjoint (Function.support (χ ∘ (M.halfSpaceFlatteningChart P.i x P.h).symm))
      (CubeStokes.boxArtificialFaces a b)
  scalar_eventually_zero_off_U_in_carrier :
    ∀ y ∈ M.carrier, y ∉ U → χ =ᶠ[𝓝 y] fun _ => 0

namespace BoundaryLocalizedStokesPiece

variable {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}

/-- Extract the pure boundary chart-box geometry from a localized boundary Stokes piece. -/
def chartBox (Q : BoundaryLocalizedStokesPiece M ω) : BoundaryChartBox M where
  x := Q.x
  P := Q.P
  U := Q.U
  a := Q.a
  b := Q.b
  U_measurable := Q.U_measurable
  U_subset_patch := Q.U_subset_patch
  U_subset_carrier := Q.U_subset_carrier
  flattening_image_eq_box := Q.flattening_image_eq_box
  box_le := Q.box_le
  box_zero_low := Q.box_zero_low

/-- Build a localized boundary Stokes piece from pure chart-box geometry and scalar/form data. -/
def ofChartBox (G : BoundaryChartBox M) (χ : ℝSpace (n + 1) → ℝ)
    (scalar_smooth : ContDiff ℝ ⊤ χ)
    (localized_differentiable : Differentiable ℝ (DiffForm.fsmul χ ω))
    (localized_extd_integrable :
      IntegrableOn (DiffForm.topCoeff (DiffForm.extd (DiffForm.fsmul χ ω))) M.carrier volume)
    (model_pullback_differentiable :
      Differentiable ℝ
        (DiffForm.pullback (M.halfSpaceFlatteningChart G.P.i G.x G.P.h).symm
          (DiffForm.fsmul χ ω)))
    (model_coord_smooth :
      CubeStokes.IsSmooth (CubeStokes.toCoordNForm
        (DiffForm.pullback (M.halfSpaceFlatteningChart G.P.i G.x G.P.h).symm
          (DiffForm.fsmul χ ω))))
    (scalar_support_disjoint_artificial :
      Disjoint (Function.support (χ ∘ (M.halfSpaceFlatteningChart G.P.i G.x G.P.h).symm))
        (CubeStokes.boxArtificialFaces G.a G.b))
    (scalar_eventually_zero_off_U_in_carrier :
      ∀ y ∈ M.carrier, y ∉ G.U → χ =ᶠ[𝓝 y] fun _ => 0) :
    BoundaryLocalizedStokesPiece M ω where
  x := G.x
  P := G.P
  χ := χ
  U := G.U
  a := G.a
  b := G.b
  U_measurable := G.U_measurable
  U_subset_patch := G.U_subset_patch
  U_subset_carrier := G.U_subset_carrier
  flattening_image_eq_box := G.flattening_image_eq_box
  box_le := G.box_le
  box_zero_low := G.box_zero_low
  scalar_smooth := scalar_smooth
  localized_differentiable := localized_differentiable
  localized_extd_integrable := localized_extd_integrable
  model_pullback_differentiable := model_pullback_differentiable
  model_coord_smooth := model_coord_smooth
  scalar_support_disjoint_artificial := scalar_support_disjoint_artificial
  scalar_eventually_zero_off_U_in_carrier := scalar_eventually_zero_off_U_in_carrier

/-- Boundary-coordinate tail of the model half-space box for a localized piece. -/
def boundaryTail (Q : BoundaryLocalizedStokesPiece M ω) : Set (ℝSpace n) :=
  Icc (Q.a ∘ Fin.succAbove (0 : Fin (n + 1)))
    (Q.b ∘ Fin.succAbove (0 : Fin (n + 1)))

/-- The boundary-coordinate tail lies in the certified local coordinate domain. -/
theorem boundaryTail_subset_localCoordDomain (Q : BoundaryLocalizedStokesPiece M ω) :
    Q.boundaryTail ⊆ Q.P.localCoordDomain :=
  Q.P.tailBox_subset_localCoordDomain_of_flattening_image_eq Q.a Q.b Q.box_le
    Q.box_zero_low Q.U_subset_patch Q.flattening_image_eq_box

/-- Patch-local boundary contribution of a certified localized Stokes piece. -/
def boundaryContribution (Q : BoundaryLocalizedStokesPiece M ω) : ℝ :=
  Q.P.localBoundaryIntegral (DiffForm.fsmul Q.χ ω) Q.boundaryTail
    Q.boundaryTail_subset_localCoordDomain

/-- Carrier integral of a boundary localized piece equals its patch-local boundary contribution. -/
theorem carrierIntegral_eq_boundaryContribution (Q : BoundaryLocalizedStokesPiece M ω)
    (hω : ContDiff ℝ ⊤ ω) :
    DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) M.carrier =
      Q.boundaryContribution := by
  have hrestrict :
      DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) M.carrier =
        DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) Q.U :=
    DiffForm.integral_extd_fsmul_eq_integral_extd_fsmul_of_subset_of_left_eventuallyEq_zero_off
      Q.χ ω M.measurableSet_carrier Q.U_measurable Q.U_subset_carrier
      Q.scalar_eventually_zero_off_U_in_carrier
  have hlocal :
      DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) Q.U =
        Q.boundaryContribution := by
    have hlocal_raw :=
      Q.P.integral_extd_fsmul_eq_localBoundaryIntegral_of_flattening_image_eq_model_box_of_disjoint_support_scalar
        Q.χ ω Q.a Q.b Q.U_measurable Q.U_subset_patch Q.flattening_image_eq_box
        Q.box_le Q.box_zero_low Q.scalar_smooth hω Q.model_pullback_differentiable
        Q.model_coord_smooth Q.scalar_support_disjoint_artificial
    simpa [BoundaryLocalizedStokesPiece.boundaryContribution,
      BoundaryLocalizedStokesPiece.boundaryTail,
      BoundaryLocalizedStokesPiece.boundaryTail_subset_localCoordDomain] using hlocal_raw
  exact hrestrict.trans hlocal

end BoundaryLocalizedStokesPiece

/-- A proof-carrying localized Stokes contribution over the carrier.

This is an intermediate certificate layer: it records that one scalar cutoff has a certified
carrier integral contribution.  It is not a construction of a partition of unity or a global
boundary integral. -/
structure LocalizedStokesPiece (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) where
  /-- Scalar cutoff for this localized piece. -/
  χ : ℝSpace (n + 1) → ℝ
  localized_differentiable : Differentiable ℝ (DiffForm.fsmul χ ω)
  localized_extd_integrable :
    IntegrableOn (DiffForm.topCoeff (DiffForm.extd (DiffForm.fsmul χ ω))) M.carrier volume
  /-- Certified contribution of this localized piece. -/
  contribution : ℝ
  carrier_integral_eq_contribution :
    DiffForm.integral (DiffForm.extd (DiffForm.fsmul χ ω)) M.carrier = contribution

namespace BoundaryLocalizedStokesPiece

variable {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}

/-- View a boundary localized Stokes piece as a generic proof-carrying localized contribution. -/
def toLocalizedStokesPiece (Q : BoundaryLocalizedStokesPiece M ω)
    (hω : ContDiff ℝ ⊤ ω) : LocalizedStokesPiece M ω where
  χ := Q.χ
  localized_differentiable := Q.localized_differentiable
  localized_extd_integrable := Q.localized_extd_integrable
  contribution := Q.boundaryContribution
  carrier_integral_eq_contribution := Q.carrierIntegral_eq_boundaryContribution hω

end BoundaryLocalizedStokesPiece

/-- One certified scalar-localized interior box contribution to Stokes.

The contribution of such a piece is zero because its localized form is supported away from every
formal cubical boundary face of the box. -/
structure InteriorLocalizedStokesPiece (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) where
  /-- Scalar cutoff for this localized piece. -/
  χ : ℝSpace (n + 1) → ℝ
  /-- Lower corner of the interior model box. -/
  a : ℝSpace (n + 1)
  /-- Upper corner of the interior model box. -/
  b : ℝSpace (n + 1)
  box_le : a ≤ b
  box_subset_carrier : Icc a b ⊆ M.carrier
  scalar_smooth : ContDiff ℝ ⊤ χ
  localized_differentiable : Differentiable ℝ (DiffForm.fsmul χ ω)
  localized_extd_integrable :
    IntegrableOn (DiffForm.topCoeff (DiffForm.extd (DiffForm.fsmul χ ω))) M.carrier volume
  scalar_support_disjoint_boundary :
    Disjoint (Function.support χ) (CubeStokes.boxBoundaryFaces a b)
  scalar_eventually_zero_off_box_in_carrier :
    ∀ y ∈ M.carrier, y ∉ Icc a b → χ =ᶠ[𝓝 y] fun _ => 0

namespace InteriorLocalizedStokesPiece

variable {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}

/-- Extract the pure interior-box geometry from a localized interior Stokes piece. -/
def interiorBox (Q : InteriorLocalizedStokesPiece M ω) : InteriorBox M where
  a := Q.a
  b := Q.b
  box_le := Q.box_le
  box_subset_carrier := Q.box_subset_carrier

/-- Build a localized interior Stokes piece from pure interior-box geometry and scalar/form data. -/
def ofInteriorBox (G : InteriorBox M) (χ : ℝSpace (n + 1) → ℝ)
    (scalar_smooth : ContDiff ℝ ⊤ χ)
    (localized_differentiable : Differentiable ℝ (DiffForm.fsmul χ ω))
    (localized_extd_integrable :
      IntegrableOn (DiffForm.topCoeff (DiffForm.extd (DiffForm.fsmul χ ω))) M.carrier volume)
    (scalar_support_disjoint_boundary :
      Disjoint (Function.support χ) (CubeStokes.boxBoundaryFaces G.a G.b))
    (scalar_eventually_zero_off_box_in_carrier :
      ∀ y ∈ M.carrier, y ∉ Icc G.a G.b → χ =ᶠ[𝓝 y] fun _ => 0) :
    InteriorLocalizedStokesPiece M ω where
  χ := χ
  a := G.a
  b := G.b
  box_le := G.box_le
  box_subset_carrier := G.box_subset_carrier
  scalar_smooth := scalar_smooth
  localized_differentiable := localized_differentiable
  localized_extd_integrable := localized_extd_integrable
  scalar_support_disjoint_boundary := scalar_support_disjoint_boundary
  scalar_eventually_zero_off_box_in_carrier := scalar_eventually_zero_off_box_in_carrier

/-- Carrier integral of an interior localized piece is zero. -/
theorem carrierIntegral_eq_zero (Q : InteriorLocalizedStokesPiece M ω)
    (hω : ContDiff ℝ ⊤ ω) :
    DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) M.carrier = 0 := by
  have hrestrict :
      DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) M.carrier =
        DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) (Icc Q.a Q.b) :=
    DiffForm.integral_extd_fsmul_eq_integral_extd_fsmul_of_subset_of_left_eventuallyEq_zero_off
      Q.χ ω M.measurableSet_carrier measurableSet_Icc Q.box_subset_carrier
      Q.scalar_eventually_zero_off_box_in_carrier
  have hχω : ContDiff ℝ ⊤ (DiffForm.fsmul Q.χ ω) :=
    DiffForm.isSmooth_fsmul Q.scalar_smooth hω
  have hdisj_form :
      Disjoint (Function.support (DiffForm.fsmul Q.χ ω))
        (CubeStokes.boxBoundaryFaces Q.a Q.b) :=
    DiffForm.disjoint_support_fsmul_of_disjoint_support_left Q.scalar_support_disjoint_boundary
  have hbox :
      DiffForm.integral (DiffForm.extd (DiffForm.fsmul Q.χ ω)) (Icc Q.a Q.b) = 0 :=
    CubeStokes.boxStokes_eq_zero_of_disjoint_support_boxBoundaryFaces
      (DiffForm.fsmul Q.χ ω) Q.a Q.b Q.box_le hχω hdisj_form
  exact hrestrict.trans hbox

/-- View an interior localized Stokes piece as a generic proof-carrying localized contribution. -/
def toLocalizedStokesPiece (Q : InteriorLocalizedStokesPiece M ω)
    (hω : ContDiff ℝ ⊤ ω) : LocalizedStokesPiece M ω where
  χ := Q.χ
  localized_differentiable := Q.localized_differentiable
  localized_extd_integrable := Q.localized_extd_integrable
  contribution := 0
  carrier_integral_eq_contribution := Q.carrierIntegral_eq_zero hω

end InteriorLocalizedStokesPiece

/-- Finite assembly of generic proof-carrying localized Stokes pieces.

Each piece supplies its own certified carrier-integral contribution.  The only global condition is
that the scalar cutoffs sum to one locally on the carrier. -/
theorem finite_localized_stokes {M : SmoothDomain (n + 1)}
    {ω : DiffForm (n + 1) n} {ι : Type*} (s : Finset ι)
    (piece : ι → LocalizedStokesPiece M ω)
    (hpartition : ∀ y ∈ M.carrier,
      (fun z => ∑ i ∈ s, (piece i).χ z) =ᶠ[𝓝 y] fun _ => 1) :
    M.domainIntegral (DiffForm.extd ω) =
      ∑ i ∈ s, (piece i).contribution := by
  have hsum :
      (∑ i ∈ s,
        DiffForm.integral (DiffForm.extd (DiffForm.fsmul (piece i).χ ω)) M.carrier) =
        DiffForm.integral (DiffForm.extd ω) M.carrier :=
    DiffForm.finset_sum_integral_extd_fsmul_eq_integral_extd_of_sum_eventuallyEq_one
      s (fun i => (piece i).χ) ω M.measurableSet_carrier
      (fun i _ => (piece i).localized_differentiable)
      (fun i _ => (piece i).localized_extd_integrable)
      hpartition
  rw [domainIntegral, ← hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact (piece i).carrier_integral_eq_contribution

/-- Finite localized Stokes assembly for a family of proof-carrying pieces whose scalar cutoffs are
the functions of an ambient smooth partition of unity.

The active finite set is extracted from topological supports meeting the compact carrier, so the
partition equality holds in ambient neighborhoods of carrier points. -/
theorem finite_localized_stokes_of_smoothPartition {M : SmoothDomain (n + 1)}
    {ω : DiffForm (n + 1) n} {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (piece : ι → LocalizedStokesPiece M ω)
    (hχ : ∀ i, (piece i).χ = fun z => ρ i z) :
    M.domainIntegral (DiffForm.extd ω) =
      ∑ i ∈ M.compactActiveFinset ρ, (piece i).contribution := by
  refine finite_localized_stokes (M.compactActiveFinset ρ) piece ?_
  intro y hy
  filter_upwards [M.smoothPartition_compactActive_eventuallyEq_one ρ hy] with z hz
  simpa [hχ] using hz

/-- Finite assembly of certified localized boundary-box Stokes pieces.

The theorem proves that the domain integral of `dω` over the compact carrier equals the finite sum
of the provided patch-local boundary contributions.  It is an assembly theorem for certified local
data, not a chart-independent boundary integral or the final exported compact-domain Stokes
statement. -/
theorem finite_boundary_localized_stokes {M : SmoothDomain (n + 1)}
    {ω : DiffForm (n + 1) n} {ι : Type*} (s : Finset ι)
    (piece : ι → BoundaryLocalizedStokesPiece M ω)
    (hω : ContDiff ℝ ⊤ ω)
    (hpartition : ∀ y ∈ M.carrier,
      (fun z => ∑ i ∈ s, (piece i).χ z) =ᶠ[𝓝 y] fun _ => 1) :
    M.domainIntegral (DiffForm.extd ω) =
      ∑ i ∈ s, (piece i).boundaryContribution := by
  simpa [BoundaryLocalizedStokesPiece.toLocalizedStokesPiece] using
    finite_localized_stokes s
      (fun i => (piece i).toLocalizedStokesPiece hω) hpartition

/-- Boundary-piece finite assembly using the finite active set of an ambient smooth partition of
unity. -/
theorem finite_boundary_localized_stokes_of_smoothPartition {M : SmoothDomain (n + 1)}
    {ω : DiffForm (n + 1) n} {ι : Type*}
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (piece : ι → BoundaryLocalizedStokesPiece M ω)
    (hω : ContDiff ℝ ⊤ ω)
    (hχ : ∀ i, (piece i).χ = fun z => ρ i z) :
    M.domainIntegral (DiffForm.extd ω) =
      ∑ i ∈ M.compactActiveFinset ρ, (piece i).boundaryContribution := by
  simpa [BoundaryLocalizedStokesPiece.toLocalizedStokesPiece] using
    finite_localized_stokes_of_smoothPartition ρ
      (fun i => (piece i).toLocalizedStokesPiece hω) hχ

end SmoothDomain

end
