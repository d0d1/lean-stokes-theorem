/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.FiniteLocalization

/-!
# Box-Controlled Carrier Covers

This module records the local cover data needed to turn a smooth partition of
unity into certified localized Stokes pieces.  The ambient open cover member
used for partition subordination is kept separate from the closed box used for
the local Stokes theorem.  This distinction is essential at boundary points:
an ambient open set containing a boundary point cannot lie inside the strict
interior of the model half-space box.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology Manifold

namespace SmoothDomain

variable {n : ℕ}

/-- An ambient open cover member controlled by an interior closed box.

The open set `V` is used for partition subordination.  Its topological support
is required to lie in the closed box and to avoid every formal boundary face of
that box. -/
structure InteriorBoxCoverMember (M : SmoothDomain (n + 1)) where
  /-- Ambient open set used as a partition cover member. -/
  V : Set (ℝSpace (n + 1))
  isOpen_V : IsOpen V
  /-- Closed full box contained in the carrier. -/
  G : InteriorBox M
  V_subset_box : V ⊆ Icc G.a G.b
  V_disjoint_boxBoundaryFaces : Disjoint V (CubeStokes.boxBoundaryFaces G.a G.b)

namespace InteriorBoxCoverMember

variable {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}

/-- Topological support controlled by an interior cover member lies in its closed box. -/
theorem tsupport_subset_box (C : InteriorBoxCoverMember M)
    {χ : ℝSpace (n + 1) → ℝ} (hχV : tsupport χ ⊆ C.V) :
    tsupport χ ⊆ Icc C.G.a C.G.b :=
  hχV.trans C.V_subset_box

/-- Topological support controlled by an interior cover member avoids the formal box boundary. -/
theorem tsupport_disjoint_boxBoundaryFaces (C : InteriorBoxCoverMember M)
    {χ : ℝSpace (n + 1) → ℝ} (hχV : tsupport χ ⊆ C.V) :
    Disjoint (tsupport χ) (CubeStokes.boxBoundaryFaces C.G.a C.G.b) :=
  C.V_disjoint_boxBoundaryFaces.mono_left hχV

/-- Raw scalar support controlled by an interior cover member avoids the formal box boundary. -/
theorem support_disjoint_boxBoundaryFaces (C : InteriorBoxCoverMember M)
    {χ : ℝSpace (n + 1) → ℝ} (hχV : tsupport χ ⊆ C.V) :
    Disjoint (Function.support χ) (CubeStokes.boxBoundaryFaces C.G.a C.G.b) :=
  disjoint_support_left_of_tsupport_subset hχV C.V_disjoint_boxBoundaryFaces

/-- Build an interior localized Stokes piece from a smooth partition cutoff subordinate to an
interior box-controlled cover member.

Only smoothness, localized differentiability, and support control are derived here; the analytic
integrability hypothesis remains explicit. -/
def toInteriorLocalizedStokesPieceOfSmoothPartition
    {ι : Type*} {s : Set (ℝSpace (n + 1))}
    (C : InteriorBoxCoverMember M)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) s)
    (i : ι) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hχV : tsupport (fun z => ρ i z) ⊆ C.V)
    (localized_extd_integrable :
      IntegrableOn
        (DiffForm.topCoeff (DiffForm.extd (DiffForm.fsmul (fun z => ρ i z) ω)))
        M.carrier volume) :
    InteriorLocalizedStokesPiece M ω :=
  InteriorLocalizedStokesPiece.ofInteriorBoxSmoothPartitionOfTSupport ρ i C.G hω
    (C.tsupport_subset_box hχV)
    (C.tsupport_disjoint_boxBoundaryFaces hχV)
    localized_extd_integrable

end InteriorBoxCoverMember

/-- An ambient open cover member controlled by a boundary half-space box.

The open set `V` is used for partition subordination.  The closed carrier-side
box `G.U` is used for local Stokes.  At the boundary we only require
`V ∩ M.carrier ⊆ G.U`, not `V ⊆ G.U`, because an ambient open neighborhood of a
boundary point necessarily crosses both sides of the boundary. -/
structure BoundaryBoxCoverMember (M : SmoothDomain (n + 1)) where
  /-- Ambient open set used as a partition cover member. -/
  V : Set (ℝSpace (n + 1))
  isOpen_V : IsOpen V
  /-- Closed half-space box chart certificate for carrier-side local Stokes. -/
  G : BoundaryChartBox M
  V_inter_carrier_subset_U : V ∩ M.carrier ⊆ G.U
  model_preimage_V_disjoint_artificial :
    Disjoint
      ((M.halfSpaceFlatteningChart G.P.i G.x G.P.h).symm ⁻¹' V)
      (CubeStokes.boxArtificialFaces G.a G.b)

namespace BoundaryBoxCoverMember

variable {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}

/-- A carrier point outside the boundary box is also outside the ambient cover member. -/
theorem notMem_V_of_mem_carrier_notMem_U (C : BoundaryBoxCoverMember M)
    {y : ℝSpace (n + 1)} (hyM : y ∈ M.carrier) (hyU : y ∉ C.G.U) :
    y ∉ C.V :=
  fun hyV => hyU (C.V_inter_carrier_subset_U ⟨hyV, hyM⟩)

/-- A partition cutoff controlled by a boundary cover member is eventually zero off the closed
carrier-side half-box at every carrier point. -/
theorem eventuallyEq_zero_off_U_in_carrier (C : BoundaryBoxCoverMember M)
    {χ : ℝSpace (n + 1) → ℝ} (hχV : tsupport χ ⊆ C.V) :
    ∀ y ∈ M.carrier, y ∉ C.G.U → χ =ᶠ[𝓝 y] fun _ => 0 := by
  intro y hyM hyU
  exact eventuallyEq_zero_of_tsupport_subset_of_notMem hχV
    (C.notMem_V_of_mem_carrier_notMem_U hyM hyU)

/-- A boundary cover member transfers ambient support control to the model-coordinate artificial
faces required by the local half-space-box Stokes theorem. -/
theorem support_comp_disjoint_artificial (C : BoundaryBoxCoverMember M)
    {χ : ℝSpace (n + 1) → ℝ} (hχV : tsupport χ ⊆ C.V) :
    Disjoint
      (Function.support (χ ∘ (M.halfSpaceFlatteningChart C.G.P.i C.G.x C.G.P.h).symm))
      (CubeStokes.boxArtificialFaces C.G.a C.G.b) :=
  C.model_preimage_V_disjoint_artificial.mono_left fun z hz => by
    have hz_support : (M.halfSpaceFlatteningChart C.G.P.i C.G.x C.G.P.h).symm z ∈
        Function.support χ := by
      simpa [Function.support] using hz
    exact hχV (subset_tsupport χ hz_support)

/-- Build a boundary localized Stokes piece from a smooth partition cutoff subordinate to a
boundary box-controlled cover member.

Only scalar smoothness, localized differentiability, eventual-zero support control, and model
artificial-face support control are derived here.  Integrability and model-coordinate regularity
remain explicit analytic hypotheses. -/
def toBoundaryLocalizedStokesPieceOfSmoothPartition
    {ι : Type*} {s : Set (ℝSpace (n + 1))}
    (C : BoundaryBoxCoverMember M)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) s)
    (i : ι) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hχV : tsupport (fun z => ρ i z) ⊆ C.V)
    (localized_extd_integrable :
      IntegrableOn
        (DiffForm.topCoeff (DiffForm.extd (DiffForm.fsmul (fun z => ρ i z) ω)))
        M.carrier volume)
    (model_pullback_differentiable :
      Differentiable ℝ
        (DiffForm.pullback (M.halfSpaceFlatteningChart C.G.P.i C.G.x C.G.P.h).symm
          (DiffForm.fsmul (fun z => ρ i z) ω)))
    (model_coord_smooth :
      CubeStokes.IsSmooth (CubeStokes.toCoordNForm
        (DiffForm.pullback (M.halfSpaceFlatteningChart C.G.P.i C.G.x C.G.P.h).symm
          (DiffForm.fsmul (fun z => ρ i z) ω)))) :
    BoundaryLocalizedStokesPiece M ω :=
  BoundaryLocalizedStokesPiece.ofChartBox C.G (fun z => ρ i z)
    (ρ.contDiff_apply_infty i)
    ((DiffForm.isSmooth_fsmul (ρ.contDiff_apply_infty i) hω).differentiable (by simp))
    localized_extd_integrable
    model_pullback_differentiable
    model_coord_smooth
    (C.support_comp_disjoint_artificial hχV)
    (C.eventuallyEq_zero_off_U_in_carrier hχV)

end BoundaryBoxCoverMember

/-- Indices for the refined carrier cover by box-controlled open members. -/
inductive BoxControlledCoverIndex (M : SmoothDomain (n + 1)) where
  | interior : InteriorBoxCoverMember M → BoxControlledCoverIndex M
  | boundary : BoundaryBoxCoverMember M → BoxControlledCoverIndex M

/-- The ambient open set associated to a box-controlled cover index. -/
def boxControlledCarrierCover (M : SmoothDomain (n + 1)) :
    BoxControlledCoverIndex M → Set (ℝSpace (n + 1))
  | BoxControlledCoverIndex.interior C => C.V
  | BoxControlledCoverIndex.boundary C => C.V

@[simp]
theorem boxControlledCarrierCover_interior (M : SmoothDomain (n + 1))
    (C : InteriorBoxCoverMember M) :
    M.boxControlledCarrierCover (BoxControlledCoverIndex.interior C) = C.V :=
  rfl

@[simp]
theorem boxControlledCarrierCover_boundary (M : SmoothDomain (n + 1))
    (C : BoundaryBoxCoverMember M) :
    M.boxControlledCarrierCover (BoxControlledCoverIndex.boundary C) = C.V :=
  rfl

/-- The box-controlled carrier cover is open. -/
theorem isOpen_boxControlledCarrierCover (M : SmoothDomain (n + 1)) :
    ∀ i, IsOpen (M.boxControlledCarrierCover i) := by
  intro i
  cases i with
  | interior C => exact C.isOpen_V
  | boundary C => exact C.isOpen_V

/-- Conditional carrier coverage from pointwise existence of box-controlled interior and boundary
members.  Later geometric work should discharge the two pointwise-existence hypotheses. -/
theorem carrier_subset_iUnion_boxControlledCarrierCover
    (M : SmoothDomain (n + 1))
    (h_int : ∀ x : ℝSpace (n + 1), x ∈ M.int →
      ∃ C : InteriorBoxCoverMember M, x ∈ C.V)
    (h_boundary : ∀ x : ℝSpace (n + 1), x ∈ M.boundary →
      ∃ C : BoundaryBoxCoverMember M, x ∈ C.V) :
    M.carrier ⊆ ⋃ i, M.boxControlledCarrierCover i := by
  intro x hx
  rcases M.mem_carrier_iff_mem_int_or_mem_boundary.mp hx with hx_int | hx_boundary
  · rcases h_int x hx_int with ⟨C, hxC⟩
    exact mem_iUnion.mpr ⟨BoxControlledCoverIndex.interior C, hxC⟩
  · rcases h_boundary x hx_boundary with ⟨C, hxC⟩
    exact mem_iUnion.mpr ⟨BoxControlledCoverIndex.boundary C, hxC⟩

/-- Conditional existence of a global ambient smooth partition subordinate to the complement-
extended box-controlled cover. -/
theorem exists_smoothPartition_subordinate_ambientBoxControlledCover
    (M : SmoothDomain (n + 1))
    (h_int : ∀ x : ℝSpace (n + 1), x ∈ M.int →
      ∃ C : InteriorBoxCoverMember M, x ∈ C.V)
    (h_boundary : ∀ x : ℝSpace (n + 1), x ∈ M.boundary →
      ∃ C : BoundaryBoxCoverMember M, x ∈ C.V) :
    ∃ ρ : SmoothPartitionOfUnity
        (Option (BoxControlledCoverIndex M)) (𝓘(ℝ, ℝSpace (n + 1)))
        (ℝSpace (n + 1)) univ,
      ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover) :=
  M.exists_smoothPartition_subordinate_ambientCoverWithComplement
    M.boxControlledCarrierCover M.isOpen_boxControlledCarrierCover
    (M.carrier_subset_iUnion_boxControlledCarrierCover h_int h_boundary)

end SmoothDomain

end
