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

namespace CubeStokes

variable {n : ℕ}

/-- Coordinatewise strict open box in `Fin d → ℝ`.

This is intentionally not `Set.Ioo c d`: the order interval for the product order is weaker than
coordinatewise strict containment. -/
def coordOpenBox {d : ℕ} (c d' : ℝSpace d) : Set (ℝSpace d) :=
  {x | ∀ i, c i < x i ∧ x i < d' i}

/-- Coordinatewise strict open boxes are open in the product topology. -/
theorem isOpen_coordOpenBox {d : ℕ} (c d' : ℝSpace d) :
    IsOpen (coordOpenBox c d') := by
  unfold coordOpenBox
  rw [show {x : ℝSpace d | ∀ i, c i < x i ∧ x i < d' i} =
      ⋂ i, {x : ℝSpace d | c i < x i ∧ x i < d' i} by
    ext x
    simp]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

/-- A coordinatewise strict open box is a neighborhood of any point with coordinatewise strict
bounds. -/
theorem coordOpenBox_mem_nhds {d : ℕ} {c d' x : ℝSpace d}
    (hx : ∀ i, c i < x i ∧ x i < d' i) :
    coordOpenBox c d' ∈ 𝓝 x :=
  (isOpen_coordOpenBox c d').mem_nhds hx

/-- A coordinatewise strict inner open box lies in a larger closed box when every inner coordinate
is strictly between the corresponding outer bounds. -/
theorem coordOpenBox_subset_Icc_of_lt
    {a b c d : ℝSpace (n + 1)}
    (hac : ∀ i, a i < c i) (hdb : ∀ i, d i < b i) :
    coordOpenBox c d ⊆ Icc a b := by
  intro x hx
  rw [mem_Icc]
  constructor
  · intro i
    exact le_of_lt ((hac i).trans (hx i).1)
  · intro i
    exact le_of_lt ((hx i).2.trans (hdb i))

/-- A coordinatewise strict inner open box is disjoint from the formal boundary faces of a larger
closed box. -/
theorem disjoint_coordOpenBox_boxBoundaryFaces_of_lt
    {a b c d : ℝSpace (n + 1)}
    (hac : ∀ i, a i < c i) (hdb : ∀ i, d i < b i) :
    Disjoint (coordOpenBox c d) (boxBoundaryFaces a b) := by
  rw [disjoint_left]
  intro x hxI hxF
  unfold boxBoundaryFaces at hxF
  rcases mem_iUnion.mp hxF with ⟨i, hface⟩
  rcases hface with hhigh | hlow
  · rcases hhigh with ⟨y, _hy, rfl⟩
    have hb_lt_d : b i < d i := by simpa using (hxI i).2
    exact (hdb i).not_gt hb_lt_d
  · rcases hlow with ⟨y, _hy, rfl⟩
    have hc_lt_a : c i < a i := by simpa using (hxI i).1
    exact (hac i).not_gt hc_lt_a

/-- A coordinatewise strict inner open box that stays below the high normal face and away from
successor-coordinate faces is disjoint from the artificial faces of a larger half-space box. -/
theorem disjoint_coordOpenBox_boxArtificialFaces_of_lt
    {a b c d : ℝSpace (n + 1)}
    (h0 : d (0 : Fin (n + 1)) < b (0 : Fin (n + 1)))
    (hac : ∀ i : Fin n, a i.succ < c i.succ)
    (hdb : ∀ i : Fin n, d i.succ < b i.succ) :
    Disjoint (coordOpenBox c d) (boxArtificialFaces a b) := by
  rw [disjoint_left]
  intro x hxI hxF
  unfold boxArtificialFaces at hxF
  rcases hxF with hzero | hsucc
  · rcases hzero with ⟨y, _hy, rfl⟩
    have hb_lt_d : b (0 : Fin (n + 1)) < d (0 : Fin (n + 1)) := by
      simpa using (hxI (0 : Fin (n + 1))).2
    exact h0.not_gt hb_lt_d
  · rcases mem_iUnion.mp hsucc with ⟨i, hface⟩
    rcases hface with hhigh | hlow
    · rcases hhigh with ⟨y, _hy, rfl⟩
      have hb_lt_d : b i.succ < d i.succ := by simpa using (hxI i.succ).2
      exact (hdb i).not_gt hb_lt_d
    · rcases hlow with ⟨y, _hy, rfl⟩
      have hc_lt_a : c i.succ < a i.succ := by simpa using (hxI i.succ).1
      exact (hac i).not_gt hc_lt_a

end CubeStokes

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

/-- Build an interior box-controlled cover member from a coordinatewise strict inner open box. -/
def ofCoordOpenBox
    {a b c d : ℝSpace (n + 1)}
    (box_le : a ≤ b) (box_subset_carrier : Icc a b ⊆ M.carrier)
    (hac : ∀ i, a i < c i) (hdb : ∀ i, d i < b i) :
    InteriorBoxCoverMember M where
  V := CubeStokes.coordOpenBox c d
  isOpen_V := CubeStokes.isOpen_coordOpenBox c d
  G := {
    a := a
    b := b
    box_le := box_le
    box_subset_carrier := box_subset_carrier }
  V_subset_box := CubeStokes.coordOpenBox_subset_Icc_of_lt hac hdb
  V_disjoint_boxBoundaryFaces :=
    CubeStokes.disjoint_coordOpenBox_boxBoundaryFaces_of_lt hac hdb

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

/-- Build a boundary box-controlled cover member by proving that the model-coordinate preimage of
the ambient open member lies in a coordinatewise strict inner box avoiding the artificial faces. -/
def ofModelPreimageSubsetCoordOpenBox
    (G : BoundaryChartBox M) {V : Set (ℝSpace (n + 1))} (hV : IsOpen V)
    (hVU : V ∩ M.carrier ⊆ G.U) {c d : ℝSpace (n + 1)}
    (h0 : d (0 : Fin (n + 1)) < G.b (0 : Fin (n + 1)))
    (hac : ∀ i : Fin n, G.a i.succ < c i.succ)
    (hdb : ∀ i : Fin n, d i.succ < G.b i.succ)
    (hpre :
      (M.halfSpaceFlatteningChart G.P.i G.x G.P.h).symm ⁻¹' V ⊆
        CubeStokes.coordOpenBox c d) :
    BoundaryBoxCoverMember M where
  V := V
  isOpen_V := hV
  G := G
  V_inter_carrier_subset_U := hVU
  model_preimage_V_disjoint_artificial :=
    (CubeStokes.disjoint_coordOpenBox_boxArtificialFaces_of_lt h0 hac hdb).mono_left hpre

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
