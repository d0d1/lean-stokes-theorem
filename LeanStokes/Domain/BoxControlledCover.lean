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

/-- The artificial face point-set of a half-space box is contained in the box. -/
theorem boxArtificialFaces_subset_Icc {a b : ℝSpace (n + 1)} (hle : a ≤ b) :
    boxArtificialFaces a b ⊆ Icc a b := by
  intro x hx
  unfold boxArtificialFaces at hx
  rcases hx with hzero | hsucc
  · rcases hzero with ⟨y, hy, rfl⟩
    rw [mem_Icc]
    constructor
    · rw [Fin.le_insertNth_iff]
      exact ⟨hle 0, hy.1⟩
    · rw [Fin.insertNth_le_iff]
      exact ⟨le_rfl, hy.2⟩
  · rcases mem_iUnion.mp hsucc with ⟨i, hface⟩
    rcases hface with hhigh | hlow
    · rcases hhigh with ⟨y, hy, rfl⟩
      rw [mem_Icc]
      constructor
      · rw [Fin.le_insertNth_iff]
        exact ⟨hle i.succ, hy.1⟩
      · rw [Fin.insertNth_le_iff]
        exact ⟨le_rfl, hy.2⟩
    · rcases hlow with ⟨y, hy, rfl⟩
      rw [mem_Icc]
      constructor
      · rw [Fin.le_insertNth_iff]
        exact ⟨le_rfl, hy.1⟩
      · rw [Fin.insertNth_le_iff]
        exact ⟨hle i.succ, hy.2⟩

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

Smoothness, localized differentiability, support control, and compact-carrier integrability are
derived from the smooth partition cutoff and smooth form. -/
def toInteriorLocalizedStokesPieceOfSmoothPartition
    {ι : Type*} {s : Set (ℝSpace (n + 1))}
    (C : InteriorBoxCoverMember M)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) s)
    (i : ι) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hχV : tsupport (fun z => ρ i z) ⊆ C.V) :
    InteriorLocalizedStokesPiece M ω :=
  InteriorLocalizedStokesPiece.ofInteriorBoxSmoothPartitionOfTSupport ρ i C.G hω
    (C.tsupport_subset_box hχV)
    (C.tsupport_disjoint_boxBoundaryFaces hχV)

end InteriorBoxCoverMember

/-- Every strict interior point has an ambient box-controlled cover member.

The proof uses a small closed coordinate box inside the open strict interior and a smaller
coordinatewise open box around the point to avoid all formal boundary faces. -/
theorem exists_interiorBoxCoverMember_at_int (M : SmoothDomain (n + 1))
    {x : ℝSpace (n + 1)} (hx : x ∈ M.int) :
    ∃ C : InteriorBoxCoverMember M, x ∈ C.V := by
  rcases Metric.mem_nhds_iff.mp (M.isOpen_int.mem_nhds hx) with ⟨ε, hε, hball⟩
  let a : ℝSpace (n + 1) := fun i => x i - ε / 2
  let b : ℝSpace (n + 1) := fun i => x i + ε / 2
  let c : ℝSpace (n + 1) := fun i => x i - ε / 4
  let d : ℝSpace (n + 1) := fun i => x i + ε / 4
  have hbox_le : a ≤ b := by
    intro i
    dsimp [a, b]
    linarith
  have hbox_subset_carrier : Icc a b ⊆ M.carrier := by
    intro y hy
    apply M.int_subset_carrier
    apply hball
    rw [Metric.mem_ball]
    have hdist_le : dist y x ≤ ε / 2 := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor
      · have hleft : x i - ε / 2 ≤ y i := by simpa [a] using hy.1 i
        linarith
      · have hright : y i ≤ x i + ε / 2 := by simpa [b] using hy.2 i
        linarith
    linarith
  have hac : ∀ i, a i < c i := by
    intro i
    dsimp [a, c]
    linarith
  have hdb : ∀ i, d i < b i := by
    intro i
    dsimp [d, b]
    linarith
  refine ⟨InteriorBoxCoverMember.ofCoordOpenBox hbox_le hbox_subset_carrier hac hdb, ?_⟩
  intro i
  dsimp [InteriorBoxCoverMember.ofCoordOpenBox, CubeStokes.coordOpenBox, c, d]
  constructor <;> linarith

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

/-- Build a boundary box-controlled cover member from a larger closed model half-box and a smaller
ambient coordinatewise open model box.

The closed half-box supplies the carrier-side Stokes domain.  The smaller open box may cross the
true boundary in the normal coordinate, but its carrier-side part lies in the closed half-box and it
stays strictly away from all artificial faces. -/
def ofModelBoxes
    {x : ℝSpace (n + 1)} (P : BoundaryChartPatch M x) (a b c d : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hboxsub : Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U })
    (h0 : d (0 : Fin (n + 1)) < b (0 : Fin (n + 1)))
    (hac : ∀ i : Fin n, a i.succ < c i.succ)
    (hdb : ∀ i : Fin n, d i.succ < b i.succ) :
    BoundaryBoxCoverMember M := by
  let G : BoundaryChartBox M := BoundaryChartBox.ofModelBoxSubsetPatch P a b hle ha0 hboxsub
  refine {
    V := (M.halfSpaceFlatteningMap P.i) ⁻¹' CubeStokes.coordOpenBox c d ∩ P.U
    isOpen_V := ?_
    G := G
    V_inter_carrier_subset_U := ?_
    model_preimage_V_disjoint_artificial := ?_ }
  · exact (((M.contDiff_halfSpaceFlatteningMap P.i).continuous).isOpen_preimage _
      (CubeStokes.isOpen_coordOpenBox c d)).inter P.isOpen_U
  · intro y hy
    rcases hy with ⟨hyV, hyM⟩
    dsimp [G, BoundaryChartBox.ofModelBoxSubsetPatch]
    constructor
    · change M.halfSpaceFlatteningMap P.i y ∈ Icc a b
      rw [mem_Icc]
      constructor
      · intro j
        cases j using Fin.cases with
        | zero =>
            have hnonneg : 0 ≤ M.halfSpaceFlatteningMap P.i y (0 : Fin (n + 1)) := by
              rw [M.mem_carrier_iff_halfSpaceFlatteningMap_mem P.i y] at hyM
              exact hyM
            simpa [ha0] using hnonneg
        | succ i =>
            exact le_of_lt ((hac i).trans (hyV.1 i.succ).1)
      · intro j
        cases j using Fin.cases with
        | zero =>
            exact le_of_lt ((hyV.1 (0 : Fin (n + 1))).2.trans h0)
        | succ i =>
            exact le_of_lt ((hyV.1 i.succ).2.trans (hdb i))
    · exact hyV.2
  · rw [disjoint_left]
    intro z hzV hzF
    dsimp [G, BoundaryChartBox.ofModelBoxSubsetPatch] at hzV hzF
    have hzbox : z ∈ Icc a b := CubeStokes.boxArtificialFaces_subset_Icc hle hzF
    have hztarget : z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target := (hboxsub hzbox).1
    let e := M.halfSpaceFlatteningChart P.i x P.h
    have hright : M.halfSpaceFlatteningMap P.i (e.symm z) = z := by
      simpa [e] using e.right_inv hztarget
    have hzcoord : z ∈ CubeStokes.coordOpenBox c d := by
      simpa [hright, e] using hzV.1
    exact (disjoint_left.mp (CubeStokes.disjoint_coordOpenBox_boxArtificialFaces_of_lt h0 hac hdb))
      hzcoord hzF

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
artificial-face support control are local hypotheses; compact-carrier integrability follows from
smoothness of the localized form. -/
def toBoundaryLocalizedStokesPieceOfSmoothPartition
    {ι : Type*} {s : Set (ℝSpace (n + 1))}
    (C : BoundaryBoxCoverMember M)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) s)
    (i : ι) (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (hχV : tsupport (fun z => ρ i z) ⊆ C.V) :
    BoundaryLocalizedStokesPiece M ω :=
  BoundaryLocalizedStokesPiece.ofChartBox C.G (fun z => ρ i z)
    (ρ.contDiff_apply_infty i)
    ((DiffForm.isSmooth_fsmul (ρ.contDiff_apply_infty i) hω).differentiable (by simp))
    (C.support_comp_disjoint_artificial hχV)
    (C.eventuallyEq_zero_off_U_in_carrier hχV)

end BoundaryBoxCoverMember

/-- Every boundary point has an ambient box-controlled cover member.

The cover member is obtained by choosing a small closed half-box in flattening coordinates whose
low normal face is the true boundary face, and a smaller ambient coordinatewise open box around the
boundary point.  The open box is allowed to cross the true boundary, while its carrier-side part is
contained in the closed half-box and its model preimage avoids all artificial faces. -/
theorem exists_boundaryBoxCoverMember_at_boundary (M : SmoothDomain (n + 1))
    {x : ℝSpace (n + 1)} (hx : x ∈ M.boundary) :
    ∃ C : BoundaryBoxCoverMember M, x ∈ C.V := by
  let P : BoundaryChartPatch M x := Classical.choice (M.exists_boundaryChartPatch_at_boundary hx)
  let e := M.halfSpaceFlatteningChart P.i x P.h
  let z0 : ℝSpace (n + 1) := M.halfSpaceFlatteningMap P.i x
  have hz0target : z0 ∈ e.target := by
    simpa [e, z0] using M.image_mem_halfSpaceFlatteningChart_target P.i x P.h
  have hsymm_z0 : e.symm z0 = x := by
    simpa [e, z0] using e.left_inv (M.mem_halfSpaceFlatteningChart_source P.i x P.h)
  have hW : e.target ∩ e.symm ⁻¹' P.U ∈ 𝓝 z0 := by
    have htarget : e.target ∈ 𝓝 z0 := e.open_target.mem_nhds hz0target
    have hpreU : e.symm ⁻¹' P.U ∈ 𝓝 z0 := by
      exact (e.continuousAt_symm hz0target).preimage_mem_nhds
        (P.isOpen_U.mem_nhds (by simpa [hsymm_z0] using P.center_mem_U))
    exact Filter.inter_mem htarget hpreU
  rcases Metric.mem_nhds_iff.mp hW with ⟨ε, hε, hballW⟩
  have hz0_zero : z0 (0 : Fin (n + 1)) = 0 := by
    simpa [z0, HalfSpaceBdry] using
      (M.mem_boundary_iff_halfSpaceFlatteningMap_mem P.i x).mp hx
  let a : ℝSpace (n + 1) := Fin.cases (0 : ℝ) (fun i : Fin n => z0 i.succ - ε / 2)
  let b : ℝSpace (n + 1) := Fin.cases (ε / 2) (fun i : Fin n => z0 i.succ + ε / 2)
  let c : ℝSpace (n + 1) := Fin.cases (-ε / 4) (fun i : Fin n => z0 i.succ - ε / 4)
  let d : ℝSpace (n + 1) := Fin.cases (ε / 4) (fun i : Fin n => z0 i.succ + ε / 4)
  have hle : a ≤ b := by
    intro j
    cases j using Fin.cases with
    | zero =>
        dsimp [a, b]
        linarith
    | succ i =>
        dsimp [a, b]
        linarith
  have ha0 : a (0 : Fin (n + 1)) = 0 := by
    simp [a]
  have hboxsub : Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U } := by
    intro z hz
    have hzball : z ∈ Metric.ball z0 ε := by
      rw [Metric.mem_ball]
      have hdist_le : dist z z0 ≤ ε / 2 := by
        rw [dist_pi_le_iff (by positivity)]
        intro j
        rw [Real.dist_eq]
        apply abs_le.mpr
        cases j using Fin.cases with
        | zero =>
            constructor
            · have hlow : (0 : ℝ) ≤ z (0 : Fin (n + 1)) := by simpa [a] using hz.1 0
              rw [hz0_zero]
              linarith
            · have hhi : z (0 : Fin (n + 1)) ≤ ε / 2 := by simpa [b] using hz.2 0
              rw [hz0_zero]
              linarith
        | succ i =>
            constructor
            · have hlow : z0 i.succ - ε / 2 ≤ z i.succ := by simpa [a] using hz.1 i.succ
              linarith
            · have hhi : z i.succ ≤ z0 i.succ + ε / 2 := by simpa [b] using hz.2 i.succ
              linarith
      linarith
    exact hballW hzball
  have h0 : d (0 : Fin (n + 1)) < b (0 : Fin (n + 1)) := by
    dsimp [d, b]
    linarith
  have hac : ∀ i : Fin n, a i.succ < c i.succ := by
    intro i
    dsimp [a, c]
    linarith
  have hdb : ∀ i : Fin n, d i.succ < b i.succ := by
    intro i
    dsimp [d, b]
    linarith
  let C : BoundaryBoxCoverMember M :=
    BoundaryBoxCoverMember.ofModelBoxes P a b c d hle ha0 hboxsub h0 hac hdb
  refine ⟨C, ?_⟩
  dsimp [C, BoundaryBoxCoverMember.ofModelBoxes]
  constructor
  · intro j
    cases j using Fin.cases with
    | zero =>
        dsimp [c, d, z0]
        constructor <;> linarith
    | succ i =>
        dsimp [c, d]
        constructor <;> linarith
  · exact P.center_mem_U

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

/-- Carrier coverage from pointwise existence of box-controlled interior and boundary members. -/
theorem carrier_subset_iUnion_boxControlledCarrierCover_of_pointwise
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

/-- Existence of a global ambient smooth partition from pointwise existence of box-controlled cover
members. -/
theorem exists_smoothPartition_subordinate_ambientBoxControlledCover_of_pointwise
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
    (M.carrier_subset_iUnion_boxControlledCarrierCover_of_pointwise h_int h_boundary)

/-- Carrier coverage after discharging the strict-interior pointwise existence geometrically. -/
theorem carrier_subset_iUnion_boxControlledCarrierCover_of_boundary
    (M : SmoothDomain (n + 1))
    (h_boundary : ∀ x : ℝSpace (n + 1), x ∈ M.boundary →
      ∃ C : BoundaryBoxCoverMember M, x ∈ C.V) :
    M.carrier ⊆ ⋃ i, M.boxControlledCarrierCover i :=
  M.carrier_subset_iUnion_boxControlledCarrierCover_of_pointwise
    (fun _ hx => M.exists_interiorBoxCoverMember_at_int hx) h_boundary

/-- Smooth partition existence after discharging the strict-interior pointwise existence
geometrically.  Boundary pointwise existence remains the next local-chart geometry obligation. -/
theorem exists_smoothPartition_subordinate_ambientBoxControlledCover_of_boundary
    (M : SmoothDomain (n + 1))
    (h_boundary : ∀ x : ℝSpace (n + 1), x ∈ M.boundary →
      ∃ C : BoundaryBoxCoverMember M, x ∈ C.V) :
    ∃ ρ : SmoothPartitionOfUnity
        (Option (BoxControlledCoverIndex M)) (𝓘(ℝ, ℝSpace (n + 1)))
        (ℝSpace (n + 1)) univ,
      ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover) :=
  M.exists_smoothPartition_subordinate_ambientBoxControlledCover_of_pointwise
    (fun _ hx => M.exists_interiorBoxCoverMember_at_int hx) h_boundary

/-- The box-controlled carrier cover covers the compact regular sublevel carrier. -/
theorem carrier_subset_iUnion_boxControlledCarrierCover (M : SmoothDomain (n + 1)) :
    M.carrier ⊆ ⋃ i, M.boxControlledCarrierCover i :=
  M.carrier_subset_iUnion_boxControlledCarrierCover_of_pointwise
    (fun _ hx => M.exists_interiorBoxCoverMember_at_int hx)
    (fun _ hx => M.exists_boundaryBoxCoverMember_at_boundary hx)

/-- A global ambient smooth partition subordinate to the complement-extended box-controlled
cover. -/
theorem exists_smoothPartition_subordinate_ambientBoxControlledCover
    (M : SmoothDomain (n + 1)) :
    ∃ ρ : SmoothPartitionOfUnity
        (Option (BoxControlledCoverIndex M)) (𝓘(ℝ, ℝSpace (n + 1)))
        (ℝSpace (n + 1)) univ,
      ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover) :=
  M.exists_smoothPartition_subordinate_ambientCoverWithComplement
    M.boxControlledCarrierCover M.isOpen_boxControlledCarrierCover
    M.carrier_subset_iUnion_boxControlledCarrierCover

/-- The underlying box-controlled cover index associated to an active complement-extended
partition index. -/
noncomputable def activeBoxControlledCoverIndex
    {M : SmoothDomain (n + 1)}
    (ρ : SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
      (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (j : { i // i ∈ M.compactActiveFinset ρ }) : BoxControlledCoverIndex M :=
  Classical.choose (M.tsupport_subset_cover_of_mem_compactActiveFinset_of_isSubordinate ρ hρ j.2)

/-- The active complement-extended index is `some` of its box-controlled cover index, and its
topological support is contained in that cover member. -/
theorem activeBoxControlledCoverIndex_spec
    {M : SmoothDomain (n + 1)}
    (ρ : SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
      (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (j : { i // i ∈ M.compactActiveFinset ρ }) :
    j.1 = some (activeBoxControlledCoverIndex ρ hρ j) ∧
      tsupport (fun z => ρ j.1 z) ⊆
        M.boxControlledCarrierCover (activeBoxControlledCoverIndex ρ hρ j) := by
  unfold activeBoxControlledCoverIndex
  exact Classical.choose_spec
    (M.tsupport_subset_cover_of_mem_compactActiveFinset_of_isSubordinate ρ hρ j.2)

/-- Certified contribution of an active box-controlled partition element.

Interior cover members contribute `0`; boundary cover members contribute the corresponding
patch-local boundary integral.  The subtype stores the carrier-integral equality alongside the
chosen real contribution. -/
noncomputable def activeBoxControlledContributionCertificate
    {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}
    (ρ : SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
      (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (j : { i // i ∈ M.compactActiveFinset ρ }) :
    { r : ℝ //
      DiffForm.integral (DiffForm.extd (DiffForm.fsmul (fun z => ρ j.1 z) ω))
        M.carrier = r } := by
  have hspec := activeBoxControlledCoverIndex_spec ρ hρ j
  cases hI : activeBoxControlledCoverIndex ρ hρ j with
  | interior C =>
      have hχV : tsupport (fun z => ρ j.1 z) ⊆ C.V := by
        simpa [hI, boxControlledCarrierCover] using hspec.2
      let Q :=
        (C.toInteriorLocalizedStokesPieceOfSmoothPartition ρ j.1 hω hχV).toLocalizedStokesPiece
          hω
      exact ⟨0, by simpa [Q] using Q.carrier_integral_eq_contribution⟩
  | boundary C =>
      have hχV : tsupport (fun z => ρ j.1 z) ⊆ C.V := by
        simpa [hI, boxControlledCarrierCover] using hspec.2
      let Q := C.toBoundaryLocalizedStokesPieceOfSmoothPartition ρ j.1 hω hχV
      have hQ := (Q.toLocalizedStokesPiece hω).carrier_integral_eq_contribution
      exact ⟨Q.boundaryContribution, by simpa [Q] using hQ⟩

/-- The real contribution associated to an active box-controlled partition element. -/
noncomputable def activeBoxControlledContribution
    {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}
    (ρ : SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
      (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (j : { i // i ∈ M.compactActiveFinset ρ }) : ℝ :=
  (activeBoxControlledContributionCertificate ρ hρ hω j).1

/-- Localized Stokes piece carried by one active box-controlled partition element. -/
noncomputable def activeBoxControlledLocalizedPiece
    {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}
    (ρ : SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
      (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (j : { i // i ∈ M.compactActiveFinset ρ }) : LocalizedStokesPiece M ω where
  χ := fun z => ρ j.1 z
  localized_differentiable :=
    ((DiffForm.isSmooth_fsmul (ρ.contDiff_apply_infty j.1) hω).differentiable (by simp))
  localized_extd_integrable :=
    M.integrableOn_topCoeff_extd_carrier_of_contDiff
      (DiffForm.isSmooth_fsmul (ρ.contDiff_apply_infty j.1) hω)
  contribution := activeBoxControlledContribution ρ hρ hω j
  carrier_integral_eq_contribution :=
    (activeBoxControlledContributionCertificate ρ hρ hω j).2

@[simp]
theorem activeBoxControlledLocalizedPiece_chi
    {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}
    (ρ : SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
      (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (j : { i // i ∈ M.compactActiveFinset ρ }) :
    (activeBoxControlledLocalizedPiece ρ hρ hω j).χ =
      fun z => ρ j.1 z :=
  rfl

/-- Finite localized Stokes assembly for an ambient smooth partition subordinate to the
box-controlled carrier cover. -/
theorem finite_boxControlled_localized_stokes_of_smoothPartition
    {M : SmoothDomain (n + 1)} {ω : DiffForm (n + 1) n}
    (ρ : SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
      (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    M.domainIntegral (DiffForm.extd ω) =
      ∑ j ∈ (M.compactActiveFinset ρ).attach,
        activeBoxControlledContribution ρ hρ hω j := by
  simpa [activeBoxControlledLocalizedPiece, activeBoxControlledContribution] using
    finite_localized_stokes_of_smoothPartition_on_active ρ
      (activeBoxControlledLocalizedPiece ρ hρ hω)
      (fun j => activeBoxControlledLocalizedPiece_chi ρ hρ hω j)

end SmoothDomain

end
