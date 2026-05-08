/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatch
import LeanStokes.Domain.PartitionOfUnity

/-!
# Boundary/Interior Covers of Smooth Domains

This module builds the honest open cover of a regular sublevel carrier by its
strict interior and boundary-flattening chart patches.  Extending this cover by
the carrier complement gives a global ambient cover, suitable for smooth
partitions of unity whose active finite sets satisfy ambient local sum-to-one
near the carrier.
-/

noncomputable section

open Set
open scoped Topology Manifold

namespace SmoothDomain

variable {d : ℕ} [NeZero d] (M : SmoothDomain d)

/-- A chosen determinant-sign-stable boundary chart patch at each boundary point. -/
def boundaryPatchAt (x : M.boundary) : BoundaryChartPatch M x :=
  Classical.choice (M.exists_boundaryChartPatch_at_boundary x.property)

/-- Index type for the carrier cover by the strict interior and boundary patches.

`none` indexes `M.int`; `some x` indexes the chosen boundary patch centered at the boundary point
`x`.  After applying `ambientCoverWithComplement`, there is one more outer `Option`: outer `none`
indexes the carrier complement. -/
abbrev BoundaryInteriorCoverIndex : Type :=
  Option M.boundary

/-- The carrier cover whose `none` member is the strict interior and whose boundary members are
chosen boundary chart patch neighborhoods. -/
def boundaryInteriorCover : M.BoundaryInteriorCoverIndex → Set (ℝSpace d)
  | none => M.int
  | some x => (M.boundaryPatchAt x).U

@[simp]
theorem boundaryInteriorCover_none :
    M.boundaryInteriorCover none = M.int :=
  rfl

@[simp]
theorem boundaryInteriorCover_some (x : M.boundary) :
    M.boundaryInteriorCover (some x) = (M.boundaryPatchAt x).U :=
  rfl

/-- In the complement-extended ambient cover, outer `none` is the carrier complement. -/
@[simp]
theorem ambientBoundaryInteriorCover_outer_none :
    M.ambientCoverWithComplement M.boundaryInteriorCover none = M.carrierᶜ :=
  rfl

/-- In the complement-extended ambient cover, `some none` is the strict interior. -/
@[simp]
theorem ambientBoundaryInteriorCover_inner_none :
    M.ambientCoverWithComplement M.boundaryInteriorCover (some none) = M.int :=
  rfl

/-- In the complement-extended ambient cover, `some (some x)` is the chosen boundary patch at `x`. -/
@[simp]
theorem ambientBoundaryInteriorCover_inner_some (x : M.boundary) :
    M.ambientCoverWithComplement M.boundaryInteriorCover (some (some x)) =
      (M.boundaryPatchAt x).U :=
  rfl

/-- Boundary patch centers belong to their chosen patch neighborhoods. -/
theorem boundaryPatchAt_center_mem_U (x : M.boundary) :
    (x : ℝSpace d) ∈ (M.boundaryPatchAt x).U :=
  (M.boundaryPatchAt x).center_mem_U

/-- The boundary/interior carrier cover is open. -/
theorem isOpen_boundaryInteriorCover :
    ∀ i, IsOpen (M.boundaryInteriorCover i) := by
  intro i
  cases i with
  | none =>
      simpa [boundaryInteriorCover] using M.isOpen_int
  | some x =>
      simpa [boundaryInteriorCover] using (M.boundaryPatchAt x).isOpen_U

/-- The strict interior plus chosen boundary patch neighborhoods cover the carrier. -/
theorem carrier_subset_iUnion_boundaryInteriorCover :
    M.carrier ⊆ ⋃ i, M.boundaryInteriorCover i := by
  intro x hx
  rcases M.mem_carrier_iff_mem_int_or_mem_boundary.mp hx with hx_int | hx_boundary
  · exact mem_iUnion.mpr ⟨none, by simpa [boundaryInteriorCover] using hx_int⟩
  · refine mem_iUnion.mpr ⟨some ⟨x, hx_boundary⟩, ?_⟩
    simpa [boundaryInteriorCover] using
      M.boundaryPatchAt_center_mem_U ⟨x, hx_boundary⟩

/-- The complement-extended boundary/interior cover has a global ambient smooth partition of unity
subordinate to it. -/
theorem exists_smoothPartition_subordinate_ambientBoundaryInteriorCover :
    ∃ ρ : SmoothPartitionOfUnity
        (Option M.BoundaryInteriorCoverIndex) (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ,
      ρ.IsSubordinate (M.ambientCoverWithComplement M.boundaryInteriorCover) :=
  M.exists_smoothPartition_subordinate_ambientCoverWithComplement
    M.boundaryInteriorCover M.isOpen_boundaryInteriorCover
    M.carrier_subset_iUnion_boundaryInteriorCover

end SmoothDomain

end
