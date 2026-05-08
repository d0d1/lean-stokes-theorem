/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoundaryChartPatchCoordDomain

/-!
# Local Box Geometry for Smooth Domains

This module separates pure local box geometry from scalar cutoffs, forms, and
Stokes assembly.  Boundary chart boxes certify an original-side patch set whose
flattening image is a half-space box; interior boxes certify a full box inside
the carrier.
-/

noncomputable section

open Set MeasureTheory

namespace SmoothDomain

variable {n : ℕ}

/-- Pure geometry for one boundary chart half-space box. -/
structure BoundaryChartBox (M : SmoothDomain (n + 1)) where
  /-- Boundary center of the certified chart patch. -/
  x : ℝSpace (n + 1)
  /-- Determinant-sign-stable boundary chart patch. -/
  P : BoundaryChartPatch M x
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

namespace BoundaryChartBox

variable {M : SmoothDomain (n + 1)}

/-- Boundary-coordinate tail of the model half-space box. -/
def boundaryTail (G : BoundaryChartBox M) : Set (ℝSpace n) :=
  Icc (G.a ∘ Fin.succAbove (0 : Fin (n + 1)))
    (G.b ∘ Fin.succAbove (0 : Fin (n + 1)))

/-- The boundary-coordinate tail lies in the certified local coordinate domain. -/
theorem boundaryTail_subset_localCoordDomain (G : BoundaryChartBox M) :
    G.boundaryTail ⊆ G.P.localCoordDomain :=
  G.P.tailBox_subset_localCoordDomain_of_flattening_image_eq G.a G.b G.box_le
    G.box_zero_low G.U_subset_patch G.flattening_image_eq_box

/-- Build a boundary chart box from a model half-box contained in the target side of a chart patch.

The original-side set is the preimage of the model box under the flattening map, intersected with
the certified patch neighborhood.  This keeps measurability elementary while giving exact image
equality by the chart inverse on the model box. -/
def ofModelBoxSubsetPatch
    {x : ℝSpace (n + 1)} (P : BoundaryChartPatch M x) (a b : ℝSpace (n + 1))
    (hle : a ≤ b) (ha0 : a (0 : Fin (n + 1)) = 0)
    (hboxsub : Icc a b ⊆ { z |
      z ∈ (M.halfSpaceFlatteningChart P.i x P.h).target ∧
        (M.halfSpaceFlatteningChart P.i x P.h).symm z ∈ P.U }) :
    BoundaryChartBox M where
  x := x
  P := P
  U := (M.halfSpaceFlatteningMap P.i) ⁻¹' Icc a b ∩ P.U
  a := a
  b := b
  U_measurable :=
    (((M.contDiff_halfSpaceFlatteningMap P.i).continuous).measurable measurableSet_Icc).inter
      P.measurableSet_U
  U_subset_patch := by
    intro y hy
    exact hy.2
  U_subset_carrier := by
    intro y hy
    rw [M.mem_carrier_iff_halfSpaceFlatteningMap_mem P.i y]
    rw [HalfSpace]
    have hlow : a (0 : Fin (n + 1)) ≤ M.halfSpaceFlatteningMap P.i y (0 : Fin (n + 1)) :=
      hy.1.1 0
    simpa [ha0] using hlow
  flattening_image_eq_box := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.1
    · intro hz
      let e := M.halfSpaceFlatteningChart P.i x P.h
      have hzpatch := hboxsub hz
      have hright : M.halfSpaceFlatteningMap P.i (e.symm z) = z := by
        simpa [e] using e.right_inv hzpatch.1
      refine ⟨e.symm z, ?_, hright⟩
      constructor
      · simpa [hright] using hz
      · exact hzpatch.2
  box_le := hle
  box_zero_low := ha0

end BoundaryChartBox

/-- Pure geometry for one interior full box contained in the carrier. -/
structure InteriorBox (M : SmoothDomain (n + 1)) where
  /-- Lower corner of the interior box. -/
  a : ℝSpace (n + 1)
  /-- Upper corner of the interior box. -/
  b : ℝSpace (n + 1)
  box_le : a ≤ b
  box_subset_carrier : Icc a b ⊆ M.carrier

end SmoothDomain

end
