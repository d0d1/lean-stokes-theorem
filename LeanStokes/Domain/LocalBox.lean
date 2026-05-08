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
