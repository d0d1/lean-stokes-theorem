/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.SmoothDomain

/-!
# Boundary Orientation

Defines the induced orientation on the boundary of a smooth domain.

## Sign Convention

We use the "outward normal first" convention:
∫_{∂M} ω = ∫_M dω with boundary sign (-1)^(d-1) in local half-space coords.
-/

noncomputable section

open Topology Filter Set

namespace SmoothDomain

variable {d : ℕ} (M : SmoothDomain d)

/-- The outward unit normal direction at a boundary point.
Since M = {φ ≤ 0}, the outward direction is +∇φ (pointing away from M). -/
def outwardNormalDir (x : ℝSpace d) : ℝSpace d → ℝ :=
  fun v => fderiv ℝ M.φ x v

/-- The boundary orientation sign: (-1)^(d-1).
This encodes the "outward normal first" convention in half-space coordinates. -/
def boundaryOrientSign : ℝ := (-1 : ℝ) ^ (d - 1)

end SmoothDomain

end
