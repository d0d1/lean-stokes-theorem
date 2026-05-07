/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic

/-!
# Half-Space Model

The upper half-space Hⁿ = {x ∈ ℝⁿ : x₀ ≥ 0} is the local model
for manifolds with boundary near boundary points.

We use the *first* coordinate x₀ as the boundary-defining coordinate
(convention: domain is {x₀ ≥ 0}, boundary is {x₀ = 0}).
This avoids the Fin.last definitional issues with variable dimension.
-/

noncomputable section

open Set Topology Filter

variable {d : ℕ}

/-- The upper half-space: points whose first coordinate (index 0) is ≥ 0. -/
def HalfSpace (d : ℕ) [NeZero d] : Set (ℝSpace d) :=
  {x | (0 : ℝ) ≤ x (0 : Fin d)}

/-- The boundary of the half-space: first coordinate = 0. -/
def HalfSpaceBdry (d : ℕ) [NeZero d] : Set (ℝSpace d) :=
  {x | x (0 : Fin d) = 0}

/-- The open half-space: first coordinate > 0. -/
def HalfSpaceOpen (d : ℕ) [NeZero d] : Set (ℝSpace d) :=
  {x | (0 : ℝ) < x (0 : Fin d)}

namespace HalfSpace

variable [NeZero d]

theorem bdry_subset : HalfSpaceBdry d ⊆ HalfSpace d := by
  intro x hx
  simp only [HalfSpaceBdry, HalfSpace, Set.mem_setOf_eq] at *
  rw [hx]

theorem open_subset : HalfSpaceOpen d ⊆ HalfSpace d := by
  intro x hx
  simp only [HalfSpaceOpen, HalfSpace, Set.mem_setOf_eq] at *
  linarith

end HalfSpace

end
