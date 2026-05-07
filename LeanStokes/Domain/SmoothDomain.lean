/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Smooth Domains with Boundary

A smooth domain with boundary in ℝⁿ is defined via a smooth defining function:
M = {x : φ(x) ≤ 0} where φ : ℝⁿ → ℝ is smooth with Dφ ≠ 0 on ∂M = {φ = 0}.
-/

noncomputable section

open Topology Filter Set

/-- A smooth domain with boundary in ℝᵈ. -/
structure SmoothDomain (d : ℕ) where
  φ : ℝSpace d → ℝ
  smooth_φ : ContDiff ℝ ⊤ φ
  isCompact : IsCompact {x : ℝSpace d | φ x ≤ 0}
  regular : ∀ x : ℝSpace d, φ x = 0 → fderiv ℝ φ x ≠ 0

namespace SmoothDomain

variable {d : ℕ} (M : SmoothDomain d)

/-- The underlying set: {x | φ(x) ≤ 0}. -/
def carrier : Set (ℝSpace d) := {x | M.φ x ≤ 0}

/-- The boundary: {x | φ(x) = 0}. -/
def boundary : Set (ℝSpace d) := {x | M.φ x = 0}

/-- The strict interior: {x | φ(x) < 0}. -/
def int : Set (ℝSpace d) := {x | M.φ x < 0}

theorem boundary_subset_carrier : M.boundary ⊆ M.carrier := by
  intro x hx
  simp only [boundary, carrier, Set.mem_setOf_eq] at *
  linarith

theorem int_subset_carrier : M.int ⊆ M.carrier := by
  intro x hx
  simp only [int, carrier, Set.mem_setOf_eq] at *
  linarith

theorem carrier_isCompact : IsCompact M.carrier := M.isCompact

end SmoothDomain

end
