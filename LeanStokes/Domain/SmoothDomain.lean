/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

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

@[simp] theorem mem_carrier {x : ℝSpace d} : x ∈ M.carrier ↔ M.φ x ≤ 0 :=
  Iff.rfl

@[simp] theorem mem_boundary {x : ℝSpace d} : x ∈ M.boundary ↔ M.φ x = 0 :=
  Iff.rfl

@[simp] theorem mem_int {x : ℝSpace d} : x ∈ M.int ↔ M.φ x < 0 :=
  Iff.rfl

/-- The defining function is continuous. -/
theorem continuous_φ : Continuous M.φ :=
  M.smooth_φ.continuous

/-- The carrier `{x | φ x ≤ 0}` is closed. -/
theorem isClosed_carrier : IsClosed M.carrier := by
  simpa [carrier] using isClosed_le M.continuous_φ continuous_const

/-- The carrier `{x | φ x ≤ 0}` is measurable. -/
theorem measurableSet_carrier : MeasurableSet M.carrier :=
  M.isClosed_carrier.measurableSet

/-- The boundary `{x | φ x = 0}` is closed. -/
theorem isClosed_boundary : IsClosed M.boundary := by
  simpa [boundary] using isClosed_eq M.continuous_φ continuous_const

/-- The boundary `{x | φ x = 0}` is measurable. -/
theorem measurableSet_boundary : MeasurableSet M.boundary :=
  M.isClosed_boundary.measurableSet

/-- The strict interior set `{x | φ x < 0}` is open. -/
theorem isOpen_int : IsOpen M.int := by
  simpa [int] using isOpen_lt M.continuous_φ continuous_const

/-- The strict interior set `{x | φ x < 0}` is measurable. -/
theorem measurableSet_int : MeasurableSet M.int :=
  M.isOpen_int.measurableSet

theorem boundary_subset_carrier : M.boundary ⊆ M.carrier := by
  intro x hx
  simp only [boundary, carrier, Set.mem_setOf_eq] at *
  linarith

theorem int_subset_carrier : M.int ⊆ M.carrier := by
  intro x hx
  simp only [int, carrier, Set.mem_setOf_eq] at *
  linarith

theorem carrier_isCompact : IsCompact M.carrier := M.isCompact

/-- The boundary is compact because it is a closed subset of the compact carrier. -/
theorem boundary_isCompact : IsCompact M.boundary :=
  M.carrier_isCompact.of_isClosed_subset M.isClosed_boundary M.boundary_subset_carrier

/-- The strict interior set is contained in the topological interior of the carrier. -/
theorem int_subset_interior : M.int ⊆ interior M.carrier :=
  interior_maximal M.int_subset_carrier M.isOpen_int

end SmoothDomain

end
