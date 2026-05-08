/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic
import Mathlib.LinearAlgebra.StdBasis
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
  smooth_φ : ContDiff ℝ (⊤ : ℕ∞) φ
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

/-- Selected coordinate derivative of the defining function. -/
def partialDeriv (i : Fin d) (x : ℝSpace d) : ℝ :=
  fderiv ℝ M.φ x (Pi.single i (1 : ℝ))

/-- The selected coordinate derivative of a smooth defining function is continuous. -/
theorem continuous_partialDeriv (i : Fin d) :
    Continuous (M.partialDeriv i) := by
  simpa [partialDeriv] using
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).continuous.comp
      (M.smooth_φ.continuous_fderiv (by simp))

/-- The set where a selected coordinate derivative is positive is open. -/
theorem isOpen_pos_partialDeriv (i : Fin d) :
    IsOpen {x : ℝSpace d | 0 < M.partialDeriv i x} := by
  simpa using isOpen_lt continuous_const (M.continuous_partialDeriv i)

/-- The set where a selected coordinate derivative is negative is open. -/
theorem isOpen_neg_partialDeriv (i : Fin d) :
    IsOpen {x : ℝSpace d | M.partialDeriv i x < 0} := by
  simpa using isOpen_lt (M.continuous_partialDeriv i) continuous_const

/-- A positive selected coordinate derivative remains positive on an open neighborhood. -/
theorem exists_pos_partialDeriv_neighborhood {i : Fin d} {x : ℝSpace d}
    (hpos : 0 < M.partialDeriv i x) :
    ∃ U : Set (ℝSpace d), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, 0 < M.partialDeriv i y :=
  ⟨{y | 0 < M.partialDeriv i y}, M.isOpen_pos_partialDeriv i, hpos, fun _ hy => hy⟩

/-- A negative selected coordinate derivative remains negative on an open neighborhood. -/
theorem exists_neg_partialDeriv_neighborhood {i : Fin d} {x : ℝSpace d}
    (hneg : M.partialDeriv i x < 0) :
    ∃ U : Set (ℝSpace d), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, M.partialDeriv i y < 0 :=
  ⟨{y | M.partialDeriv i y < 0}, M.isOpen_neg_partialDeriv i, hneg, fun _ hy => hy⟩

/-- A nonzero selected coordinate derivative remains nonzero on an open neighborhood. -/
theorem exists_nonzero_partialDeriv_neighborhood {i : Fin d} {x : ℝSpace d}
    (h : M.partialDeriv i x ≠ 0) :
    ∃ U : Set (ℝSpace d), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, M.partialDeriv i y ≠ 0 := by
  by_cases hpos : 0 < M.partialDeriv i x
  · rcases M.exists_pos_partialDeriv_neighborhood hpos with ⟨U, hUo, hxU, hU⟩
    exact ⟨U, hUo, hxU, fun y hy => ne_of_gt (hU y hy)⟩
  · have hneg : M.partialDeriv i x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) h
    rcases M.exists_neg_partialDeriv_neighborhood hneg with ⟨U, hUo, hxU, hU⟩
    exact ⟨U, hUo, hxU, fun y hy => ne_of_lt (hU y hy)⟩

/-- At every boundary point, some selected coordinate derivative is nonzero. -/
theorem exists_nonzero_partialDeriv_at_boundary {x : ℝSpace d} (hx : x ∈ M.boundary) :
    ∃ i : Fin d, M.partialDeriv i x ≠ 0 := by
  by_contra h
  apply M.regular x hx
  push Not at h
  have hraw : ∀ i : Fin d, fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) = 0 := by
    intro i
    simpa [partialDeriv] using h i
  apply ContinuousLinearMap.ext
  intro v
  calc
    fderiv ℝ M.φ x v =
        fderiv ℝ M.φ x
          (∑ i, ((Pi.basisFun ℝ (Fin d)).repr v) i • (Pi.basisFun ℝ (Fin d)) i) := by
      rw [(Pi.basisFun ℝ (Fin d)).sum_repr v]
    _ = ∑ i, ((Pi.basisFun ℝ (Fin d)).repr v) i •
          fderiv ℝ M.φ x ((Pi.basisFun ℝ (Fin d)) i) := by
      simp [map_sum]
    _ = 0 := by
      simp [hraw]

/-- At every boundary point, some selected coordinate derivative has stable sign on an open
neighborhood. -/
theorem exists_partialDeriv_sign_neighborhood_at_boundary {x : ℝSpace d} (hx : x ∈ M.boundary) :
    ∃ i : Fin d, ∃ U : Set (ℝSpace d), IsOpen U ∧ x ∈ U ∧
      ((0 < M.partialDeriv i x ∧ ∀ y ∈ U, 0 < M.partialDeriv i y) ∨
        (M.partialDeriv i x < 0 ∧ ∀ y ∈ U, M.partialDeriv i y < 0)) := by
  rcases M.exists_nonzero_partialDeriv_at_boundary hx with ⟨i, hi⟩
  by_cases hpos : 0 < M.partialDeriv i x
  · rcases M.exists_pos_partialDeriv_neighborhood hpos with ⟨U, hUo, hxU, hU⟩
    exact ⟨i, U, hUo, hxU, Or.inl ⟨hpos, hU⟩⟩
  · have hneg : M.partialDeriv i x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi
    rcases M.exists_neg_partialDeriv_neighborhood hneg with ⟨U, hUo, hxU, hU⟩
    exact ⟨i, U, hUo, hxU, Or.inr ⟨hneg, hU⟩⟩

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

/-- A point of the carrier is either in the strict interior or on the boundary. -/
theorem mem_carrier_iff_mem_int_or_mem_boundary {x : ℝSpace d} :
    x ∈ M.carrier ↔ x ∈ M.int ∨ x ∈ M.boundary := by
  simp only [carrier, int, boundary, mem_setOf_eq]
  constructor
  · exact lt_or_eq_of_le
  · rintro (hx | hx)
    · exact le_of_lt hx
    · exact le_of_eq hx

/-- The carrier is contained in the union of the strict interior and boundary. -/
theorem carrier_subset_int_union_boundary : M.carrier ⊆ M.int ∪ M.boundary := by
  intro x hx
  exact (M.mem_carrier_iff_mem_int_or_mem_boundary.mp hx)

/-- The carrier is the union of the strict interior and boundary. -/
theorem carrier_eq_int_union_boundary : M.carrier = M.int ∪ M.boundary := by
  ext x
  simpa [Set.mem_union] using M.mem_carrier_iff_mem_int_or_mem_boundary (x := x)

/-- The strict interior is disjoint from the boundary. -/
theorem disjoint_int_boundary : Disjoint M.int M.boundary := by
  rw [Set.disjoint_left]
  intro x hx_int hx_boundary
  rw [mem_boundary] at hx_boundary
  rw [mem_int] at hx_int
  linarith

/-- The boundary is the carrier with the strict interior removed. -/
theorem boundary_eq_carrier_diff_int : M.boundary = M.carrier \ M.int := by
  ext x
  simp only [carrier, int, boundary, mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hx
    exact ⟨le_of_eq hx, by linarith⟩
  · intro hx
    exact le_antisymm hx.1 (le_of_not_gt hx.2)

theorem carrier_isCompact : IsCompact M.carrier := M.isCompact

/-- The boundary is compact because it is a closed subset of the compact carrier. -/
theorem boundary_isCompact : IsCompact M.boundary :=
  M.carrier_isCompact.of_isClosed_subset M.isClosed_boundary M.boundary_subset_carrier

/-- The strict interior set is contained in the topological interior of the carrier. -/
theorem int_subset_interior : M.int ⊆ interior M.carrier :=
  interior_maximal M.int_subset_carrier M.isOpen_int

end SmoothDomain

end
