/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.Coordinate
import LeanStokes.Domain.SmoothDomain
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Boundary Flattening Coordinates

For a regular sublevel domain `M = {x | M.φ x ≤ 0}`, replacing one coordinate by
`-M.φ` sends the carrier condition to an upper half-space condition in that
coordinate.  The local diffeomorphism and determinant API built on this map is
developed separately.
-/

noncomputable section

open Topology Filter Set

namespace SmoothDomain

variable {d : ℕ} (M : SmoothDomain d)

/-- Coordinate replacement map used for local boundary flattening.

The chosen coordinate is `-φ`, so `φ ≤ 0` becomes the upper-half-space condition
`0 ≤ coord`.  Other coordinates are unchanged. -/
def flatteningMap (i : Fin d) : ℝSpace d → ℝSpace d :=
  fun x j => if j = i then -M.φ x else x j

/-- First-coordinate-facing version of `flatteningMap`.

It sends the selected flattening coordinate to coordinate `0`, so membership in the domain becomes
membership in the standard first-coordinate half-space.  The coordinate swap has determinant `1`
when `i = 0` and `-1` otherwise, so orientation-sensitive statements must record its sign. -/
def halfSpaceFlatteningMap [NeZero d] (i : Fin d) : ℝSpace d → ℝSpace d :=
  fun x => Coordinate.moveToZero i (M.flatteningMap i x)

@[simp] theorem flatteningMap_apply_self (i : Fin d) (x : ℝSpace d) :
    M.flatteningMap i x i = -M.φ x := by
  simp [flatteningMap]

@[simp] theorem flatteningMap_apply_ne {i j : Fin d} (hji : j ≠ i) (x : ℝSpace d) :
    M.flatteningMap i x j = x j := by
  simp [flatteningMap, hji]

@[simp] theorem halfSpaceFlatteningMap_apply_zero [NeZero d] (i : Fin d) (x : ℝSpace d) :
    M.halfSpaceFlatteningMap i x (0 : Fin d) = -M.φ x := by
  simp [halfSpaceFlatteningMap]

/-- The carrier condition is the nonnegative condition on the replaced coordinate. -/
theorem mem_carrier_iff_flatteningMap_coord_nonneg (i : Fin d) (x : ℝSpace d) :
    x ∈ M.carrier ↔ 0 ≤ M.flatteningMap i x i := by
  simp [carrier]

/-- The boundary condition is the zero condition on the replaced coordinate. -/
theorem mem_boundary_iff_flatteningMap_coord_eq_zero (i : Fin d) (x : ℝSpace d) :
    x ∈ M.boundary ↔ M.flatteningMap i x i = 0 := by
  simp [boundary]

/-- The strict interior condition is the positive condition on the replaced coordinate. -/
theorem mem_int_iff_flatteningMap_coord_pos (i : Fin d) (x : ℝSpace d) :
    x ∈ M.int ↔ 0 < M.flatteningMap i x i := by
  simp [int]

/-- The carrier condition becomes membership in the standard first-coordinate half-space. -/
theorem mem_carrier_iff_halfSpaceFlatteningMap_mem [NeZero d] (i : Fin d) (x : ℝSpace d) :
    x ∈ M.carrier ↔ M.halfSpaceFlatteningMap i x ∈ HalfSpace d := by
  rw [M.mem_carrier_iff_flatteningMap_coord_nonneg i x]
  simp [halfSpaceFlatteningMap, HalfSpace]

/-- The boundary condition becomes membership in the standard first-coordinate boundary face. -/
theorem mem_boundary_iff_halfSpaceFlatteningMap_mem [NeZero d] (i : Fin d) (x : ℝSpace d) :
    x ∈ M.boundary ↔ M.halfSpaceFlatteningMap i x ∈ HalfSpaceBdry d := by
  rw [M.mem_boundary_iff_flatteningMap_coord_eq_zero i x]
  simp [halfSpaceFlatteningMap, HalfSpaceBdry]

/-- The strict interior condition becomes membership in the standard open half-space. -/
theorem mem_int_iff_halfSpaceFlatteningMap_mem [NeZero d] (i : Fin d) (x : ℝSpace d) :
    x ∈ M.int ↔ M.halfSpaceFlatteningMap i x ∈ HalfSpaceOpen d := by
  rw [M.mem_int_iff_flatteningMap_coord_pos i x]
  simp [halfSpaceFlatteningMap, HalfSpaceOpen]

/-- The coordinate replacement map is smooth. -/
theorem contDiff_flatteningMap (i : Fin d) :
    ContDiff ℝ ⊤ (M.flatteningMap i) := by
  apply contDiff_pi'
  intro j
  by_cases hji : j = i
  · subst j
    simpa [flatteningMap] using M.smooth_φ.neg
  · simpa [flatteningMap, hji] using
      ((contDiff_apply ℝ ℝ j) : ContDiff ℝ ⊤ fun x : ℝSpace d => x j)

/-- Derivative of the coordinate replacement map. -/
theorem fderiv_flatteningMap (i : Fin d) (x : ℝSpace d) :
    fderiv ℝ (M.flatteningMap i) x =
      ContinuousLinearMap.pi (fun j : Fin d =>
        if j = i then -fderiv ℝ M.φ x else ContinuousLinearMap.proj j) := by
  rw [fderiv_pi]
  · ext v j
    by_cases hji : j = i
    · subst j
      simp [flatteningMap]
    · have hproj :
          fderiv ℝ (fun x : ℝSpace d => x j) x = ContinuousLinearMap.proj j := by
        exact (ContinuousLinearMap.fderiv
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) (x := x))
      simp [flatteningMap, hji, hproj]
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [flatteningMap] using
        (M.smooth_φ.differentiable (by simp)).differentiableAt.neg
    · simpa [flatteningMap, hji] using
        ((contDiff_apply ℝ ℝ j).differentiable
          (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt

/-- The flattening map has derivative equal to its `fderiv`. -/
theorem hasFDerivAt_flatteningMap (i : Fin d) (x : ℝSpace d) :
    HasFDerivAt (M.flatteningMap i) (fderiv ℝ (M.flatteningMap i) x) x :=
  ((M.contDiff_flatteningMap i).differentiable (by simp)).differentiableAt.hasFDerivAt

/-- The first-coordinate-facing flattening map has derivative obtained by composing the coordinate
swap with the derivative of the coordinate replacement map. -/
theorem hasFDerivAt_halfSpaceFlatteningMap [NeZero d] (i : Fin d) (x : ℝSpace d) :
    HasFDerivAt (M.halfSpaceFlatteningMap i)
      ((Coordinate.moveToZero i : ℝSpace d →L[ℝ] ℝSpace d).comp
        (fderiv ℝ (M.flatteningMap i) x)) x := by
  simpa [halfSpaceFlatteningMap, Function.comp_def] using
    (Coordinate.moveToZero i : ℝSpace d →L[ℝ] ℝSpace d).hasFDerivAt.comp x
      (M.hasFDerivAt_flatteningMap i x)

/-- Derivative of the first-coordinate-facing flattening map. -/
theorem fderiv_halfSpaceFlatteningMap [NeZero d] (i : Fin d) (x : ℝSpace d) :
    fderiv ℝ (M.halfSpaceFlatteningMap i) x =
      ((Coordinate.moveToZero i : ℝSpace d →L[ℝ] ℝSpace d).comp
        (fderiv ℝ (M.flatteningMap i) x)) := by
  exact (M.hasFDerivAt_halfSpaceFlatteningMap i x).fderiv

/-- Matrix of the flattening derivative in the standard basis.

It is the identity matrix with the selected row replaced by the row of `-dφ`. -/
theorem toMatrix_fderiv_flatteningMap (i : Fin d) (x : ℝSpace d) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
      (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) =
    Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) i
      (fun k => -fderiv ℝ M.φ x ((Pi.basisFun ℝ (Fin d)) k)) := by
  ext j k
  rw [LinearMap.toMatrix_apply]
  rw [M.fderiv_flatteningMap]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji, Matrix.one_apply, Pi.single_apply]

/-- The determinant of the flattening derivative is the negative selected partial derivative. -/
theorem det_fderiv_flatteningMap (i : Fin d) (x : ℝSpace d) :
    LinearMap.det (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) =
      -fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) := by
  let b : Module.Basis (Fin d) ℝ (ℝSpace d) := Pi.basisFun ℝ (Fin d)
  rw [← LinearMap.det_toMatrix b
    (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d)]
  rw [M.toMatrix_fderiv_flatteningMap]
  let row : Fin d → ℝ := fun k => -fderiv ℝ M.φ x (b k)
  have hrow : row = ∑ k, row k • (1 : Matrix (Fin d) (Fin d) ℝ) k := by
    ext k
    simp [row, Matrix.one_apply]
  change (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) i row).det =
    -fderiv ℝ M.φ x (Pi.single i (1 : ℝ))
  rw [hrow]
  rw [Matrix.det_updateRow_sum]
  simp [row, b]

/-- The flattening derivative has nonzero determinant when the selected partial derivative is
nonzero. -/
theorem det_fderiv_flatteningMap_ne_zero (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    LinearMap.det (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) ≠ 0 := by
  rw [M.det_fderiv_flatteningMap]
  exact neg_ne_zero.mpr h

/-- Nonvanishing determinant of the flattening derivative is equivalent to the selected partial
derivative being nonzero. -/
theorem det_fderiv_flatteningMap_ne_zero_iff (i : Fin d) (x : ℝSpace d) :
    LinearMap.det (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) ≠ 0 ↔
      fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0 := by
  rw [M.det_fderiv_flatteningMap]
  exact neg_ne_zero

/-- Determinant of the first-coordinate-facing flattening derivative. -/
theorem det_fderiv_halfSpaceFlatteningMap [NeZero d] (i : Fin d) (x : ℝSpace d) :
    LinearMap.det
      (fderiv ℝ (M.halfSpaceFlatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) =
      (Equiv.Perm.sign (Equiv.swap (0 : Fin d) i) : ℝ) *
        (-fderiv ℝ M.φ x (Pi.single i (1 : ℝ))) := by
  rw [M.fderiv_halfSpaceFlatteningMap]
  change LinearMap.det
      (((Coordinate.moveToZero i : ℝSpace d →L[ℝ] ℝSpace d).toLinearMap).comp
        (fderiv ℝ (M.flatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d)) =
      (Equiv.Perm.sign (Equiv.swap (0 : Fin d) i) : ℝ) *
        (-fderiv ℝ M.φ x (Pi.single i (1 : ℝ)))
  rw [LinearMap.det_comp, Coordinate.det_moveToZero, M.det_fderiv_flatteningMap]

/-- The first-coordinate-facing flattening derivative has nonzero determinant when the selected
partial derivative is nonzero. -/
theorem det_fderiv_halfSpaceFlatteningMap_ne_zero [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    LinearMap.det
      (fderiv ℝ (M.halfSpaceFlatteningMap i) x : ℝSpace d →ₗ[ℝ] ℝSpace d) ≠ 0 := by
  rw [M.det_fderiv_halfSpaceFlatteningMap]
  have hswap : (Equiv.Perm.sign (Equiv.swap (0 : Fin d) i) : ℝ) ≠ 0 := by
    simp
  exact mul_ne_zero hswap (neg_ne_zero.mpr h)

/-- The continuous linear equivalence supplied by a flattening derivative whose selected partial
derivative is nonzero. -/
def flatteningFDerivEquiv (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    ℝSpace d ≃L[ℝ] ℝSpace d :=
  (fderiv ℝ (M.flatteningMap i) x).toContinuousLinearEquivOfDetNeZero
    (by simpa using M.det_fderiv_flatteningMap_ne_zero i x h)

@[simp] theorem coe_flatteningFDerivEquiv (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    (M.flatteningFDerivEquiv i x h : ℝSpace d →L[ℝ] ℝSpace d) =
      fderiv ℝ (M.flatteningMap i) x := by
  simp [flatteningFDerivEquiv]

/-- Derivative witness for the flattening map using the generated continuous linear equivalence. -/
theorem hasFDerivAt_flatteningMap_equiv (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    HasFDerivAt (M.flatteningMap i)
      (M.flatteningFDerivEquiv i x h : ℝSpace d →L[ℝ] ℝSpace d) x := by
  simpa using M.hasFDerivAt_flatteningMap i x

/-- Local boundary-flattening chart at a point where the selected partial derivative is nonzero.

This chart still flattens to the selected coordinate `i`; a later coordinate permutation moves that
coordinate to the first-coordinate half-space model. -/
def flatteningChart (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    OpenPartialHomeomorph (ℝSpace d) (ℝSpace d) :=
  ((M.contDiff_flatteningMap i).contDiffAt).toOpenPartialHomeomorph
    (M.flatteningMap i) (M.hasFDerivAt_flatteningMap_equiv i x h) (by simp)

/-- Local boundary-flattening chart whose target coordinates use the standard first-coordinate
half-space convention. -/
def halfSpaceFlatteningChart [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    OpenPartialHomeomorph (ℝSpace d) (ℝSpace d) :=
  (M.flatteningChart i x h).transHomeomorph (Coordinate.moveToZeroHomeomorph i)

@[simp] theorem flatteningChart_coe (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    (M.flatteningChart i x h : ℝSpace d → ℝSpace d) = M.flatteningMap i :=
  rfl

@[simp] theorem halfSpaceFlatteningChart_coe [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    (M.halfSpaceFlatteningChart i x h : ℝSpace d → ℝSpace d) =
      M.halfSpaceFlatteningMap i :=
  rfl

/-- The center point belongs to the source of its flattening chart. -/
theorem mem_flatteningChart_source (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    x ∈ (M.flatteningChart i x h).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((M.contDiff_flatteningMap i).contDiffAt)
    (M.hasFDerivAt_flatteningMap_equiv i x h) (by simp)

/-- The image of the center point belongs to the target of its flattening chart. -/
theorem image_mem_flatteningChart_target (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    M.flatteningMap i x ∈ (M.flatteningChart i x h).target :=
  ContDiffAt.image_mem_toOpenPartialHomeomorph_target
    ((M.contDiff_flatteningMap i).contDiffAt)
    (M.hasFDerivAt_flatteningMap_equiv i x h) (by simp)

/-- The center point belongs to the source of its first-coordinate-facing flattening chart. -/
theorem mem_halfSpaceFlatteningChart_source [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    x ∈ (M.halfSpaceFlatteningChart i x h).source := by
  simpa [halfSpaceFlatteningChart] using M.mem_flatteningChart_source i x h

/-- The center image belongs to the target of its first-coordinate-facing flattening chart. -/
theorem image_mem_halfSpaceFlatteningChart_target [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) :
    M.halfSpaceFlatteningMap i x ∈ (M.halfSpaceFlatteningChart i x h).target := by
  simpa [halfSpaceFlatteningChart, halfSpaceFlatteningMap, Coordinate.moveToZeroHomeomorph] using
    M.image_mem_flatteningChart_target i x h

/-- Carrier membership expressed using the total function underlying a flattening chart. -/
theorem mem_carrier_iff_flatteningChart_coord_nonneg (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) (y : ℝSpace d) :
    y ∈ M.carrier ↔ 0 ≤ (M.flatteningChart i x h y) i := by
  simp [flatteningChart, M.mem_carrier_iff_flatteningMap_coord_nonneg i y]

/-- Boundary membership expressed using the total function underlying a flattening chart. -/
theorem mem_boundary_iff_flatteningChart_coord_eq_zero (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) (y : ℝSpace d) :
    y ∈ M.boundary ↔ (M.flatteningChart i x h y) i = 0 := by
  simp [flatteningChart, M.mem_boundary_iff_flatteningMap_coord_eq_zero i y]

/-- Strict interior membership expressed using the total function underlying a flattening chart. -/
theorem mem_int_iff_flatteningChart_coord_pos (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) (y : ℝSpace d) :
    y ∈ M.int ↔ 0 < (M.flatteningChart i x h y) i := by
  simp [flatteningChart, M.mem_int_iff_flatteningMap_coord_pos i y]

/-- Carrier membership expressed using the total function underlying a first-coordinate-facing
flattening chart. -/
theorem mem_carrier_iff_halfSpaceFlatteningChart_mem [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) (y : ℝSpace d) :
    y ∈ M.carrier ↔ M.halfSpaceFlatteningChart i x h y ∈ HalfSpace d := by
  simpa using M.mem_carrier_iff_halfSpaceFlatteningMap_mem i y

/-- Boundary membership expressed using the total function underlying a first-coordinate-facing
flattening chart. -/
theorem mem_boundary_iff_halfSpaceFlatteningChart_mem [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) (y : ℝSpace d) :
    y ∈ M.boundary ↔ M.halfSpaceFlatteningChart i x h y ∈ HalfSpaceBdry d := by
  simpa using M.mem_boundary_iff_halfSpaceFlatteningMap_mem i y

/-- Strict interior membership via the total function underlying a first-coordinate-facing
flattening chart. -/
theorem mem_int_iff_halfSpaceFlatteningChart_mem [NeZero d] (i : Fin d) (x : ℝSpace d)
    (h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0) (y : ℝSpace d) :
    y ∈ M.int ↔ M.halfSpaceFlatteningChart i x h y ∈ HalfSpaceOpen d := by
  simpa using M.mem_int_iff_halfSpaceFlatteningMap_mem i y

/-- At every boundary point, some standard coordinate has nonzero derivative. -/
theorem exists_nonzero_fderiv_stdBasis {x : ℝSpace d} (hx : x ∈ M.boundary) :
    ∃ i : Fin d, fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0 := by
  simpa [SmoothDomain.partialDeriv] using M.exists_nonzero_partialDeriv_at_boundary hx

/-- Every boundary point admits a flattening chart for a suitable coordinate. -/
theorem exists_flatteningChart_at_boundary {x : ℝSpace d} (hx : x ∈ M.boundary) :
    ∃ i, ∃ h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0,
      x ∈ (M.flatteningChart i x h).source := by
  rcases M.exists_nonzero_fderiv_stdBasis hx with ⟨i, hi⟩
  exact ⟨i, hi, M.mem_flatteningChart_source i x hi⟩

/-- Every boundary point admits a first-coordinate-facing flattening chart for a suitable
coordinate. -/
theorem exists_halfSpaceFlatteningChart_at_boundary [NeZero d] {x : ℝSpace d}
    (hx : x ∈ M.boundary) :
    ∃ i, ∃ h : fderiv ℝ M.φ x (Pi.single i (1 : ℝ)) ≠ 0,
      x ∈ (M.halfSpaceFlatteningChart i x h).source := by
  rcases M.exists_nonzero_fderiv_stdBasis hx with ⟨i, hi⟩
  exact ⟨i, hi, M.mem_halfSpaceFlatteningChart_source i x hi⟩

end SmoothDomain

end
