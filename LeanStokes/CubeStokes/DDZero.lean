/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Bridge
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# d² = 0: Nilpotency of the Exterior Derivative

Demonstrates d² = 0 for differential forms in our setting, using both
the abstract mathlib `extDeriv_extDeriv` theorem and its coordinate
consequence via the bridge theorem.

## Main results

* `CubeStokes.dd_zero_abstract`: `extDeriv (extDeriv ω) = 0` for C^∞ forms (from mathlib).
* `CubeStokes.dd_zero_coord_top`: The top-form evaluation of `extDeriv (extDeriv ω)` is zero.
* `CubeStokes.stokes_dd_zero`: Stokes' identity for `d²ω` gives zero on both sides.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function VectorField
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- **d² = 0** (abstract): The second exterior derivative of a smooth form is zero.
This is `extDeriv_extDeriv` from mathlib, restated for our setting. -/
theorem dd_zero_abstract
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    extDeriv (extDeriv ω) = 0 :=
  extDeriv_extDeriv hω (by
    simpa [minSmoothness_of_isRCLikeNormedField] using
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤) :
        (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))

/-- **d² = 0** (coordinate consequence): Evaluating `extDeriv(extDeriv ω)` on any
tuple of vectors gives zero. In particular, the top-form coefficient is zero. -/
theorem dd_zero_coord_top
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (x : Fin (n + 1) → ℝ) (v : Fin (n + 1 + 1) → Fin (n + 1) → ℝ) :
    extDeriv (extDeriv ω) x v = 0 := by
  rw [dd_zero_abstract ω hω]
  simp

/-- **Stokes for d²ω is trivial**: Since d²ω = 0, integrating any evaluation of
`extDeriv(extDeriv ω)` over a box gives zero. This is a cohomological
consequence: the boundary integral of an exact form's derivative vanishes. -/
theorem stokes_dd_zero
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (a b : Fin (n + 1) → ℝ)
    (v : Fin (n + 1 + 1) → Fin (n + 1) → ℝ) :
    (∫ x in Icc a b, extDeriv (extDeriv ω) x v) = 0 := by
  have h : extDeriv (extDeriv ω) = 0 := dd_zero_abstract ω hω
  simp [h]

end CubeStokes

end
