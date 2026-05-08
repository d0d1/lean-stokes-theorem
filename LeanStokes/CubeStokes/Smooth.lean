/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Theorem
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Stokes' Theorem for Smooth Forms

A user-friendly version of the cubical Stokes theorem with smooth-form hypotheses.

## Main results

* `CubeStokes.stokes_contDiffAt_box`: Stokes on a box from pointwise ambient
  smoothness at every point of the closed box.
* `CubeStokes.stokes_smooth`: Stokes on a box for globally smooth coefficient functions.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- Stokes' theorem on a box from pointwise ambient smoothness on the closed box.

The hypothesis is deliberately stated with `ContDiffAt` at every point of
`Icc a b`, not with a relative `ContDiffOn` condition. This is the local form
needed for chart-box arguments: the coefficients only need ambient smooth
extensions near the model box, not globally smooth total functions. -/
theorem stokes_contDiffAt_box (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (ω : CoordNForm n)
    (hω : ∀ i, ∀ x ∈ Icc a b, ContDiffAt ℝ (⊤ : ℕ∞) (ω i) x) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b := by
  apply stokes_on_box a b hle ω ∅ Set.countable_empty
  -- (1) Continuity of signed coefficients on [a, b]
  · intro i x hx
    exact (continuous_const.continuousAt.mul (hω i x hx).continuousAt).continuousWithinAt
  -- (2) Differentiability on the open box
  · intro x hx i
    have hxIcc : x ∈ Icc a b := by
      rw [Set.mem_Icc]
      constructor
      · intro j
        exact le_of_lt ((hx.1 j trivial).1)
      · intro j
        exact le_of_lt ((hx.1 j trivial).2)
    exact ((hω i x hxIcc).differentiableAt (by simp)).hasFDerivAt.const_mul _
  -- (3) Integrability of the exterior derivative on the compact box
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_finset_sum
    intro i _ x hx
    have hfd : ContinuousAt (fderiv ℝ (ω i)) x :=
      ContDiffAt.continuousAt_fderiv (hω i x hx) (by simp)
    have happ : ContinuousAt (fun y => fderiv ℝ (ω i) y (Pi.single i 1)) x := by
      simpa only [Function.comp_apply] using
        ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous.continuousAt.comp hfd)
    exact (continuous_const.continuousAt.mul happ).continuousWithinAt

/-- Stokes' theorem for smooth forms on a non-degenerate box.

If `ω` is a coordinate `n`-form with smooth (C^∞) coefficients, then on any
non-degenerate box `[a, b]` (with `a ≤ b`):

  `∫_{[a,b]} dω = ∫_{∂[a,b]} ω`
-/
theorem stokes_smooth (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (ω : CoordNForm n) (hω : IsSmooth ω) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b := by
  exact stokes_contDiffAt_box a b hle ω (fun i x _ => (hω i).contDiffAt)

end CubeStokes

end
