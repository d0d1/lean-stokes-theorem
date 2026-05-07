/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Theorem
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Stokes' Theorem for Smooth Forms

A user-friendly version of the cubical Stokes theorem with smooth-form hypotheses.

## Main results

* `CubeStokes.stokes_smooth`: Stokes on a box for smooth coefficient functions.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- Stokes' theorem for smooth forms on a non-degenerate box.

If `ω` is a coordinate `n`-form with smooth (C^∞) coefficients, then on any
non-degenerate box `[a, b]` (with `a ≤ b`):

  `∫_{[a,b]} dω = ∫_{∂[a,b]} ω`
-/
theorem stokes_smooth (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (ω : CoordNForm n) (hω : IsSmooth ω) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b := by
  apply stokes_on_box a b hle ω ∅ Set.countable_empty
  -- (1) Continuity of signed coefficients on [a, b]
  · intro i
    exact (continuous_const.mul (hω i).continuous).continuousOn
  -- (2) Differentiability: signedCoeff ω i has the correct derivative
  · intro x _ i
    exact ((hω i).differentiable (by simp)).differentiableAt.hasFDerivAt.const_mul _
  -- (3) Integrability of the exterior derivative on the compact box
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_finset_sum
    intro i _
    have h1 : Continuous (fderiv ℝ (ω i)) := (hω i).continuous_fderiv (by simp)
    have h2 : Continuous (fun x => fderiv ℝ (ω i) x (Pi.single i 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous.comp h1
    exact (continuous_const.mul h2).continuousOn

end CubeStokes

end
