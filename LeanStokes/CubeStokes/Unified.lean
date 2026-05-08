/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Bridge
import LeanStokes.CubeStokes.Smooth

/-!
# Unified Stokes: mathlib forms on boxes

Combines the bridge theorem (connecting `extDeriv` to `extDerivCoord`) with
the cubical Stokes theorem to state Stokes' theorem directly in terms of
mathlib's `extDeriv` for smooth differential forms on boxes.

## Main results

* `CubeStokes.stokes_extDeriv`: For a smooth (n-1)-form ω on ℝⁿ⁺¹, the integral
  of `extDeriv ω` (evaluated on the standard basis) over a box equals the boundary
  integral of ω.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function VectorField
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- **Stokes' theorem for mathlib differential forms on boxes.**

For a smooth `n`-form `ω` on `ℝⁿ⁺¹` (in the sense of mathlib's
`ContinuousAlternatingMap`), with smooth coordinate coefficients,
the integral of `extDeriv ω` over a box equals the boundary integral of `ω`:

  `∫_{[a,b]} (extDeriv ω)(e₀, …, eₙ) = ∫_{∂[a,b]} ω`

This combines:
1. The bridge theorem (`extDeriv_topCoeff_eq_extDerivCoord`)
2. The cubical Stokes theorem (`stokes_smooth`)
-/
theorem stokes_extDeriv
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (hω_diff : Differentiable ℝ ω)
    (hcoeff_smooth : IsSmooth (toCoordNForm ω)) :
    (∫ x in Icc a b, extDeriv ω x (fun j => Pi.single j 1)) =
    bdryIntegral (toCoordNForm ω) a b := by
  -- Step 1: Replace extDeriv with extDerivCoord via the bridge
  have h_eq : ∀ x ∈ Icc a b,
      extDeriv ω x (fun j => Pi.single j 1) = extDerivCoord (toCoordNForm ω) x := by
    intro x _
    exact extDeriv_topCoeff_eq_extDerivCoord ω x hω_diff.differentiableAt
  -- Step 2: Rewrite the integral using pointwise equality on the box
  rw [show (∫ x in Icc a b, extDeriv ω x (fun j => Pi.single j 1)) =
      boxIntegral (extDerivCoord (toCoordNForm ω)) a b from by
    unfold boxIntegral
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc h_eq]
  -- Step 3: Apply cubical Stokes
  exact stokes_smooth a b hle (toCoordNForm ω) hcoeff_smooth

/-- **Stokes' theorem for C^∞ mathlib forms.**

If ω is globally C^∞ (as a map into alternating maps), then Stokes holds
on any box with `a ≤ b`. This is the cleanest statement: no separate
coefficient smoothness hypothesis needed. -/
theorem stokes_extDeriv_smooth
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    (∫ x in Icc a b, extDeriv ω x (fun j => Pi.single j 1)) =
    bdryIntegral (toCoordNForm ω) a b :=
    stokes_extDeriv ω a b hle (hω.differentiable (by simp)) (toCoordNForm_smooth ω hω)

end CubeStokes

end
