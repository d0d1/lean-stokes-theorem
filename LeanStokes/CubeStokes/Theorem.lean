/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Defs

/-!
# Stokes' Theorem on Boxes (Cubical Stokes)

We prove Stokes' theorem for coordinate `n`-forms on axis-aligned boxes in `ℝⁿ⁺¹`:

  `∫_{[a,b]} dω = ∫_{∂[a,b]} ω`

The proof reduces to the divergence theorem on boxes
(`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`).

## Main results

* `CubeStokes.stokes_on_box`: Stokes' theorem on a box in `ℝⁿ⁺¹`.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- **Stokes' theorem on a box** in `ℝⁿ⁺¹`.

For a coordinate `n`-form `ω` on `ℝⁿ⁺¹` whose coefficients are continuous on the
closed box `[a, b]` and differentiable on its interior (off a countable set), with
integrable exterior derivative:

  `∫_{[a,b]} dω = ∫_{∂[a,b]} ω`
-/
theorem stokes_on_box (a b : Fin (n + 1) → ℝ) (hle : a ≤ b)
    (ω : CoordNForm n)
    (s : Set (Fin (n + 1) → ℝ)) (hs : s.Countable)
    (hc : ∀ i, ContinuousOn (signedCoeff ω i) (Icc a b))
    (hd : ∀ x ∈ (pi univ fun i => Ioo (a i) (b i)) \ s,
      ∀ i, HasFDerivAt (signedCoeff ω i)
        ((-1 : ℝ) ^ (i : ℕ) • fderiv ℝ (ω i) x) x)
    (hi : IntegrableOn (fun x => ∑ i : Fin (n + 1),
      ((-1 : ℝ) ^ (i : ℕ) • fderiv ℝ (ω i) x) (Pi.single i 1)) (Icc a b)) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b := by
  unfold boxIntegral bdryIntegral extDerivCoord
  exact MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable' a b hle
    (signedCoeff ω) (fun i x => (-1 : ℝ) ^ (i : ℕ) • fderiv ℝ (ω i) x)
    s hs hc hd hi

end CubeStokes

end
