/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Smooth

/-!
# Classical Corollaries of Cubical Stokes

Specializations of the cubical Stokes theorem to low dimensions.
These instantiate `stokes_smooth` at specific `n` values.

## Coefficient Conventions

For a coordinate `n`-form `ω` on `ℝⁿ⁺¹`:
- `ω i` is the coefficient of `dx₀ ∧ ⋯ ∧ d̂xᵢ ∧ ⋯ ∧ dxₙ` (hat = omit)
- `extDerivCoord ω x = ∑ᵢ (-1)ⁱ · (∂ωᵢ/∂xᵢ)(x)`

### Dimension 1 (FTC, n = 0)
- `CoordNForm 0`: one coefficient `ω 0 : ℝ¹ → ℝ`
- `extDerivCoord ω x = (∂(ω 0)/∂x₀)(x)` = derivative of `ω 0`
- `bdryIntegral ω a b = (ω 0)(b) - (ω 0)(a)`
- This is the fundamental theorem of calculus.

### Dimension 2 (Green, n = 1)
- `CoordNForm 1`: two coefficients `ω 0, ω 1 : ℝ² → ℝ`
- Convention: `ω 0` = coefficient of `dx₁` (i.e., `dy`), `ω 1` = coefficient of `dx₀` (i.e., `dx`)
- `extDerivCoord ω x = ∂(ω 0)/∂x₀ - ∂(ω 1)/∂x₁ = ∂Q/∂x - ∂P/∂y`
  where `Q := ω 0`, `P := ω 1`
- This is Green's theorem: `∫∫ (∂Q/∂x - ∂P/∂y) dA = ∮_∂R ω`

### Dimension 3 (Divergence, n = 2)
- `CoordNForm 2`: three coefficients `ω 0, ω 1, ω 2 : ℝ³ → ℝ`
- Convention:
  - `ω 0` = coefficient of `dx₁ ∧ dx₂` (i.e., `dy ∧ dz`)
  - `ω 1` = coefficient of `dx₀ ∧ dx₂` (i.e., `dx ∧ dz`)
  - `ω 2` = coefficient of `dx₀ ∧ dx₁` (i.e., `dx ∧ dy`)
- `extDerivCoord ω x = ∂(ω 0)/∂x₀ - ∂(ω 1)/∂x₁ + ∂(ω 2)/∂x₂`
- For a vector field `F = (F₁, F₂, F₃)`, set `ω 0 = F₁`, `ω 1 = -F₂`, `ω 2 = F₃`
  to get `extDerivCoord ω = div F`.

## Main results

* `CubeStokes.ftc_on_interval`: FTC as Stokes for `n = 0`.
* `CubeStokes.green_on_rectangle`: Green's theorem for `n = 1`.
* `CubeStokes.divergence_on_box_3d`: Divergence theorem for `n = 2`.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace CubeStokes

/-- **Fundamental theorem of calculus** as Stokes for 0-forms on `ℝ¹`.
Setting `ω 0 = f`, this gives `∫ f' dx = f(b) - f(a)`. -/
theorem ftc_on_interval (a b : Fin 1 → ℝ) (hle : a ≤ b)
    (ω : CoordNForm 0) (hω : IsSmooth ω) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b :=
  stokes_smooth a b hle ω hω

/-- **Green's theorem** on a rectangle in `ℝ²`.
Setting `Q := ω 0`, `P := ω 1`, this gives
`∫∫_R (∂Q/∂x - ∂P/∂y) dA = ∮_∂R (Q dy + P dx)`. -/
theorem green_on_rectangle (a b : Fin 2 → ℝ) (hle : a ≤ b)
    (ω : CoordNForm 1) (hω : IsSmooth ω) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b :=
  stokes_smooth a b hle ω hω

/-- **Divergence theorem** on a 3D box.
Setting `ω 0 = F₁`, `ω 1 = -F₂`, `ω 2 = F₃`, this gives
`∫∫∫_B div(F) dV = ∯_∂B F · dS`. -/
theorem divergence_on_box_3d (a b : Fin 3 → ℝ) (hle : a ≤ b)
    (ω : CoordNForm 2) (hω : IsSmooth ω) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b :=
  stokes_smooth a b hle ω hω

end CubeStokes

end
