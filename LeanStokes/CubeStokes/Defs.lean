/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Definitions for Cubical Stokes' Theorem

We define the coordinate representation of differential forms on boxes in `ℝⁿ⁺¹`,
their exterior derivatives, and boundary integrals.

## Main definitions

* `CubeStokes.CoordNForm n`: an `n`-form on `ℝⁿ⁺¹` in coordinate representation,
  given as a family of coefficient functions `Fin (n+1) → (Fin (n+1) → ℝ) → ℝ`.
* `CubeStokes.extDerivCoord`: the exterior derivative coefficient function.
* `CubeStokes.boxIntegral`: integral of a function over a box `[a, b]`.
* `CubeStokes.bdryIntegral`: oriented boundary integral of a coordinate n-form.

## Mathematical context

An `n`-form on `ℝⁿ⁺¹` can be written as:
  `ω = ∑ᵢ ωᵢ · dx₀ ∧ ⋯ ∧ d̂xᵢ ∧ ⋯ ∧ dxₙ`

Its exterior derivative is the top form:
  `dω = (∑ᵢ (-1)ⁱ ∂ωᵢ/∂xᵢ) · dx₀ ∧ ⋯ ∧ dxₙ`

Stokes' theorem on the box `[a,b]` states:
  `∫_{[a,b]} dω = ∫_{∂[a,b]} ω`
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- A coordinate `n`-form on `ℝⁿ⁺¹` is a family of `n+1` coefficient functions.
The `i`-th coefficient `ω i` represents the component in the direction
`dx₀ ∧ ⋯ ∧ d̂xᵢ ∧ ⋯ ∧ dxₙ`. -/
def CoordNForm (n : ℕ) := Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ

instance : CoeFun (CoordNForm n) (fun _ => Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) :=
  ⟨id⟩

/-- The sign-flipped coefficient: `(-1)ⁱ · ωᵢ`. This is the function whose divergence
gives the exterior derivative, and whose face values give the boundary integral. -/
def signedCoeff (ω : CoordNForm n) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : ℝ :=
  (-1 : ℝ) ^ (i : ℕ) * ω i x

/-- The exterior derivative of a coordinate `n`-form, evaluated at a point.
This gives the coefficient of the top form `dx₀ ∧ ⋯ ∧ dxₙ`:
  `(dω)(x) = ∑ᵢ (-1)ⁱ · ∂ωᵢ/∂xᵢ(x)`

Equivalently, this is the divergence of the signed coefficients:
  `(dω)(x) = ∑ᵢ ∂(signedCoeff ω i)/∂xᵢ(x)` -/
def extDerivCoord (ω : CoordNForm n) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (ω i) x (Pi.single i 1)

/-- Integral of a scalar function over a box `[a, b]`. -/
def boxIntegral (f : (Fin (n + 1) → ℝ) → ℝ) (a b : Fin (n + 1) → ℝ) : ℝ :=
  ∫ x in Icc a b, f x

/-- The oriented boundary integral of a coordinate `n`-form over `∂[a, b]`.
This is defined as the sum of face integrals of the signed coefficients:
  `∫_{∂[a,b]} ω = ∑ᵢ (∫_{face i} (signedCoeff ω i)(frontFace i ·)
                      - ∫_{face i} (signedCoeff ω i)(backFace i ·))`

which equals (by linearity of integration):
  `∑ᵢ (-1)ⁱ · (∫_{face i} ωᵢ(frontFace i ·) - ∫_{face i} ωᵢ(backFace i ·))` -/
def bdryIntegral (ω : CoordNForm n) (a b : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
        signedCoeff ω i (Fin.insertNth i (b i) x)) -
     (∫ x in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
        signedCoeff ω i (Fin.insertNth i (a i) x)))

/-- A coordinate `n`-form is smooth if each coefficient function is smooth. -/
def IsSmooth (ω : CoordNForm n) : Prop :=
  ∀ i : Fin (n + 1), ContDiff ℝ (⊤ : ℕ∞) (ω i)

/-- A coordinate `n`-form is continuous on a set if each coefficient is. -/
def IsContinuousOn (ω : CoordNForm n) (s : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∀ i : Fin (n + 1), ContinuousOn (ω i) s

/-- A coordinate `n`-form is differentiable at a point if each coefficient is. -/
def IsDifferentiableAt (ω : CoordNForm n) (x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i : Fin (n + 1), DifferentiableAt ℝ (ω i) x

end CubeStokes

end
