/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Smooth
import LeanStokes.CubeStokes.Chains
import LeanStokes.CubeStokes.Subdivision
import LeanStokes.CubeStokes.FTC
import LeanStokes.CubeStokes.Green
import LeanStokes.CubeStokes.Divergence
import LeanStokes.CubeStokes.Bridge

/-!
# Library Usage Demo

This module demonstrates how downstream users can import and use the
cubical Stokes library. It shows:

1. How to define coordinate forms
2. How to apply Stokes on a box
3. How to use the FTC, Green's, and divergence corollaries
4. How to work with chains
5. How to connect to mathlib's `extDeriv`

## Quick Start

To use this library in your own Lean 4 project:

```lean
-- In your lakefile.lean, add:
-- require LeanStokes from git "https://github.com/d0d1/lean-stokes-theorem"

-- Then import what you need:
import LeanStokes.CubeStokes.Smooth    -- For Stokes theorem
import LeanStokes.CubeStokes.Green     -- For Green's theorem
import LeanStokes.CubeStokes.Bridge    -- For mathlib connection
```
-/

noncomputable section

open CubeStokes

/-! ## Example 1: Define a smooth form and apply Stokes -/

/-- A constant 1-form on ℝ² (all coefficients = 1). -/
def myConstForm : CoordNForm 1 := fun _ _ => 1

/-- Smoothness of the constant form. -/
theorem myConstForm_smooth : IsSmooth myConstForm :=
  fun _ => contDiff_const

/-- Stokes on the unit square [0,1]² for a constant form. -/
example : boxIntegral (extDerivCoord myConstForm) (fun _ => 0) (fun _ => 1) =
    bdryIntegral myConstForm (fun _ => 0) (fun _ => 1) := by
  have h : (fun _ : Fin 2 => (0 : ℝ)) ≤ (fun _ => 1) := by
    intro i; norm_num
  exact stokes_smooth (fun _ => 0) (fun _ => 1) h myConstForm myConstForm_smooth

/-! ## Example 2: FTC as a special case of Stokes -/

/-- The Fundamental Theorem of Calculus via Stokes: for f : ℝ¹ → ℝ smooth,
    ∫_[a,b] dω = boundary values. -/
example (f : (Fin 1 → ℝ) → ℝ) (hf : ContDiff ℝ ⊤ f)
    (a b : Fin 1 → ℝ) (hab : a ≤ b) :
    let ω : CoordNForm 0 := fun _ => f
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b := by
  intro ω
  exact stokes_smooth a b hab ω (fun _ => hf)

/-! ## Example 3: Working with chains -/

/-- Two adjacent boxes form a chain; Stokes holds for the chain. -/
example (ω : CoordNForm 1) (hω : IsSmooth ω) :
    let B₁ : CubicalBox 1 := ⟨fun _ => 0, fun _ => 1, fun _ => by norm_num⟩
    let B₂ : CubicalBox 1 := ⟨fun _ => 1, fun _ => 2, fun _ => by norm_num⟩
    integrateExterior (twoBoxChain B₁ B₂) ω = integrateBdry (twoBoxChain B₁ B₂) ω := by
  intro B₁ B₂
  exact stokes_chain (twoBoxChain B₁ B₂) ω hω

/-! ## Example 4: Higher-dimensional Stokes (4D) -/

/-- Stokes on a 4-dimensional box [a,b] ⊂ ℝ⁴.
    Demonstrates the framework is genuinely n-dimensional. -/
example (ω : CoordNForm 3) (hω : IsSmooth ω)
    (a b : Fin 4 → ℝ) (hab : a ≤ b) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b :=
  stokes_smooth a b hab ω hω

/-! ## Example 5: 5D Stokes -/

/-- Stokes on a 5-dimensional box. Proof is identical regardless of dimension. -/
example (ω : CoordNForm 4) (hω : IsSmooth ω)
    (a b : Fin 5 → ℝ) (hab : a ≤ b) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b :=
  stokes_smooth a b hab ω hω

/-! ## Example 6: 10D Stokes -/

/-- Stokes in 10 dimensions — the same one-line proof works for any n. -/
example (ω : CoordNForm 9) (hω : IsSmooth ω)
    (a b : Fin 10 → ℝ) (hab : a ≤ b) :
    boxIntegral (extDerivCoord ω) a b = bdryIntegral ω a b :=
  stokes_smooth a b hab ω hω

/-! ## Example 7: Subdivision with shared-face cancellation -/

/-- Two adjacent rectangles [0,1]×[0,1] and [1,2]×[0,1] sharing the edge at x=1.
    The shared edge integral cancels in the combined boundary. -/
example (ω : CoordNForm 1) (hω : IsSmooth ω) :
    let B₁ : CubicalBox 1 := ⟨fun _ => 0, ![1, 1], fun i => by fin_cases i <;> norm_num⟩
    let B₂ : CubicalBox 1 := ⟨![1, 0], ![2, 1], fun i => by fin_cases i <;> norm_num⟩
    -- These boxes are adjacent in direction 0 (x-direction)
    Adjacent B₁ B₂ 0 := by
  intro B₁ B₂
  refine ⟨?_, ?_, ?_⟩
  · show (![1, 1] : Fin 2 → ℝ) 0 = (![1, 0] : Fin 2 → ℝ) 0
    norm_num [Matrix.cons_val_zero]
  · intro j; fin_cases j
    show (fun _ : Fin 2 => (0 : ℝ)) (Fin.succAbove 0 0) = (![1, 0] : Fin 2 → ℝ) (Fin.succAbove 0 0)
    simp [Fin.succAbove]
  · intro j; fin_cases j
    show (![1, 1] : Fin 2 → ℝ) (Fin.succAbove 0 0) = (![2, 1] : Fin 2 → ℝ) (Fin.succAbove 0 0)
    simp [Fin.succAbove]

/-- The combined Stokes identity holds on the subdivision. -/
example (ω : CoordNForm 1) (hω : IsSmooth ω) :
    let B₁ : CubicalBox 1 := ⟨fun _ => 0, ![1, 1], fun i => by fin_cases i <;> norm_num⟩
    let B₂ : CubicalBox 1 := ⟨![1, 0], ![2, 1], fun i => by fin_cases i <;> norm_num⟩
    boxIntegral (extDerivCoord ω) B₁.lo B₁.hi +
    boxIntegral (extDerivCoord ω) B₂.lo B₂.hi =
    bdryIntegral ω B₁.lo B₁.hi + bdryIntegral ω B₂.lo B₂.hi := by
  intro B₁ B₂
  exact subdivision_stokes_equiv B₁ B₂ ω hω

end
