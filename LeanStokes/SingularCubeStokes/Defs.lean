/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Smooth Singular Cubes

Defines smooth singular cubes and their face maps for singular cubical Stokes.

## Main definitions

* `SingularCubeStokes.SmoothSingularCube n m`: A C^∞ map σ : ℝⁿ → ℝᵐ
* `SingularCubeStokes.faceInclusion i ε`: Insert ε at position i (ℝⁿ → ℝⁿ⁺¹)
* `SingularCubeStokes.singularFace σ i ε`: Face restriction σ ∘ faceInclusion

## Design

We use globally smooth maps (ContDiff ℝ ⊤) and integrate over [0,1]^n.
The pullback here is the TRUE differential-form pullback via fderiv.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace SingularCubeStokes

variable {n m : ℕ}

/-- A smooth singular n-cube in ℝᵐ: a C^∞ map from ℝⁿ to ℝᵐ. -/
@[ext]
structure SmoothSingularCube (n m : ℕ) where
  toFun : (Fin n → ℝ) → (Fin m → ℝ)
  smooth : ContDiff ℝ ⊤ toFun

instance : CoeFun (SmoothSingularCube n m) (fun _ => (Fin n → ℝ) → (Fin m → ℝ)) :=
  ⟨SmoothSingularCube.toFun⟩

/-- The standard unit cube [0,1]^n. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Icc (fun _ => (0 : ℝ)) (fun _ => 1)

/-- Face inclusion: inserts ε at position i.
For j < i: output is t_j. For j = i: output is ε. For j > i: output is t_{j-1}. -/
def faceInclusion {n : ℕ} (i : Fin (n + 1)) (ε : ℝ) (t : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun j =>
    if h1 : (j : ℕ) < (i : ℕ) then t ⟨j, by omega⟩
    else if h2 : (j : ℕ) = (i : ℕ) then ε
    else t ⟨(j : ℕ) - 1, by omega⟩

/-- Each component of faceInclusion is smooth (constant or projection). -/
theorem faceInclusion_contDiff {n : ℕ} (i : Fin (n + 1)) (ε : ℝ) :
    ContDiff ℝ ⊤ (faceInclusion i ε) := by
  apply contDiff_pi.mpr
  intro j
  show ContDiff ℝ ⊤ fun t => faceInclusion i ε t j
  simp only [faceInclusion]
  split_ifs with h1 h2
  · -- j < i: this is fun t => t ⟨j, _⟩
    have hlt : (j : ℕ) < n := by have := i.isLt; omega
    exact contDiff_apply (𝕜 := ℝ) (E := ℝ) (⟨j, hlt⟩ : Fin n)
  · -- j = i: constant
    exact contDiff_const
  · -- j > i: this is fun t => t ⟨j - 1, _⟩
    have hlt : (j : ℕ) - 1 < n := by have := j.isLt; have := i.isLt; omega
    exact contDiff_apply (𝕜 := ℝ) (E := ℝ) (⟨(j : ℕ) - 1, hlt⟩ : Fin n)

/-- The face inclusion is differentiable. -/
theorem faceInclusion_differentiable {n : ℕ} (i : Fin (n + 1)) (ε : ℝ) :
    Differentiable ℝ (faceInclusion i ε) :=
  (faceInclusion_contDiff i ε).differentiable (by norm_num)

/-- The i-th face of a smooth singular cube at value ε: σ ∘ ι_{i,ε}. -/
def singularFace (σ : SmoothSingularCube (n + 1) m) (i : Fin (n + 1)) (ε : ℝ) :
    SmoothSingularCube n m where
  toFun := σ.toFun ∘ faceInclusion i ε
  smooth := σ.smooth.comp (faceInclusion_contDiff i ε)

/-- Boundary sign: (-1)^(i + orientation).
hi = true means the "high" face (ε=1), hi = false means "low" face (ε=0). -/
def boundarySign (i : Fin (n + 1)) (hi : Bool) : ℤ :=
  if hi then (-1 : ℤ) ^ (i : ℕ) else (-1 : ℤ) ^ ((i : ℕ) + 1)

/-- The identity singular cube. -/
def idCube (n : ℕ) : SmoothSingularCube n n where
  toFun := id
  smooth := contDiff_id

end SingularCubeStokes

end
