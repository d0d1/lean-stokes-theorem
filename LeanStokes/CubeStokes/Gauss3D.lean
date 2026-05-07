/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Divergence

/-!
# 3D Gauss Divergence Theorem on Boxes

Provides a recognizable statement of the 3D divergence theorem on boxes:
For a smooth vector field F = (F₀, F₁, F₂) on ℝ³ and box [a, b]:

  ∫∫∫_[a,b] div F dV = (flux through 6 faces)

This is a direct corollary of the general `divergence_stokes` theorem
specialized to dimension 3.

## Main results

* `CubeStokes.gauss_3d`: The 3D divergence theorem on boxes.
* `CubeStokes.div3_eq`: div(F) = ∂F₀/∂x + ∂F₁/∂y + ∂F₂/∂z.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

/-- The divergence in 3D written with explicit partial derivatives. -/
theorem div3_eq (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) :
    divergence F x =
    (fderiv ℝ (fun y => F y 0) x) (Pi.single 0 1) +
    (fderiv ℝ (fun y => F y 1) x) (Pi.single 1 1) +
    (fderiv ℝ (fun y => F y 2) x) (Pi.single 2 1) := by
  simp only [divergence]
  rw [show Finset.univ (α := Fin 3) = {0, 1, 2} from by decide]
  simp only [Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)))]
  simp only [Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
  simp only [Finset.sum_singleton]
  ring

/-- **3D Gauss Divergence Theorem on Boxes.**

For smooth F : ℝ³ → ℝ³ and box [a, b]:
  ∫_[a,b] (∂F₀/∂x + ∂F₁/∂y + ∂F₂/∂z) dV = ∫_∂[a,b] F·n dS

The right-hand side is the boundary integral with the sign-compensated form
(each component pre-multiplied by (-1)^i to cancel the exterior derivative sign). -/
theorem gauss_3d (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (a b : Fin 3 → ℝ) (hab : a ≤ b)
    (hF : ∀ i, ContDiff ℝ ⊤ (fun x => F x i)) :
    (∫ x in Icc a b, divergence F x) =
    bdryIntegral (fun i y => (-1 : ℝ) ^ (i : ℕ) * F y i) a b :=
  divergence_stokes F a b hab hF

end CubeStokes
end
