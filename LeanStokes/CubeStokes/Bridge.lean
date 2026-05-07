/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField

/-!
# Bridge: Coordinate forms ↔ mathlib differential forms

Establishes the formal connection between `CoordNForm` (coordinate representation)
and mathlib's differential forms via `extDeriv`.

## Main results

* `CubeStokes.toCoordNForm`: Extract coordinate coefficients from a mathlib form.
* `CubeStokes.extDeriv_topCoeff_eq_extDerivCoord`: The top-form coefficient of
  `extDeriv ω` equals `extDerivCoord (toCoordNForm ω)`.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function VectorField
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- Extract coordinate coefficients from a mathlib differential form.
The i-th coefficient is the form evaluated on the standard basis with e_i omitted. -/
def toCoordNForm (ω : (Fin (n + 1) → ℝ) →
    (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : CoordNForm n :=
  fun i x => ω x (fun k => Pi.single (Fin.succAbove i k) 1)

/-- The top-form coefficient of `extDeriv ω`, evaluated on the full standard basis,
equals the coordinate exterior derivative of the extracted coefficients. -/
theorem extDeriv_topCoeff_eq_extDerivCoord
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (x : Fin (n + 1) → ℝ)
    (hω : DifferentiableAt ℝ ω x) :
    extDeriv ω x (fun j => Pi.single j 1) = extDerivCoord (toCoordNForm ω) x := by
  set V : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun j _ => Pi.single j 1
  have hV : ∀ j, DifferentiableAt ℝ (V j) x := fun j => differentiableAt_const _
  have hcomm : Pairwise fun i j : Fin (n + 1) =>
      lieBracket ℝ (V i) (V j) x = 0 := by
    intro i j _
    simp [lieBracket, V]
  have hkey := extDeriv_apply_vectorField_of_pairwise_commute hω hV hcomm
  change extDeriv ω x (fun j => V j x) = _ at hkey
  simp only [V] at hkey
  rw [hkey]
  -- Goal: ∑ i, (-1:ℤ)^↑i • fderiv(... removeNth ...) = ∑ i, (-1:ℝ)^↑i * fderiv(... succAbove ...)
  unfold extDerivCoord toCoordNForm
  congr 1; ext i
  -- Unfold removeNth to make the fderiv functions syntactically equal
  dsimp only [Fin.removeNth]
  -- Now both sides have the same fderiv; just cast ℤ•r to ℝ*r
  rw [zsmul_eq_mul]
  norm_cast

/-- If a mathlib form is smooth (C^∞ as a map into alternating maps), then its
extracted coordinate coefficients are also smooth. -/
theorem toCoordNForm_smooth
    (ω : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ ⊤ ω) :
    IsSmooth (toCoordNForm ω) := by
  intro i
  show ContDiff ℝ ⊤ (fun x => (ω x) (fun k => Pi.single (Fin.succAbove i k) 1))
  change ContDiff ℝ ⊤ ((ContinuousAlternatingMap.apply ℝ (Fin (n + 1) → ℝ) ℝ
    (fun k => Pi.single (Fin.succAbove i k) 1)) ∘ ω)
  exact (ContinuousAlternatingMap.apply ℝ (Fin (n + 1) → ℝ) ℝ
    (fun k => Pi.single (Fin.succAbove i k) 1)).contDiff.comp hω

end CubeStokes

end
