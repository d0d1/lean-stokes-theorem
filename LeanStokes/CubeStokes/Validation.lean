import LeanStokes.CubeStokes.FTC
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Independent Validation: FTC via Two Paths

This module provides non-circular validation of the cubical Stokes theorem by:
1. Proving FTC directly from mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt`
2. Showing that the Stokes-derived FTC and the direct interval-integral FTC
   produce identical results

The divergence-theorem path (via `stokes_smooth`) produces:
  `∫_{[a,b]} (deriv f) = f(b) - f(a)`

The interval-integral path (via `integral_eq_sub_of_hasDerivAt`) produces:
  `∫_a^b (deriv f) = f(b) - f(a)`

The agreement theorem shows these are literally the same value.

## Main results

* `CubeStokes.ftc_intervalIntegral`: FTC from mathlib's interval integral.
* `CubeStokes.stokes_lhs_eq_intervalIntegral`: Stokes LHS equals `f b - f a`.
* `CubeStokes.ftc_paths_agree`: Agreement between both derivations.
-/

open Set Finset MeasureTheory Filter Function intervalIntegral
open scoped Topology

noncomputable section

namespace CubeStokes

/-- **FTC via mathlib interval integral**: For smooth `f` and `a ≤ b`,
`∫ x in a..b, deriv f x = f b - f a`. Direct from
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem ftc_intervalIntegral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∫ x in a..b, deriv f x = f b - f a := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    exact (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  · exact ((hf.of_le (by
      exact WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)
    )).continuous_deriv le_rfl).continuousOn.intervalIntegrable

/-- The Stokes-derived integral (set integral over `Fin 1 → ℝ` of `fderiv`)
equals `f b - f a`. Uses `fderiv_deriv` to align with `ftc_stokes`. -/
theorem stokes_lhs_eq_intervalIntegral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (∫ x : Fin 1 → ℝ in Icc (fun _ => a) (fun _ => b),
      fderiv ℝ f (x 0) 1) = f b - f a := by
  have heq : (fun x : Fin 1 → ℝ => (fderiv ℝ f (x 0)) (1 : ℝ)) =
             (fun x : Fin 1 → ℝ => deriv f (x 0)) := by
    ext x; exact fderiv_deriv
  rw [heq]
  exact ftc_stokes f a b hab hf

/-- **Non-circular validation**: Both paths agree.
- Path 1 (Stokes): `stokes_smooth` → `ftc_stokes` → `f b - f a`
- Path 2 (direct): `integral_eq_sub_of_hasDerivAt` → `f b - f a`

The theorem shows the Stokes-derived LHS equals the interval integral. -/
theorem ftc_paths_agree (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (∫ x : Fin 1 → ℝ in Icc (fun _ => a) (fun _ => b),
      fderiv ℝ f (x 0) 1) =
    ∫ x in a..b, deriv f x := by
  rw [stokes_lhs_eq_intervalIntegral f a b hab hf,
      ftc_intervalIntegral f a b hab hf]

end CubeStokes
end
