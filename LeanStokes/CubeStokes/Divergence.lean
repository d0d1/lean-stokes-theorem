import LeanStokes.CubeStokes.Smooth
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Divergence Theorem as a Corollary of Cubical Stokes

The divergence theorem states `∫_R div(F) dV = flux of F through ∂R`.
We derive this from `stokes_smooth`.

## Main results

* `CubeStokes.divergence_stokes`: Divergence theorem on a box.
* `CubeStokes.extDerivCoord_eq_divergence`: Exterior derivative = divergence.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

/-- The divergence of a vector field `F : ℝⁿ⁺¹ → ℝⁿ⁺¹`:
  `div F(x) = ∑ᵢ ∂Fᵢ/∂xᵢ(x)` -/
def divergence {n : ℕ} (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), fderiv ℝ (fun y => F y i) x (Pi.single i 1)

/-- The exterior derivative of the signed-component form equals the divergence. -/
lemma extDerivCoord_eq_divergence (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℝ)
    (hF : ∀ i, DifferentiableAt ℝ (fun y => F y i) x) :
    extDerivCoord (fun i y => (-1 : ℝ) ^ (i : ℕ) * F y i) x = divergence F x := by
  unfold extDerivCoord divergence
  congr 1; ext i
  change (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ (fun y => (-1 : ℝ) ^ (i : ℕ) * F y i) x (Pi.single i 1))
    = fderiv ℝ (fun y => F y i) x (Pi.single i 1)
  rw [fderiv_const_mul (hF i)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, show (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 from by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num]
  ring

/-- **Divergence Theorem** on a box in ℝⁿ⁺¹.

For a smooth vector field `F` and a box `[a, b]` with `a ≤ b`:
  `∫_{[a,b]} div(F) dV = ∫_{∂[a,b]} F · n̂ dS`

expressed via the boundary integral of the signed component form. -/
theorem divergence_stokes (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (hF : ∀ i, ContDiff ℝ ⊤ (fun x => F x i)) :
    (∫ x in Icc a b, divergence F x) =
    bdryIntegral (fun i y => (-1 : ℝ) ^ (i : ℕ) * F y i) a b := by
  set ω : CoordNForm n := fun i y => (-1 : ℝ) ^ (i : ℕ) * F y i
  have hsmooth : IsSmooth ω := fun i =>
    ContDiff.mul contDiff_const (hF i)
  have hlhs : ∀ x, extDerivCoord ω x = divergence F x := fun x =>
    extDerivCoord_eq_divergence F x (fun i => (hF i).differentiable (by norm_num) |>.differentiableAt)
  calc ∫ x in Icc a b, divergence F x
      = boxIntegral (extDerivCoord ω) a b := by
          unfold boxIntegral; congr 1; ext x; exact (hlhs x).symm
    _ = bdryIntegral ω a b := stokes_smooth a b hab ω hsmooth

end CubeStokes
end
