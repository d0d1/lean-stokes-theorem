import LeanStokes.CubeStokes.FTC
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Integration by Parts via Stokes

Derives integration by parts from the FTC corollary of cubical Stokes.

## Main results

* `CubeStokes.integration_by_parts`: IBP on a 1D box via FTC/Stokes.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

private lemma continuous_deriv_of_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (deriv f) := by
  have hcf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have heq : (fun x => (fderiv ℝ f x) (1 : ℝ)) = deriv f := by
    ext x; simp [fderiv_deriv]
  rw [← heq]
  exact ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous).comp hcf

/-- **Integration by Parts** derived from the FTC corollary of Stokes.

For smooth `f, g : ℝ → ℝ` and `a ≤ b`:
  `∫_{[a,b]} f·g' = f(b)g(b) - f(a)g(a) - ∫_{[a,b]} f'·g` -/
theorem integration_by_parts (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    (∫ x in Icc (fun _ : Fin 1 => a) (fun _ : Fin 1 => b),
      f (x 0) * deriv g (x 0)) =
    f b * g b - f a * g a -
    (∫ x in Icc (fun _ : Fin 1 => a) (fun _ : Fin 1 => b),
      deriv f (x 0) * g (x 0)) := by
  -- FTC applied to f*g
  have hfg : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * g x) := hf.mul hg
  have ftc_fg := ftc_stokes (fun x => f x * g x) a b hab hfg
  -- Product rule: (f*g)' = f'*g + f*g'
  have hprod : ∀ x, deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x := by
    intro x
    have hd1 := (hf.differentiable (by norm_num)).differentiableAt (x := x)
    have hd2 := (hg.differentiable (by norm_num)).differentiableAt (x := x)
    have h := deriv_mul hd1 hd2
    simp [Pi.mul_apply] at h
    exact h
  -- Rewrite FTC integral using product rule
  have ftc_eq : (∫ x in Icc (fun _ : Fin 1 => a) (fun _ : Fin 1 => b),
    (deriv f (x 0) * g (x 0) + f (x 0) * deriv g (x 0))) =
    f b * g b - f a * g a := by
      convert ftc_fg using 1
      congr 1; ext x; exact (hprod (x 0)).symm
  -- Integrability
  have hint1 : IntegrableOn (fun x : Fin 1 → ℝ => deriv f (x 0) * g (x 0))
    (Icc (fun _ => a) (fun _ => b)) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact (((continuous_deriv_of_contDiff f hf).comp (continuous_apply 0)).mul
        (hg.continuous.comp (continuous_apply 0))).continuousOn
  have hint2 : IntegrableOn (fun x : Fin 1 → ℝ => f (x 0) * deriv g (x 0))
    (Icc (fun _ => a) (fun _ => b)) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact ((hf.continuous.comp (continuous_apply 0)).mul
        ((continuous_deriv_of_contDiff g hg).comp (continuous_apply 0))).continuousOn
  have hsplit := integral_add hint1 hint2
  linarith [hsplit, ftc_eq]

end CubeStokes
end
