import LeanStokes.CubeStokes.Smooth
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Fundamental Theorem of Calculus via Stokes

We derive the classical FTC `∫_a^b f' = f(b) - f(a)` as a corollary of
`stokes_smooth` at dimension n = 0.

## Main results

* `CubeStokes.ftc_stokes`: FTC derived from Stokes' theorem.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

/-- The Icc box in `Fin 0 → ℝ` is trivially all of the space. -/
lemma icc_fin0_univ (a b : Fin 0 → ℝ) : Set.Icc a b = Set.univ := by
  ext x; constructor
  · intro _; trivial
  · intro _; exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- The volume of the full space `Fin 0 → ℝ` is 1. -/
lemma volume_univ_fin0 : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 :=
  Measure.pi_empty_univ _

/-- Integration of a constant over the trivial `Fin 0 → ℝ` box yields that constant. -/
lemma integral_const_fin0 (a b : Fin 0 → ℝ) (c : ℝ) :
    ∫ x in Set.Icc a b, c = c := by
  rw [icc_fin0_univ, Measure.restrict_univ, integral_unique]
  have h : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
    simp [Measure.real, volume_univ_fin0]
  rw [h]; simp

/-- The boundary integral of a constant 0-form `f(x₀)` on a 1D box equals `f(b) - f(a)`. -/
lemma bdryIntegral_fin1 (f : ℝ → ℝ) (a b : ℝ) :
    bdryIntegral (fun (_ : Fin 1) (x : Fin 1 → ℝ) => f (x 0))
      (fun _ => a) (fun _ => b) = f b - f a := by
  unfold bdryIntegral signedCoeff
  simp only [comp_def]
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_mul]
  simp_rw [Fin.insertNth_apply_same]
  rw [integral_const_fin0 _ _ (f b), integral_const_fin0 _ _ (f a)]

/-- The exterior derivative of the constant form `ω i x = f(x₀)` equals `f'(x₀)`. -/
lemma extDerivCoord_of_comp_proj (f : ℝ → ℝ) (x : Fin 1 → ℝ)
    (hf : Differentiable ℝ f) :
    extDerivCoord (fun (_ : Fin 1) (y : Fin 1 → ℝ) => f (y 0)) x = deriv f (x 0) := by
  unfold extDerivCoord
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_mul]
  have heq : (fun y : Fin 1 → ℝ => f (y 0)) =
      f ∘ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) := rfl
  rw [heq, fderiv_comp x hf.differentiableAt
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).differentiableAt]
  simp [ContinuousLinearMap.comp_apply]

/-- **Fundamental Theorem of Calculus** derived from cubical Stokes.

For a smooth function `f : ℝ → ℝ` and `a ≤ b`:
  `∫ x in [a, b], f'(x) = f(b) - f(a)`

stated in the `Fin 1 → ℝ` coordinate framework. -/
theorem ftc_stokes (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContDiff ℝ ⊤ f) :
    (∫ x in Icc (fun _ : Fin 1 => a) (fun _ : Fin 1 => b),
      deriv f (x 0)) = f b - f a := by
  set ω : CoordNForm 0 := fun _ x => f (x 0) with hω_def
  have hlhs : ∀ x : Fin 1 → ℝ, extDerivCoord ω x = deriv f (x 0) :=
    fun x => extDerivCoord_of_comp_proj f x (hf.differentiable (by norm_num))
  have hrhs : bdryIntegral ω (fun _ => a) (fun _ => b) = f b - f a :=
    bdryIntegral_fin1 f a b
  have hsmooth : IsSmooth ω := fun _ =>
    hf.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff
  have hle : (fun _ : Fin 1 => a) ≤ (fun _ : Fin 1 => b) := fun _ => hab
  calc ∫ x in Icc (fun _ : Fin 1 => a) (fun _ : Fin 1 => b), deriv f (x 0)
      = boxIntegral (extDerivCoord ω) (fun _ => a) (fun _ => b) := by
          unfold boxIntegral; congr 1; ext x; exact (hlhs x).symm
    _ = bdryIntegral ω (fun _ => a) (fun _ => b) :=
          stokes_smooth _ _ hle ω hsmooth
    _ = f b - f a := hrhs

end CubeStokes
end
