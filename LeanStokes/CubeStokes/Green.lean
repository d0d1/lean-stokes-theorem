import LeanStokes.CubeStokes.Smooth
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Green's Theorem as a Corollary of Cubical Stokes

Green's theorem in the plane:
  `∮_{∂R} (P dx + Q dy) = ∬_R (∂Q/∂x - ∂P/∂y) dA`

derived from `stokes_smooth` at dimension n = 1.

## Main results

* `CubeStokes.green_stokes`: Green's theorem on a rectangle.
* `CubeStokes.green_four_edges`: Explicit four-edge decomposition.
* `CubeStokes.bdryIntegral_dim1_expand`: Face expansion for n=1.
* `CubeStokes.partialDeriv`: Partial derivative definition.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

/-- Partial derivative `∂f/∂xᵢ` at a point. -/
def partialDeriv (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- At dimension n = 1, `extDerivCoord ω x = ∂ω₀/∂x₀ - ∂ω₁/∂x₁`. -/
lemma extDerivCoord_dim1 (ω : CoordNForm 1) (x : Fin 2 → ℝ) :
    extDerivCoord ω x = partialDeriv (ω 0) 0 x - partialDeriv (ω 1) 1 x := by
  unfold extDerivCoord partialDeriv
  rw [Fin.sum_univ_two]
  simp [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  ring

/-- **Green's Theorem** on a rectangle `[a₀,b₀] × [a₁,b₁]`.

Given smooth `Q, P : ℝ² → ℝ` and a rectangle with `a ≤ b`:
  `∬_R (∂Q/∂x - ∂P/∂y) dA = ∮_{∂R} ω`

where `ω = ![Q, P]` is the coordinate 1-form with `ω₀ = Q`, `ω₁ = P`.
The sign convention gives `dω = ∂Q/∂x - ∂P/∂y` matching the classical Green formula. -/
theorem green_stokes (Q P : (Fin 2 → ℝ) → ℝ) (a b : Fin 2 → ℝ) (hab : a ≤ b)
    (hQ : ContDiff ℝ ⊤ Q) (hP : ContDiff ℝ ⊤ P) :
    (∫ x in Icc a b, partialDeriv Q 0 x - partialDeriv P 1 x) =
    bdryIntegral ![Q, P] a b := by
  set ω : CoordNForm 1 := ![Q, P] with hω_def
  have hsmooth : IsSmooth ω := by
    intro i; fin_cases i <;> simp [ω, Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption
  have hlhs : ∀ x, extDerivCoord ω x = partialDeriv Q 0 x - partialDeriv P 1 x := by
    intro x
    rw [extDerivCoord_dim1]
    simp [ω, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  calc ∫ x in Icc a b, partialDeriv Q 0 x - partialDeriv P 1 x
      = boxIntegral (extDerivCoord ω) a b := by
          unfold boxIntegral; congr 1; ext x; exact (hlhs x).symm
    _ = bdryIntegral ω a b := stokes_smooth a b hab ω hsmooth
    _ = bdryIntegral ![Q, P] a b := rfl

/-- Expand bdryIntegral for n=1 into two face integrals. -/
theorem bdryIntegral_dim1_expand (ω : CoordNForm 1) (a b : Fin 2 → ℝ) :
    bdryIntegral ω a b =
    (∫ x : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (0 : Fin 2)) (b ∘ Fin.succAbove (0 : Fin 2)),
      signedCoeff ω 0 (Fin.insertNth (0 : Fin 2) (b 0) x)) -
    (∫ x : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (0 : Fin 2)) (b ∘ Fin.succAbove (0 : Fin 2)),
      signedCoeff ω 0 (Fin.insertNth (0 : Fin 2) (a 0) x)) +
    ((∫ x : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (1 : Fin 2)) (b ∘ Fin.succAbove (1 : Fin 2)),
      signedCoeff ω 1 (Fin.insertNth (1 : Fin 2) (b 1) x)) -
    (∫ x : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (1 : Fin 2)) (b ∘ Fin.succAbove (1 : Fin 2)),
      signedCoeff ω 1 (Fin.insertNth (1 : Fin 2) (a 1) x))) := by
  unfold bdryIntegral; rw [Fin.sum_univ_two]

/-- **Green's theorem with four oriented edge integrals.**

The double integral equals the sum of four oriented edge contributions:
- Right edge: `+∫ Q(b₀, y) dy` over `y ∈ [a₁, b₁]`
- Left edge: `-∫ Q(a₀, y) dy` over `y ∈ [a₁, b₁]`
- Top edge: `-∫ P(x, b₁) dx` over `x ∈ [a₀, b₀]`
- Bottom edge: `+∫ P(x, a₁) dx` over `x ∈ [a₀, b₀]` -/
theorem green_four_edges (Q P : (Fin 2 → ℝ) → ℝ) (a b : Fin 2 → ℝ) (hab : a ≤ b)
    (hQ : ContDiff ℝ ⊤ Q) (hP : ContDiff ℝ ⊤ P) :
    (∫ x in Icc a b, partialDeriv Q 0 x - partialDeriv P 1 x) =
    (∫ y : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (0 : Fin 2)) (b ∘ Fin.succAbove (0 : Fin 2)),
      Q (Fin.insertNth (0 : Fin 2) (b 0) y)) -
    (∫ y : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (0 : Fin 2)) (b ∘ Fin.succAbove (0 : Fin 2)),
      Q (Fin.insertNth (0 : Fin 2) (a 0) y)) -
    (∫ x : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (1 : Fin 2)) (b ∘ Fin.succAbove (1 : Fin 2)),
      P (Fin.insertNth (1 : Fin 2) (b 1) x)) +
    (∫ x : Fin 1 → ℝ in Icc (a ∘ Fin.succAbove (1 : Fin 2)) (b ∘ Fin.succAbove (1 : Fin 2)),
      P (Fin.insertNth (1 : Fin 2) (a 1) x)) := by
  rw [green_stokes Q P a b hab hQ hP, bdryIntegral_dim1_expand]
  simp only [signedCoeff, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul]
  have hQ0 : ∀ x, (![Q, P] : CoordNForm 1) 0 x = Q x := by
    intro x; simp [Matrix.cons_val_zero]
  have hP1 : ∀ x, (![Q, P] : CoordNForm 1) 1 x = P x := by
    intro x; simp [Matrix.cons_val_one, Matrix.head_cons]
  simp_rw [hQ0, hP1]
  set S1 := Icc (a ∘ Fin.succAbove (1 : Fin 2)) (b ∘ Fin.succAbove (1 : Fin 2))
  have hP_b : (∫ x : Fin 1 → ℝ in S1, -(P (Fin.insertNth (1 : Fin 2) (b 1) x))) =
    -(∫ x : Fin 1 → ℝ in S1, P (Fin.insertNth (1 : Fin 2) (b 1) x)) := by
    rw [integral_neg]
  have hP_a : (∫ x : Fin 1 → ℝ in S1, -(P (Fin.insertNth (1 : Fin 2) (a 1) x))) =
    -(∫ x : Fin 1 → ℝ in S1, P (Fin.insertNth (1 : Fin 2) (a 1) x)) := by
    rw [integral_neg]
  rw [hP_b, hP_a]
  ring

end CubeStokes
end
