import LeanStokes.CubeStokes.Smooth
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Cubical Chains and Stokes for Chains

We define cubical chains as formal ℤ-linear combinations of boxes and prove that
Stokes' theorem extends by linearity from single boxes to arbitrary chains.

## Main definitions

* `CubeStokes.CubicalBox n`: A non-degenerate box `[a, b]` in `Fin (n+1) → ℝ`.
* `CubeStokes.CubicalChain n`: Formal ℤ-linear combinations of boxes.
* `CubeStokes.integrateExterior`: Integration of dω over a chain.
* `CubeStokes.integrateBdry`: Integration of ω over boundaries of a chain.

## Main results

* `CubeStokes.stokes_chain`: Stokes extends by linearity to chains.
-/

open Set Finset MeasureTheory Filter Function
open scoped Topology

noncomputable section

namespace CubeStokes

/-- A non-degenerate cubical box in `ℝⁿ⁺¹`: a pair of corners `a ≤ b`. -/
structure CubicalBox (n : ℕ) where
  lo : Fin (n + 1) → ℝ
  hi : Fin (n + 1) → ℝ
  le : lo ≤ hi

/-- A cubical chain is a formal ℤ-linear combination of boxes. -/
abbrev CubicalChain (n : ℕ) := CubicalBox n →₀ ℤ

/-- A singleton chain consisting of one box with coefficient 1. -/
def singletonChain (B : CubicalBox n) : CubicalChain n :=
  Finsupp.single B 1

/-- Integration of the exterior derivative `dω` over a chain. -/
def integrateExterior (c : CubicalChain n) (ω : CoordNForm n) : ℝ :=
  c.sum fun B k => (k : ℝ) * boxIntegral (extDerivCoord ω) B.lo B.hi

/-- Boundary integral of `ω` over each box in a chain (weighted by coefficients). -/
def integrateBdry (c : CubicalChain n) (ω : CoordNForm n) : ℝ :=
  c.sum fun B k => (k : ℝ) * bdryIntegral ω B.lo B.hi

/-- **Stokes' theorem for cubical chains.**

For a smooth form `ω`, integration of `dω` over a chain equals the boundary
integral of `ω` over the same chain. This is the linear extension of
`stokes_smooth` from single boxes to formal combinations. -/
theorem stokes_chain (c : CubicalChain n) (ω : CoordNForm n) (hω : IsSmooth ω) :
    integrateExterior c ω = integrateBdry c ω := by
  unfold integrateExterior integrateBdry
  apply Finsupp.sum_congr
  intro B _
  congr 1
  exact stokes_smooth B.lo B.hi B.le ω hω

/-- Stokes for a singleton chain: reduces to `stokes_smooth`. -/
theorem stokes_single (B : CubicalBox n) (ω : CoordNForm n) (hω : IsSmooth ω) :
    integrateExterior (singletonChain B) ω = integrateBdry (singletonChain B) ω :=
  stokes_chain (singletonChain B) ω hω

/-- Additivity: integration over a sum of chains. -/
theorem integrateExterior_add (c₁ c₂ : CubicalChain n) (ω : CoordNForm n) :
    integrateExterior (c₁ + c₂) ω =
    integrateExterior c₁ ω + integrateExterior c₂ ω := by
  unfold integrateExterior
  rw [Finsupp.sum_add_index']
  · intro B; simp
  · intro B k₁ k₂; push_cast; ring

/-- Additivity: boundary integration over a sum of chains. -/
theorem integrateBdry_add (c₁ c₂ : CubicalChain n) (ω : CoordNForm n) :
    integrateBdry (c₁ + c₂) ω =
    integrateBdry c₁ ω + integrateBdry c₂ ω := by
  unfold integrateBdry
  rw [Finsupp.sum_add_index']
  · intro B; simp
  · intro B k₁ k₂; push_cast; ring

end CubeStokes
end
