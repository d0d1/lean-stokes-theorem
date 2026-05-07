/-
Copyright (c) 2025 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.Theorem

/-!
# Smooth Singular Cubical Chains

Provides the chain-level formulation of Stokes' theorem: the boundary
integral of ω equals the interior integral of dω, extended by ℤ-linearity
to formal chains.

## Main definitions

* `SingularCubeStokes.SingularChain`: Formal ℤ-linear combination of cubes.
* `SingularCubeStokes.bdryIntegral_singular`: Oriented boundary integral.
* `SingularCubeStokes.integrateChain`: Integration over chains.

## Main results

* `SingularCubeStokes.stokes_singular_boundary`: ∫_{∂σ} ω = ∫_σ dω
* `SingularCubeStokes.integrateChain_add`: Linearity of chain integration.
-/

noncomputable section

open Set Finset MeasureTheory Filter
open scoped Topology

namespace SingularCubeStokes

variable {n m : ℕ}

/-! ### Singular Chains -/

/-- A smooth singular n-chain in ℝᵐ: a formal ℤ-linear combination of
smooth singular n-cubes. -/
abbrev SingularChain (n m : ℕ) := SmoothSingularCube n m →₀ ℤ

/-- The chain consisting of a single cube with coefficient 1. -/
def singleChain (σ : SmoothSingularCube n m) : SingularChain n m :=
  Finsupp.single σ 1

/-! ### Boundary Operator -/

/-- The boundary of a single (n+1)-cube as an n-chain:
  ∂σ = Σᵢ (-1)^i (face_i(1) - face_i(0))

This is the standard singular cubical boundary operator. -/
def singularBoundarySingle (σ : SmoothSingularCube (n + 1) m) :
    SingularChain n m :=
  ∑ i : Fin (n + 1),
    (Finsupp.single (singularFace σ i 1) ((-1 : ℤ) ^ (i : ℕ)) +
     Finsupp.single (singularFace σ i 0) ((-1 : ℤ) ^ ((i : ℕ) + 1)))

/-- The boundary operator on singular chains (ℤ-linear extension).
  ∂(Σ kⱼ σⱼ) = Σ kⱼ · ∂σⱼ -/
def singularBoundary (c : SingularChain (n + 1) m) : SingularChain n m :=
  c.sum (fun σ k => k • singularBoundarySingle σ)

/-- The boundary of a single-cube chain. -/
theorem singularBoundary_single (σ : SmoothSingularCube (n + 1) m) :
    singularBoundary (singleChain σ) = singularBoundarySingle σ := by
  classical
  simp [singularBoundary, singleChain, Finsupp.sum_single_index, one_smul]

/-! ### Integration over Chains -/

/-- Integration of an n-form over a singular n-chain (ℤ-linear extension). -/
def integrateChain (c : SingularChain n m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  c.sum (fun σ k => (k : ℝ) * integrateForm σ ω)

/-- Integration over a single-cube chain equals integration over the cube. -/
theorem integrateChain_single (σ : SmoothSingularCube n m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateChain (singleChain σ) ω = integrateForm σ ω := by
  simp [integrateChain, singleChain, Finsupp.sum_single_index]

/-! ### Boundary Integration -/

/-- The oriented boundary integral of an n-form ω over the boundary of
a smooth singular (n+1)-cube σ:
  ∫_{∂σ} ω = Σᵢ (-1)^i * (∫_{face_i(1)} ω - ∫_{face_i(0)} ω)
This is the direct definition of boundary integration via oriented faces. -/
def bdryIntegral_singular (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) *
    (integrateForm (singularFace σ i 1) ω -
     integrateForm (singularFace σ i 0) ω)

/-! ### Chain-level Stokes Theorem -/

/-- **Stokes' theorem for smooth singular cubes** (boundary integral form):
  ∫_{∂σ} ω = ∫_σ dω

For σ : [0,1]^{n+1} → ℝᵐ smooth and ω a smooth n-form on ℝᵐ,
the oriented boundary integral of ω equals the interior integral of dω.
This is the fundamental theorem of exterior calculus for parametrized cubes. -/
theorem stokes_singular_boundary (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ ⊤ ω) :
    bdryIntegral_singular σ ω =
    integrateForm σ (fun y => extDeriv ω y) :=
  (singularStokes σ ω hω).symm

/-! ### Linearity of Chain Integration -/

/-- Chain integration is additive in the chain. -/
theorem integrateChain_add (c₁ c₂ : SingularChain n m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateChain (c₁ + c₂) ω =
    integrateChain c₁ ω + integrateChain c₂ ω := by
  classical
  simp only [integrateChain]
  rw [Finsupp.sum_add_index]
  · intro a _; simp
  · intro a _ b₁ b₂; push_cast; ring

/-- Chain integration is compatible with scalar multiplication. -/
theorem integrateChain_smul (k : ℤ) (c : SingularChain n m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateChain (k • c) ω = (k : ℝ) * integrateChain c ω := by
  simp only [integrateChain]
  rw [Finsupp.sum_smul_index (fun _ => by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  congr 1; ext σ; push_cast; ring

/-- Chain integration is zero on the zero chain. -/
theorem integrateChain_zero
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateChain (0 : SingularChain n m) ω = 0 := by
  simp [integrateChain, Finsupp.sum]

/-! ### Chain-level Stokes Theorem (Full) -/

/-- Chain integration distributes over finite sums of chains. -/
theorem integrateChain_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → SingularChain n m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateChain (s.sum f) ω =
    s.sum (fun i => integrateChain (f i) ω) := by
  induction s using Finset.cons_induction with
  | empty => simp [integrateChain_zero]
  | cons a s has ih =>
    rw [Finset.sum_cons, integrateChain_add, ih, Finset.sum_cons]

/-- Integration over the boundary chain equals the boundary integral.
  ∫_{∂σ} ω = Σᵢ (-1)^i (∫_{face_i(1)} ω - ∫_{face_i(0)} ω)

This connects the boundary operator (as chain map) to the direct
boundary integral formula. -/
theorem integrateChain_singularBoundarySingle (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateChain (singularBoundarySingle σ) ω =
    bdryIntegral_singular σ ω := by
  classical
  -- Unfold to see both sides as Finset sums
  unfold singularBoundarySingle bdryIntegral_singular
  -- Use integrateChain_finset_sum (with explicit Finset.univ)
  show integrateChain (Finset.univ.sum (fun i : Fin (n + 1) =>
    Finsupp.single (singularFace σ i 1) ((-1 : ℤ) ^ (i : ℕ)) +
    Finsupp.single (singularFace σ i 0) ((-1 : ℤ) ^ ((i : ℕ) + 1)))) ω = _
  rw [integrateChain_finset_sum]
  congr 1; ext i
  rw [integrateChain_add]
  unfold integrateChain
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  push_cast; ring

/-- **Stokes' theorem for a single singular cube** (chain formulation):
   ∫_{∂σ} ω = ∫_σ dω

For a smooth singular (n+1)-cube σ and smooth n-form ω, the integral
over the boundary chain equals the interior integral of dω. -/
theorem stokes_singular_chain (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ ⊤ ω) :
    integrateChain (singularBoundarySingle σ) ω =
    integrateForm σ (fun y => extDeriv ω y) := by
  rw [integrateChain_singularBoundarySingle]
  exact stokes_singular_boundary σ ω hω

/-! ### Boundary Operator Algebraic Properties -/

/-- The boundary of the zero chain is zero. -/
theorem singularBoundary_zero :
    singularBoundary (0 : SingularChain (n + 1) m) = 0 := by
  simp [singularBoundary, Finsupp.sum]

/-- The boundary operator distributes over chain addition. -/
theorem singularBoundary_add (c₁ c₂ : SingularChain (n + 1) m) :
    singularBoundary (c₁ + c₂) = singularBoundary c₁ + singularBoundary c₂ := by
  classical
  unfold singularBoundary
  apply Finsupp.sum_add_index
  · intro a _; exact zero_smul ℤ (singularBoundarySingle a)
  · intro a _ b₁ b₂; exact add_smul b₁ b₂ (singularBoundarySingle a)

/-- The boundary of a single-coefficient chain. -/
theorem singularBoundary_single_coeff (σ : SmoothSingularCube (n + 1) m) (k : ℤ) :
    singularBoundary (Finsupp.single σ k) = k • singularBoundarySingle σ := by
  simp [singularBoundary, Finsupp.sum_single_index, zero_smul]

/-! ### Stokes' Theorem for Arbitrary Chains -/

/-- **Stokes' theorem for arbitrary singular chains**:
   ∫_{∂c} ω = ∫_c dω

For any singular chain c (formal ℤ-linear combination of smooth cubes)
and smooth n-form ω, the integral of ω over the boundary chain equals
the integral of dω over c. This extends the single-cube Stokes theorem
by ℤ-linearity. -/
theorem stokes_chain (c : SingularChain (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ ⊤ ω) :
    integrateChain (singularBoundary c) ω =
    integrateChain c (fun y => extDeriv ω y) := by
  induction c using Finsupp.induction with
  | zero =>
    simp [singularBoundary_zero, integrateChain_zero]
  | single_add σ k f hσ hk ih =>
    rw [singularBoundary_add, integrateChain_add, integrateChain_add, ih]
    congr 1
    rw [singularBoundary_single_coeff, integrateChain_smul,
        stokes_singular_chain σ ω hω]
    simp [integrateChain, Finsupp.sum_single_index]

end SingularCubeStokes

end
