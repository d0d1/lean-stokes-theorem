/-
Copyright (c) 2025 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.FaceMatching
import LeanStokes.CubeStokes.Unified

/-!
# Stokes' Theorem for Smooth Singular Cubes

The main theorem: for σ : [0,1]^{n+1} → ℝᵐ smooth and ω an n-form on ℝᵐ,

  ∫_σ dω = ∫_{∂σ} ω

where the LHS is the integral of σ*(dω) over the unit cube and the RHS
is the oriented sum of face integrals.

## Main results

* `SingularCubeStokes.singularStokes`: The full singular cubical Stokes theorem

## Proof strategy

1. Define η = σ*ω (pullback of ω along σ), an n-form on ℝ^{n+1}
2. By `extDeriv_pullback`: d(η) = σ*(dω) pointwise
3. By existing `stokes_extDeriv` on [0,1]^{n+1}: ∫ dη = boundary integral of η
4. LHS gives ∫ σ*(dω) = integrateForm σ (dω)
5. RHS gives Σ faces (±) integrateForm(face, ω) via face_matching
-/

noncomputable section

open Set Finset MeasureTheory Filter
open scoped Topology

namespace SingularCubeStokes

variable {n m : ℕ}

/-- **Naturality of pullback**: The exterior derivative commutes with pullback.
  d(σ*ω) = σ*(dω)
This is the key identity that reduces singular Stokes to box Stokes.
It follows directly from mathlib's `extDeriv_pullback`. -/
theorem pullback_extDeriv (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (x : Fin (n + 1) → ℝ) :
    extDeriv (pullbackForm σ ω) x =
    (extDeriv ω (σ.toFun x)).compContinuousLinearMap (fderiv ℝ σ.toFun x) := by
  -- pullbackForm σ ω x = (ω(σ x)).compCLM(fderiv ℝ σ x)
  -- This has exactly the form that extDeriv_pullback handles:
  -- extDeriv (fun x => (ω(f x)).compCLM(fderiv f x)) x = (extDeriv ω (f x)).compCLM(fderiv f x)
  have hω_diff : DifferentiableAt ℝ ω (σ.toFun x) :=
    (hω.differentiable (by simp)).differentiableAt
  have hσ_smooth : ContDiffAt ℝ (⊤ : ℕ∞) σ.toFun x := σ.smooth.contDiffAt
  exact extDeriv_pullback hω_diff hσ_smooth (by
    simpa [minSmoothness_of_isRCLikeNormedField] using
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤) :
        (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))

/-- The pullback of dω equals the exterior derivative of the pullback of ω,
expressed via `pullbackForm`. -/
theorem pullbackForm_extDeriv_eq (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (x : Fin (n + 1) → ℝ) :
    pullbackForm σ (fun y => extDeriv ω y) x = extDeriv (pullbackForm σ ω) x := by
  -- LHS = (extDeriv ω (σ x)).compCLM(fderiv ℝ σ x)
  -- RHS = extDeriv(pullbackForm σ ω) x = same thing by pullback_extDeriv
  rw [pullback_extDeriv σ ω hω x]
  rfl

/-- **Stokes' theorem for smooth singular cubes (abstract form).**

For a smooth singular (n+1)-cube σ : ℝ^{n+1} → ℝᵐ and a smooth n-form ω
on ℝᵐ:

  ∫_{[0,1]^{n+1}} σ*(dω) = bdryIntegral(σ*ω)

The LHS is the integral of the pullback of dω over the unit cube.
The RHS is the boundary integral of the pullback form σ*ω, computed
via the existing box Stokes theorem.

This is the singular cubical Stokes theorem reduced to our existing
box Stokes infrastructure. -/
theorem singularStokes_abstract (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    integrateForm σ (fun y => extDeriv ω y) =
    CubeStokes.bdryIntegral
      (CubeStokes.toCoordNForm (pullbackForm σ ω))
      (fun _ => 0) (fun _ => 1) := by
  -- Step 1: The LHS equals ∫ extDeriv(σ*ω) on [0,1]^{n+1} by naturality
  unfold integrateForm
  -- We need: ∫ (pullbackForm σ (extDeriv ω)) (standard) = ∫ extDeriv(σ*ω) (standard)
  have h_eq : ∀ x ∈ Icc (fun _ : Fin (n+1) => (0:ℝ)) (fun _ => 1),
      (pullbackForm σ (fun y => extDeriv ω y) x) (fun j => Pi.single j 1) =
      extDeriv (pullbackForm σ ω) x (fun j => Pi.single j 1) := by
    intro x _
    rw [← pullbackForm_extDeriv_eq σ ω hω x]
  -- Step 2: Rewrite using pointwise equality
  rw [show (∫ x in Icc (fun _ : Fin (n+1) => (0:ℝ)) (fun _ => 1),
        (pullbackForm σ (fun y => extDeriv ω y) x) (fun j => Pi.single j 1)) =
      (∫ x in Icc (fun _ : Fin (n+1) => (0:ℝ)) (fun _ => 1),
        extDeriv (pullbackForm σ ω) x (fun j => Pi.single j 1)) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc h_eq]
  -- Step 3: Apply stokes_extDeriv to σ*ω on [0,1]^{n+1}
  -- Uses weaker hypotheses: Differentiable + IsSmooth(coefficients)
  have hpb_diff : Differentiable ℝ (pullbackForm σ ω) :=
    pullbackForm_differentiable σ ω hω
  have hpb_smooth : CubeStokes.IsSmooth (CubeStokes.toCoordNForm (pullbackForm σ ω)) :=
    toCoordNForm_pullback_isSmooth σ ω hω
  exact CubeStokes.stokes_extDeriv (pullbackForm σ ω)
    (fun _ => 0) (fun _ => 1) (fun _ => by norm_num) hpb_diff hpb_smooth

/-- **Stokes' theorem for smooth singular cubes (integration form).**

  integrateForm σ (dω) = Σᵢ (-1)ⁱ · (integrateForm (face σ i 1) ω - integrateForm (face σ i 0) ω)

This expresses the singular cubical Stokes theorem with explicit boundary orientation signs.
The sign (-1)ⁱ comes from the boundary orientation of the i-th face pair. -/
theorem singularStokes (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    integrateForm σ (fun y => extDeriv ω y) =
    ∑ i : Fin (n + 1),
      (-1 : ℝ) ^ (i : ℕ) *
      (integrateForm (singularFace σ i 1) ω -
       integrateForm (singularFace σ i 0) ω) := by
  -- Step 1: Use the abstract form
  rw [singularStokes_abstract σ ω hω]
  -- Goal: bdryIntegral(toCoordNForm(σ*ω)) 0 1 = Σᵢ (-1)^i * (face_1 - face_0)
  -- Step 2: Unfold bdryIntegral and integrateForm
  simp only [CubeStokes.bdryIntegral, CubeStokes.signedCoeff, CubeStokes.toCoordNForm,
             integrateForm, Function.comp_def]
  -- Both sides are sums; show they agree term by term
  congr 1
  ext i
  -- Step 3: Factor out (-1)^i and prove integral equality
  -- LHS: ∫ (-1)^i * f(insertNth 1) - ∫ (-1)^i * f(insertNth 0)
  -- RHS: (-1)^i * (∫ g(face 1) - ∫ g(face 0))
  -- After ring manipulation: suffices to show ∫ f(insertNth ε) = ∫ g(face ε) for each ε
  ring_nf
  congr 1
  · -- The front face (ε = 1): show ∫ f(x) * c = (∫ g(x)) * c
    -- Factor constant out of integral
    rw [integral_mul_const]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    have h := face_matching σ ω i 1 x
    rw [faceInclusion_eq_insertNth] at h
    exact h
  · -- The back face (ε = 0)
    rw [integral_mul_const]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    have h := face_matching σ ω i 0 x
    rw [faceInclusion_eq_insertNth] at h
    exact h

end SingularCubeStokes

end
