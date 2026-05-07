/-
Copyright (c) 2025 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.Chain

/-!
# ∂² = 0 for Smooth Singular Cubical Chains

Proves that the boundary operator on smooth singular cubical chains
satisfies ∂∂ = 0 both at the chain level (the true chain complex identity)
and at the integral level.

## Main results

* `SingularCubeStokes.faceInclusion_comp_le`: Face inclusion commutation identity
* `SingularCubeStokes.singularFace_comp`: Face-of-face for singular cubes
* `SingularCubeStokes.bdry_bdry_chain_zero`: ∂²σ = 0 as chain identity
* `SingularCubeStokes.bdry_bdry_integral_zero`: ∫_{∂²σ} ω = 0

## Proof strategy

The chain-level ∂²=0 uses a sign-reversing involution on the index set
of the double boundary sum. For i ≤ j, the involution pairs
(i, ε, j, δ) with (j+1, δ, i, ε). The face-of-face identity shows
these produce the same cube, while sign arithmetic shows their
coefficients are opposite.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace SingularCubeStokes

variable {n m : ℕ}

/-! ### Face Composition Identity -/

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 400000 in
/-- Face inclusion composition: when (i : ℕ) ≤ (j : ℕ),
  faceInclusion i ε (faceInclusion j δ t) = faceInclusion (j+1) δ (faceInclusion i ε t) -/
theorem faceInclusion_comp_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : (i : ℕ) ≤ (j : ℕ)) (ε δ : ℝ) (t : Fin n → ℝ) :
    faceInclusion i ε (faceInclusion j δ t) =
    faceInclusion ⟨(j : ℕ) + 1, by omega⟩ δ
      (faceInclusion ⟨(i : ℕ), by omega⟩ ε t) := by
  funext ⟨k, hk⟩
  simp only [faceInclusion]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
  all_goals (first | rfl | (congr 1; ext; omega) | omega)

/-- The face-of-face identity for singular cubes: for i ≤ j,
  face j δ (face i ε σ) = face i ε (face (j+1) δ σ) -/
theorem singularFace_comp {n m : ℕ} (σ : SmoothSingularCube (n + 2) m)
    (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : (i : ℕ) ≤ (j : ℕ)) (ε δ : ℝ) :
    singularFace (singularFace σ i ε) j δ =
    singularFace (singularFace σ ⟨(j : ℕ) + 1, by omega⟩ δ)
      ⟨(i : ℕ), by omega⟩ ε := by
  ext1; funext t
  simp only [singularFace, comp_apply]
  congr 1
  exact faceInclusion_comp_le i j hij ε δ t

/-- Integration over a face-of-face commutes. -/
theorem integrateForm_face_face {n m : ℕ} (σ : SmoothSingularCube (n + 2) m)
    (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : (i : ℕ) ≤ (j : ℕ)) (ε δ : ℝ)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateForm (singularFace (singularFace σ i ε) j δ) ω =
    integrateForm
      (singularFace (singularFace σ ⟨(j : ℕ) + 1, by omega⟩ δ)
        ⟨(i : ℕ), by omega⟩ ε) ω := by
  rw [singularFace_comp σ i j hij ε δ]

/-! ### ∂² = 0 (Chain-Level Identity) -/

/-- The boundary operator as an additive group homomorphism. -/
def singularBoundaryHom (n m : ℕ) : SingularChain (n + 1) m →+ SingularChain n m where
  toFun := singularBoundary
  map_zero' := singularBoundary_zero
  map_add' := singularBoundary_add

/-- singularBoundary distributes over Finset sums. -/
theorem singularBoundary_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → SingularChain (n + 1) m) :
    singularBoundary (s.sum f) = s.sum (fun i => singularBoundary (f i)) :=
  map_sum (singularBoundaryHom n m) f s

/-! ### Involution machinery for ∂² = 0 -/

/-- The sign-reversing involution on Fin(n+2) × Fin(n+1) for the ∂²=0 proof.
Maps (i, j) to (j+1, i) when i ≤ j, and to (j, i-1) when i > j. -/
private def bdryInvol (n : ℕ) : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
  fun ⟨i, j⟩ =>
    if h : (i : ℕ) ≤ (j : ℕ) then
      (⟨(j : ℕ) + 1, by omega⟩, ⟨(i : ℕ), by omega⟩)
    else
      (⟨(j : ℕ), by omega⟩, ⟨(i : ℕ) - 1, by omega⟩)

set_option linter.style.maxHeartbeats false in
-- Nested split_ifs on double bdryInvol application.
set_option maxHeartbeats 1600000 in
private theorem bdryInvol_invol (n : ℕ) (p : Fin (n + 2) × Fin (n + 1)) :
    bdryInvol n (bdryInvol n p) = p := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  simp only [bdryInvol]
  split_ifs with h1 h2 h3
  · exfalso; exact absurd (show j + 1 ≤ i from h2) (by omega)
  · rfl
  · exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext (by dsimp))
  · exfalso; exact absurd (show ¬(j ≤ i - 1) from h3) (by omega)

set_option linter.style.maxHeartbeats false in
-- Simple case split on the dite condition.
set_option maxHeartbeats 400000 in
private theorem bdryInvol_ne (n : ℕ) (p : Fin (n + 2) × Fin (n + 1)) :
    bdryInvol n p ≠ p := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  simp only [bdryInvol]
  split_ifs with h
  · exact fun heq => absurd
      (show j + 1 = i from congrArg (fun x => (Prod.fst x).val) heq) (by omega)
  · exact fun heq => absurd
      (show j = i from congrArg (fun x => (Prod.fst x).val) heq) (by omega)

/-- (-1)^(k-1) = -(-1)^k for k ≥ 1. Used in case 2 of the involution cancellation. -/
private lemma neg_one_pow_pred (k : ℕ) (hk : 1 ≤ k) : (-1 : ℤ) ^ (k - 1) = -(-1) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [pow_succ]

set_option linter.style.maxHeartbeats false in
-- The split_ifs generates many goals (up to 256), each closed by ring.
set_option maxHeartbeats 12800000 in
/-- **∂² = 0 (chain-level identity)**: the boundary of the boundary of any
smooth singular cube is zero as a formal chain.

  ∂(∂σ) = 0

Proved by expressing the double boundary as a sum indexed by
Fin(n+2) × Fin(n+1) and applying a sign-reversing fixed-point-free
involution `bdryInvol`. For each pair (i, j) with i ≤ j, the partner
(j+1, i) gives the same cube via face-of-face (`singularFace_comp`)
with opposite coefficient. The ext + split_ifs + ring strategy
handles all sign arithmetic automatically. -/
theorem bdry_bdry_chain_zero (σ : SmoothSingularCube (n + 2) m) :
    singularBoundary (singularBoundarySingle σ) = 0 := by
  classical
  unfold singularBoundarySingle
  rw [singularBoundary_finset_sum]
  simp_rw [singularBoundary_add, singularBoundary_single_coeff, singularBoundarySingle,
           Finset.smul_sum, smul_add, Finsupp.smul_single, ← Finset.sum_add_distrib]
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ]
  apply Finset.sum_ninvolution (g := bdryInvol n)
  · -- Cancellation: f(i,j) + f(g(i,j)) = 0
    intro ⟨i, j⟩
    simp only [bdryInvol]
    split_ifs with h
    · -- Case i ≤ j: partner is (j+1, i)
      -- Face-of-face: face_j(δ)(face_i(ε)σ) = face_i(ε)(face_{j+1}(δ)σ)
      have hfc := singularFace_comp σ i j h
      simp only [hfc]
      ext τ
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> ring
    · -- Case i > j: partner is (j, i-1)
      -- Face-of-face with (j, i-1) where j ≤ i-1:
      have hle : (j : ℕ) ≤ (i : ℕ) - 1 := by omega
      have hfc := singularFace_comp σ
        (⟨(j : ℕ), by omega⟩ : Fin (n + 2))
        (⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 1))
        hle
      simp only [hfc]
      -- Simplify (i-1)+1 = i and Fin equalities
      simp only [show (i : ℕ) - 1 + 1 = (i : ℕ) from by omega]
      simp only [show (⟨(i : ℕ), by omega⟩ : Fin (n + 2)) = i from Fin.ext rfl,
                 show (⟨(j : ℕ), by omega⟩ : Fin (n + 1)) = j from Fin.ext rfl]
      -- Normalize (-1)^(i-1) = -(-1)^i for ring
      simp only [neg_one_pow_pred (i : ℕ) (by omega : 1 ≤ (i : ℕ))]
      ext τ
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> ring
  · -- Fixed-point-free
    intro p _
    exact bdryInvol_ne n p
  · -- Membership in univ
    intro _
    exact Finset.mem_univ _
  · -- Involution
    intro p
    exact bdryInvol_invol n p

/-- ∂² = 0 for arbitrary singular chains:
  ∂(∂c) = 0 -/
theorem bdry_bdry_chain_zero_general (c : SingularChain (n + 2) m) :
    singularBoundary (singularBoundary c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [singularBoundary_zero]
  | single_add σ k f hσ hk ih =>
    rw [singularBoundary_add, singularBoundary_add, ih, add_zero,
        singularBoundary_single_coeff]
    have h : singularBoundary (k • singularBoundarySingle σ) =
        k • singularBoundary (singularBoundarySingle σ) :=
      (singularBoundaryHom n m).map_zsmul (singularBoundarySingle σ) k
    rw [h, bdry_bdry_chain_zero σ, smul_zero]

/-! ### ∂² = 0 (Integral Level) -/

/-- Integration over the zero form is zero. -/
theorem integrateForm_zero (σ : SmoothSingularCube n m) :
    integrateForm σ (fun _ => 0) = 0 := by
  simp [integrateForm, pullbackForm]

/-- **∂² = 0 at the integral level**: ∫_{∂(∂σ)} ω = 0
This follows immediately from the chain-level identity ∂²σ = 0. -/
theorem bdry_bdry_integral_zero {n m : ℕ} (σ : SmoothSingularCube (n + 2) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    integrateChain (singularBoundary (singularBoundarySingle σ)) ω = 0 := by
  rw [bdry_bdry_chain_zero σ, integrateChain_zero]

end SingularCubeStokes

end
