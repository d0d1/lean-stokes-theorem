/-
Copyright (c) 2025 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.Smoothness

/-!
# Face Matching for Singular Cubical Stokes

Proves the face matching identity connecting `bdryIntegral(toCoordNForm(σ*ω))`
to the sum of face integrals.

## Main results

* `fderiv_faceInclusion_single`: The Fréchet derivative of `faceInclusion i ε` maps
  standard basis vectors `e_j` to `e_{succAbove i j}`.
* `face_matching`: The face matching identity connecting face integrands to
  the singular face pullback.
-/

noncomputable section

open Set Finset MeasureTheory Filter ContinuousLinearMap
open scoped Topology

namespace SingularCubeStokes

variable {n m : ℕ}

/-! ### The linear part of faceInclusion -/

/-- The linear part of `faceInclusion i ε`: inserts 0 at position i.
This is the Fréchet derivative of `faceInclusion i ε` (which is affine). -/
private def faceLinearMap (i : Fin (n + 1)) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun k =>
    if h1 : (k : ℕ) < (i : ℕ) then
      proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨(k : ℕ), by omega⟩
    else if _ : (k : ℕ) = (i : ℕ) then
      0
    else
      proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨(k : ℕ) - 1, by omega⟩)

/-- Helper: `Fin.succAbove i j` has value `j` if `j < i`, else `j + 1`. -/
private theorem succAbove_val (i : Fin (n + 1)) (j : Fin n) :
    (Fin.succAbove i j : ℕ) = if (j : ℕ) < (i : ℕ) then (j : ℕ) else (j : ℕ) + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> first | exact Fin.val_castSucc j | exact Fin.val_succ j

/-- `faceInclusion i ε` equals its linear part plus a constant. -/
private theorem faceInclusion_eq_affine (i : Fin (n + 1)) (ε : ℝ) (t : Fin n → ℝ) :
    faceInclusion i ε t = faceLinearMap i t + Pi.single i ε := by
  ext k
  simp only [faceLinearMap, faceInclusion, pi_apply, Pi.add_apply, Pi.single_apply]
  by_cases h1 : (k : ℕ) < (i : ℕ)
  · simp [h1, show ¬(k = i) from fun h => absurd (congrArg Fin.val h) (Nat.ne_of_lt h1)]
  · by_cases h2 : (k : ℕ) = (i : ℕ)
    · have hki : k = i := Fin.ext h2
      simp [hki]
    · simp [h1, h2, show ¬(k = i) from fun h => absurd (congrArg Fin.val h) h2]

/-- `faceInclusion i ε` has `faceLinearMap i` as its Fréchet derivative. -/
private theorem hasFDerivAt_faceInclusion (i : Fin (n + 1)) (ε : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (faceInclusion i ε) (faceLinearMap i) x := by
  have h_eq : faceInclusion i ε = fun t => faceLinearMap i t + Pi.single i ε :=
    funext (faceInclusion_eq_affine i ε)
  rw [h_eq]
  exact (faceLinearMap i).hasFDerivAt.add_const _

set_option maxHeartbeats 800000 in
-- The proof of faceLinearMap_single involves extensive case splits on Fin
-- comparisons that require many heartbeats due to omega/split_ifs overhead.
/-- `faceLinearMap i` sends `e_j` to `e_{succAbove i j}`. -/
private theorem faceLinearMap_single (i : Fin (n + 1)) (j : Fin n) :
    faceLinearMap i (Pi.single j 1 : Fin n → ℝ) =
    (Pi.single (Fin.succAbove i j) (1 : ℝ) : Fin (n + 1) → ℝ) := by
  ext k
  simp only [faceLinearMap, pi_apply, Pi.single_apply]
  simp_rw [show ∀ (a : Fin (n+1)), (k = a) ↔ ((k : ℕ) = (a : ℕ)) from
    fun a => Fin.ext_iff]
  rw [show (Fin.succAbove i j : ℕ) = if (j : ℕ) < (i : ℕ) then (j : ℕ) else (j : ℕ) + 1 from
    succAbove_val i j]
  have hj := j.isLt
  have hk := k.isLt
  have hi := i.isLt
  by_cases h1 : (k : ℕ) < (i : ℕ)
  · have hne : ¬((k : ℕ) = (i : ℕ)) := Nat.ne_of_lt h1
    simp only [h1, hne, dite_true, dite_false, proj_apply, Pi.single_apply, Fin.ext_iff]
    congr 1; ext; constructor <;> intro h <;> (split_ifs at * <;> omega)
  · by_cases h2 : (k : ℕ) = (i : ℕ)
    · have lhs_eq : (if h : (k : ℕ) < (i : ℕ) then
            proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨(k : ℕ), by omega⟩
          else if _ : (k : ℕ) = (i : ℕ) then (0 : (Fin n → ℝ) →L[ℝ] ℝ)
          else proj (R := ℝ) (φ := fun _ : Fin n => ℝ) ⟨(k : ℕ) - 1, by omega⟩)
          (Pi.single j 1 : Fin n → ℝ) = 0 := by
        rw [dif_neg h1, dif_pos h2, zero_apply]
      rw [lhs_eq, if_neg]
      intro h; split_ifs at h <;> omega
    · simp only [h1, h2, dite_false, proj_apply, Pi.single_apply, Fin.ext_iff]
      congr 1; ext; constructor <;> intro h <;> (split_ifs at * <;> omega)

/-! ### Main derivative identity -/

/-- The Fréchet derivative of `faceInclusion i ε` sends `e_j` to `e_{succAbove i j}`. -/
theorem fderiv_faceInclusion_single (i : Fin (n + 1)) (ε : ℝ)
    (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (faceInclusion i ε) x (Pi.single j 1) =
    (Pi.single (Fin.succAbove i j) (1 : ℝ) : Fin (n + 1) → ℝ) := by
  rw [(hasFDerivAt_faceInclusion i ε x).fderiv, faceLinearMap_single]

/-! ### Face matching identity -/

/-- **Face matching identity**: The pullback form evaluated at a face point,
with standard basis vectors adapted via `succAbove`, equals the face pullback.

Mathematically: `ω(σ(face x))(Dσ(face x) · e_{succAbove i ·})`
equals `ω(σ(face x))((D(σ ∘ face) x) · e_·)`. -/
theorem face_matching (σ : SmoothSingularCube (n + 1) m)
    (ω : (Fin m → ℝ) → (Fin m → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (i : Fin (n + 1)) (ε : ℝ) (x : Fin n → ℝ) :
    (pullbackForm σ ω (faceInclusion i ε x)) (fun k => Pi.single (Fin.succAbove i k) 1) =
    (pullbackForm (singularFace σ i ε) ω x) (fun j => Pi.single j 1) := by
  simp only [pullbackForm, singularFace,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  have hσ_diff : DifferentiableAt ℝ σ.toFun (faceInclusion i ε x) :=
    (σ.smooth.differentiable (by simp)).differentiableAt
  have hface_diff : DifferentiableAt ℝ (faceInclusion i ε) x :=
    (faceInclusion_differentiable i ε).differentiableAt
  have hchain : fderiv ℝ (σ.toFun ∘ faceInclusion i ε) x =
      (fderiv ℝ σ.toFun (faceInclusion i ε x)).comp (fderiv ℝ (faceInclusion i ε) x) :=
    fderiv_comp x hσ_diff hface_diff
  calc fderiv ℝ σ.toFun (faceInclusion i ε x) (Pi.single (Fin.succAbove i j) 1)
      = fderiv ℝ σ.toFun (faceInclusion i ε x)
          (fderiv ℝ (faceInclusion i ε) x (Pi.single j 1)) := by
        rw [fderiv_faceInclusion_single]
    _ = (fderiv ℝ σ.toFun (faceInclusion i ε x)).comp
          (fderiv ℝ (faceInclusion i ε) x) (Pi.single j 1) := by
        rw [ContinuousLinearMap.comp_apply]
    _ = fderiv ℝ (σ.toFun ∘ faceInclusion i ε) x (Pi.single j 1) := by
        rw [← hchain]

/-! ### Equivalence with Fin.insertNth -/

/-- `faceInclusion i ε x` and `Fin.insertNth i ε x` are the same function.
Both insert `ε` at position `i` in a vector `x : Fin n → ℝ`. -/
theorem faceInclusion_eq_insertNth (i : Fin (n + 1)) (ε : ℝ) (x : Fin n → ℝ) :
    faceInclusion i ε x = Fin.insertNth i ε x := by
  ext k
  by_cases hk : k = i
  · rw [hk, Fin.insertNth_apply_same]
    simp [faceInclusion]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
    rw [← hj, Fin.insertNth_apply_succAbove]
    have h_val : (Fin.succAbove i j : ℕ) =
        if (j : ℕ) < (i : ℕ) then (j : ℕ) else (j : ℕ) + 1 := by
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> first | exact Fin.val_castSucc j | exact Fin.val_succ j
    simp only [faceInclusion]
    by_cases hji : (j : ℕ) < (i : ℕ)
    · have hsa_val : (Fin.succAbove i j : ℕ) = (j : ℕ) := by rw [h_val, if_pos hji]
      simp only [show ((Fin.succAbove i j : ℕ) < (i : ℕ)) from hsa_val ▸ hji, dite_true]
      congr 1; simp only [Fin.ext_iff]; omega
    · have hsa_val : (Fin.succAbove i j : ℕ) = (j : ℕ) + 1 := by rw [h_val, if_neg hji]
      have hsa_gt : ¬((Fin.succAbove i j : ℕ) < (i : ℕ)) := by omega
      have hsa_ne : ¬((Fin.succAbove i j : ℕ) = (i : ℕ)) := by omega
      simp only [hsa_gt, hsa_ne, dite_false]
      congr 1; simp only [Fin.ext_iff]; omega

end SingularCubeStokes

end
