/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Faces

/-!
# Cubical Boundary Operator and ∂² = 0

The fundamental algebraic property of the cubical boundary operator is ∂² = 0:
applying the boundary twice gives zero. This file proves the sign cancellation
lemma that is the algebraic core of ∂² = 0.

## Main results

* `CubeStokes.neg_one_pow_add_of_parity_ne`: Helper for sign cancellation.
* `CubeStokes.bdry_sq_sign_cancel`: Sign cancellation for paired codim-2 faces.
* `CubeStokes.bdry_sq_geometric`: Combined geometric + sign ∂² = 0.
-/

open Set Finset MeasureTheory Filter Function Fin
open scoped Topology

noncomputable section

namespace CubeStokes

/-- The sign of the (i, ε)-face in the cubical boundary formula. -/
def bdrySign (i : Fin (k + 1)) (ε : Bool) : ℤ :=
  (-1) ^ (i.val + ε.toNat)

/-- The composite sign for a codimension-2 face. -/
def bdrySign2 (i : Fin (k + 2)) (ε : Bool) (j : Fin (k + 1)) (η : Bool) : ℤ :=
  bdrySign i ε * bdrySign j η

/-- If two natural numbers have different parity, `(-1)^a + (-1)^b = 0`. -/
theorem neg_one_pow_add_of_parity_ne {a b : ℕ} (h : a % 2 ≠ b % 2) :
    (-1 : ℤ) ^ a + (-1 : ℤ) ^ b = 0 := by
  have fact : ∀ m : ℕ, (-1 : ℤ) ^ m = (-1) ^ (m % 2) := fun m => by
    conv_lhs => rw [show m = m % 2 + 2 * (m / 2) from (Nat.mod_add_div m 2).symm]
    rw [pow_add, pow_mul, show (-1:ℤ)^2 = 1 from by norm_num, one_pow, mul_one]
  rw [fact a, fact b]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · exact absurd (by omega : a % 2 = b % 2) h
  · rw [ha0, hb1]; norm_num
  · rw [ha1, hb0]; norm_num
  · exact absurd (by omega : a % 2 = b % 2) h

/-- The combined exponents for the two paths to the same codim-2 face have
    different parity. This is the computational core of ∂² = 0. -/
private theorem bdry_sq_parity (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (ε η : Bool) :
    (i.val + ε.toNat + (j.val + η.toNat)) % 2 ≠
    ((i.succAbove j).val + η.toNat + ((j.predAbove i).val + ε.toNat)) % 2 := by
  simp only [succAbove, predAbove, lt_def, val_castSucc, apply_dite Fin.val,
    val_pred, coe_castPred, dite_eq_ite, apply_ite Fin.val, val_succ]
  split_ifs <;> omega

/-- **Sign cancellation for ∂².** -/
theorem bdry_sq_sign_cancel (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (ε η : Bool) :
    bdrySign2 i ε j η + bdrySign2 (i.succAbove j) η (j.predAbove i) ε = 0 := by
  unfold bdrySign2 bdrySign
  have h1 : (-1:ℤ) ^ (i.val + ε.toNat) * (-1) ^ (j.val + η.toNat) =
      (-1) ^ (i.val + ε.toNat + (j.val + η.toNat)) := (pow_add (-1) _ _).symm
  have h2 : (-1:ℤ) ^ ((i.succAbove j).val + η.toNat) *
      (-1) ^ ((j.predAbove i).val + ε.toNat) =
      (-1) ^ ((i.succAbove j).val + η.toNat + ((j.predAbove i).val + ε.toNat)) :=
    (pow_add (-1) _ _).symm
  rw [h1, h2]
  exact neg_one_pow_add_of_parity_ne (bdry_sq_parity n i j ε η)

/-- Key parity lemma stated as an equation on `(-1)^_`. -/
theorem succAbove_predAbove_neg_one_pow (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ ((i.succAbove j).val + (j.predAbove i).val) =
    -((-1 : ℤ) ^ (i.val + j.val)) := by
  have h : (i.val + j.val) % 2 ≠
      ((i.succAbove j).val + (j.predAbove i).val) % 2 := by
    simp only [succAbove, predAbove, lt_def, val_castSucc, apply_dite Fin.val,
      val_pred, coe_castPred, dite_eq_ite, apply_ite Fin.val, val_succ]
    split_ifs <;> omega
  have sum_zero := neg_one_pow_add_of_parity_ne h
  linarith

/-- **∂² = 0 (geometric + algebraic combined statement).** -/
theorem bdry_sq_geometric (n : ℕ) (B : CubicalBox (n + 2))
    (i : Fin (n + 3)) (j : Fin (n + 2)) (ε η : Bool) :
    (∀ k, (faceBox (faceBox B i) j).lo k =
          (faceBox (faceBox B (i.succAbove j)) (j.predAbove i)).lo k) ∧
    (∀ k, (faceBox (faceBox B i) j).hi k =
          (faceBox (faceBox B (i.succAbove j)) (j.predAbove i)).hi k) ∧
    bdrySign2 i ε j η + bdrySign2 (i.succAbove j) η (j.predAbove i) ε = 0 :=
  ⟨fun k => faceBox_faceBox_lo B i j k,
   fun k => faceBox_faceBox_hi B i j k,
   bdry_sq_sign_cancel n i j ε η⟩

end CubeStokes
end
