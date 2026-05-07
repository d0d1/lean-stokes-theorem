/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import Mathlib.Data.Real.Basic

/-!
# Jacobian Sign Branches

This module contains the two discrete sign branches for a nonzero local
Jacobian determinant.  It deliberately does not expose arbitrary real-valued
orientation signs.
-/

namespace SmoothDomain

/-- The two possible nonzero signs of a local flattening-chart Jacobian determinant. -/
inductive JacobianSign where
  /-- Positive ambient Jacobian determinant for a local flattening map. -/
  | pos
  /-- Negative ambient Jacobian determinant for a local flattening map. -/
  | neg
  deriving DecidableEq

namespace JacobianSign

/-- Sign with which a chart branch changes oriented top-dimensional domain integrals. -/
def domainSign : JacobianSign → ℝ
  | pos => 1
  | neg => -1

/-- Sign with which a chart branch changes induced boundary integrals.

For the upper half-space convention `{x₀ ≥ 0}`, the model boundary sign is `-1`
because the outward normal is `-e₀`; reversing the ambient chart orientation
reverses the induced boundary orientation. -/
def boundarySign : JacobianSign → ℝ
  | pos => -1
  | neg => 1

@[simp] theorem domainSign_pos : domainSign pos = 1 := rfl

@[simp] theorem domainSign_neg : domainSign neg = -1 := rfl

@[simp] theorem boundarySign_pos : boundarySign pos = -1 := rfl

@[simp] theorem boundarySign_neg : boundarySign neg = 1 := rfl

/-- Boundary orientation changes by the negative of the ambient domain-orientation sign. -/
theorem boundarySign_eq_neg_domainSign (σ : JacobianSign) :
    σ.boundarySign = -σ.domainSign := by
  cases σ <;> simp [boundarySign, domainSign]

@[simp] theorem domainSign_ne_zero (σ : JacobianSign) : σ.domainSign ≠ 0 := by
  cases σ <;> simp [domainSign]

@[simp] theorem boundarySign_ne_zero (σ : JacobianSign) : σ.boundarySign ≠ 0 := by
  cases σ <;> simp [boundarySign]

end JacobianSign

end SmoothDomain
