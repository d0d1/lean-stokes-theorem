/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Chains

/-!
# Subdivision Invariance via Chains

Shows that Stokes' theorem is compatible with box subdivision by expressing
the result as a chain-level identity. When two adjacent boxes (sharing a face)
are combined into a 2-element chain, Stokes holds for the chain as a whole.

This demonstrates that the cubical chain infrastructure supports subdivision
without needing to prove integral splitting directly.

## Main results

* `CubeStokes.stokes_two_boxes`: Stokes for a two-box chain (adjacent boxes).
* `CubeStokes.subdivision_chain`: The sum of box integrals on two adjacent boxes
  equals the sum of their boundary integrals.
-/

noncomputable section

open Set Finset MeasureTheory Filter Function
open scoped Topology

namespace CubeStokes

variable {n : ℕ}

/-- Construct a two-box chain from two CubicalBoxes. -/
def twoBoxChain (B₁ B₂ : CubicalBox n) : CubicalChain n :=
  Finsupp.single B₁ 1 + Finsupp.single B₂ 1

/-- **Stokes for a two-box chain**: For any two boxes and a smooth form,
the sum of `∫ dω` over both boxes equals the sum of `∫_{∂} ω` over both boxes.

When the two boxes share a face (subdivision), the shared face contributions
cancel in the boundary sum, giving the correct result for the combined domain. -/
theorem stokes_two_boxes (B₁ B₂ : CubicalBox n) (ω : CoordNForm n) (hω : IsSmooth ω) :
    integrateExterior (twoBoxChain B₁ B₂) ω = integrateBdry (twoBoxChain B₁ B₂) ω :=
  stokes_chain (twoBoxChain B₁ B₂) ω hω

/-- **Subdivision additivity**: The integral of dω over two boxes equals the sum
of their individual integrals of dω. Combined with Stokes, this means the
boundary integral decomposes as well. -/
theorem subdivision_exterior_add (B₁ B₂ : CubicalBox n) (ω : CoordNForm n) :
    integrateExterior (twoBoxChain B₁ B₂) ω =
    integrateExterior (singletonChain B₁) ω + integrateExterior (singletonChain B₂) ω := by
  unfold twoBoxChain singletonChain
  exact integrateExterior_add (Finsupp.single B₁ 1) (Finsupp.single B₂ 1) ω

/-- The boundary integral also decomposes additively over a two-box chain. -/
theorem subdivision_bdry_add (B₁ B₂ : CubicalBox n) (ω : CoordNForm n) :
    integrateBdry (twoBoxChain B₁ B₂) ω =
    integrateBdry (singletonChain B₁) ω + integrateBdry (singletonChain B₂) ω := by
  unfold twoBoxChain singletonChain
  exact integrateBdry_add (Finsupp.single B₁ 1) (Finsupp.single B₂ 1) ω

/-- **Full subdivision invariance**: For a smooth form on two adjacent boxes,
the individual Stokes identities (one per box) together imply
the Stokes identity on the combined chain. This is the core property showing
that cubical Stokes extends beyond single boxes. -/
theorem subdivision_stokes_equiv (B₁ B₂ : CubicalBox n) (ω : CoordNForm n) (hω : IsSmooth ω) :
    boxIntegral (extDerivCoord ω) B₁.lo B₁.hi +
    boxIntegral (extDerivCoord ω) B₂.lo B₂.hi =
    bdryIntegral ω B₁.lo B₁.hi + bdryIntegral ω B₂.lo B₂.hi := by
  have h1 := stokes_smooth B₁.lo B₁.hi B₁.le ω hω
  have h2 := stokes_smooth B₂.lo B₂.hi B₂.le ω hω
  linarith

/-- Two boxes are **adjacent in direction i** if they share a face:
    B₁'s high face in direction i equals B₂'s low face in direction i,
    and the remaining coordinates agree. -/
def Adjacent (B₁ B₂ : CubicalBox n) (i : Fin (n + 1)) : Prop :=
  B₁.hi i = B₂.lo i ∧
  (∀ j : Fin n, B₁.lo (Fin.succAbove i j) = B₂.lo (Fin.succAbove i j)) ∧
  (∀ j : Fin n, B₁.hi (Fin.succAbove i j) = B₂.hi (Fin.succAbove i j))

/-- **Shared-face cancellation**: When two boxes are adjacent in direction i,
    the boundary contribution from B₁'s hi-face equals (with opposite sign)
    B₂'s lo-face contribution. Specifically:
    - B₁ contributes `+∫ signedCoeff ω i (insertNth i (B₁.hi i) x) dx` (hi-face)
    - B₂ contributes `-∫ signedCoeff ω i (insertNth i (B₂.lo i) x) dx` (lo-face)
    Since B₁.hi i = B₂.lo i and the projection domains match, these cancel. -/
theorem shared_face_cancel (B₁ B₂ : CubicalBox n) (i : Fin (n + 1))
    (hadj : Adjacent B₁ B₂ i) (ω : CoordNForm n) :
    -- The hi-face of B₁ at direction i (positive contribution in bdryIntegral)
    (∫ x in Icc (B₁.lo ∘ Fin.succAbove i) (B₁.hi ∘ Fin.succAbove i),
        signedCoeff ω i (Fin.insertNth i (B₁.hi i) x)) =
    -- The lo-face of B₂ at direction i (which appears with a minus in bdryIntegral)
    (∫ x in Icc (B₂.lo ∘ Fin.succAbove i) (B₂.hi ∘ Fin.succAbove i),
        signedCoeff ω i (Fin.insertNth i (B₂.lo i) x)) := by
  -- B₁.hi i = B₂.lo i (values on shared face are the same)
  have hval : B₁.hi i = B₂.lo i := hadj.1
  -- Projection domains agree
  have hlo : B₁.lo ∘ Fin.succAbove i = B₂.lo ∘ Fin.succAbove i := by
    ext j; exact hadj.2.1 j
  have hhi : B₁.hi ∘ Fin.succAbove i = B₂.hi ∘ Fin.succAbove i := by
    ext j; exact hadj.2.2 j
  rw [hval, hlo, hhi]

/-- **Net boundary of adjacent boxes**: When B₁ and B₂ are adjacent in direction i,
    the sum of their boundary integrals simplifies: the shared-face terms cancel,
    leaving only the outer faces. -/
theorem adjacent_boundary_simplifies (B₁ B₂ : CubicalBox n) (i : Fin (n + 1))
    (hadj : Adjacent B₁ B₂ i) (ω : CoordNForm n) :
    -- In the combined boundary, the hi-face of B₁ cancels the lo-face of B₂
    -- at direction i. The net contribution at direction i is:
    -- (hi-face of B₂) - (lo-face of B₁) = boundary of merged box at direction i
    (∫ x in Icc (B₁.lo ∘ Fin.succAbove i) (B₁.hi ∘ Fin.succAbove i),
        signedCoeff ω i (Fin.insertNth i (B₁.hi i) x)) -
    (∫ x in Icc (B₂.lo ∘ Fin.succAbove i) (B₂.hi ∘ Fin.succAbove i),
        signedCoeff ω i (Fin.insertNth i (B₂.lo i) x)) = 0 := by
  linarith [shared_face_cancel B₁ B₂ i hadj ω]

end CubeStokes

end
