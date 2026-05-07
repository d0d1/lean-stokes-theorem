/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.SingularCubeStokes.Theorem
import LeanStokes.SingularCubeStokes.Chain
import LeanStokes.SingularCubeStokes.BdryBdry

/-!
# Axiom verification for Singular Cubical Stokes

Verifies that all sorry-free singular Stokes theorems depend only on standard
Lean/mathlib axioms: `propext`, `Classical.choice`, `Quot.sound`.

This extends the box Stokes axiom audit (CubeStokes.Check) to cover the
singular cubical layer.
-/

namespace SingularCubeStokes

-- Main singular Stokes theorem
#print axioms singularStokes
#print axioms singularStokes_abstract

-- Chain-level theorems
#print axioms stokes_singular_boundary
#print axioms stokes_singular_chain
#print axioms stokes_chain

-- Boundary operator
#print axioms singularBoundarySingle
#print axioms singularBoundary

-- ∂²=0
#print axioms bdry_bdry_chain_zero
#print axioms bdry_bdry_chain_zero_general

-- Integration
#print axioms integrateChain
#print axioms integrateForm

-- Pullback and face matching
#print axioms pullbackForm
#print axioms singularFace
#print axioms face_matching

end SingularCubeStokes
