/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.CubeStokes.Unified
import LeanStokes.CubeStokes.Smooth
import LeanStokes.CubeStokes.Classical
import LeanStokes.CubeStokes.FTC
import LeanStokes.CubeStokes.Chains
import LeanStokes.CubeStokes.Green
import LeanStokes.CubeStokes.Divergence
import LeanStokes.CubeStokes.Properties
import LeanStokes.CubeStokes.IBP
import LeanStokes.CubeStokes.Validation
import LeanStokes.CubeStokes.BdryOp
import LeanStokes.CubeStokes.Leibniz
import LeanStokes.CubeStokes.Examples
import LeanStokes.CubeStokes.Gauss3D
import LeanStokes.CubeStokes.DDZero
import LeanStokes.CubeStokes.Subdivision
import LeanStokes.CubeStokes.Naturality
import LeanStokes.CubeStokes.BoundaryChain

/-!
# Axiom verification for Cubical Stokes

Verifies that all sorry-free theorems depend only on standard Lean/mathlib axioms:
`propext`, `Classical.choice`, `Quot.sound`.

This file serves as a complete audit of the formalization's logical foundations.
-/

section CoreTheorems
-- Core Stokes theorem
#print axioms CubeStokes.stokes_on_box
#print axioms CubeStokes.stokes_contDiffAt_box
#print axioms CubeStokes.stokes_smooth
end CoreTheorems

section BridgeTheorems
-- Bridge to mathlib extDeriv
#print axioms CubeStokes.extDeriv_topCoeff_eq_extDerivCoord
#print axioms CubeStokes.stokes_extDeriv
#print axioms CubeStokes.stokes_extDeriv_smooth
#print axioms CubeStokes.toCoordNForm_smooth
end BridgeTheorems

section ClassicalCorollaries
-- Classical vector calculus theorems
#print axioms CubeStokes.green_on_rectangle
#print axioms CubeStokes.divergence_on_box_3d
#print axioms CubeStokes.green_stokes
#print axioms CubeStokes.green_four_edges
#print axioms CubeStokes.divergence_stokes
end ClassicalCorollaries

section FTCTheorems
-- Fundamental Theorem of Calculus
#print axioms CubeStokes.ftc_stokes
#print axioms CubeStokes.bdryIntegral_fin1
#print axioms CubeStokes.extDerivCoord_of_comp_proj
end FTCTheorems

section ValidationTheorems
-- Independent non-circular validation
#print axioms CubeStokes.ftc_intervalIntegral
#print axioms CubeStokes.stokes_lhs_eq_intervalIntegral
#print axioms CubeStokes.ftc_paths_agree
end ValidationTheorems

section ChainTheorems
-- Cubical chains
#print axioms CubeStokes.stokes_chain
#print axioms CubeStokes.stokes_single
#print axioms CubeStokes.integrateExterior_add
#print axioms CubeStokes.integrateBdry_add
end ChainTheorems

section AlgebraicProperties
-- Linearity of exterior derivative and integration
#print axioms CubeStokes.extDerivCoord_add
#print axioms CubeStokes.extDerivCoord_smul
#print axioms CubeStokes.extDerivCoord_neg
#print axioms CubeStokes.extDerivCoord_zero
#print axioms CubeStokes.bdryIntegral_zero
#print axioms CubeStokes.stokes_smooth_add
#print axioms CubeStokes.stokes_smooth_smul
#print axioms CubeStokes.boxIntegral_smul
end AlgebraicProperties

section IBPTheorems
-- Integration by parts
#print axioms CubeStokes.integration_by_parts
end IBPTheorems

section BdryOpTheorems
-- Boundary operator ∂² = 0
#print axioms CubeStokes.neg_one_pow_add_of_parity_ne
#print axioms CubeStokes.bdry_sq_sign_cancel
#print axioms CubeStokes.succAbove_predAbove_neg_one_pow
#print axioms CubeStokes.bdry_sq_geometric
end BdryOpTheorems

section FaceTheorems
-- Face geometry
#print axioms CubeStokes.faceBox_faceBox_lo
#print axioms CubeStokes.faceBox_faceBox_hi
#print axioms CubeStokes.faceBox_Icc
end FaceTheorems

section LeibnizTheorems
-- Leibniz / product rule for exterior derivative
#print axioms CubeStokes.extDerivCoord_scalarMul
#print axioms CubeStokes.extDerivCoord_scalarMul_split
end LeibnizTheorems

section ExampleTheorems
-- Concrete computations
#print axioms CubeStokes.extDerivCoord_const_zero
#print axioms CubeStokes.stokes_constant_form
#print axioms CubeStokes.extDerivCoord_coordForm1d
#print axioms CubeStokes.stokes_coordForm1d
end ExampleTheorems

section Gauss3DTheorems
-- 3D Gauss divergence theorem
#print axioms CubeStokes.div3_eq
#print axioms CubeStokes.gauss_3d
end Gauss3DTheorems

section DDZeroTheorems
-- d² = 0 (nilpotency of exterior derivative)
#print axioms CubeStokes.dd_zero_abstract
#print axioms CubeStokes.dd_zero_coord_top
#print axioms CubeStokes.stokes_dd_zero
end DDZeroTheorems

section SubdivisionTheorems
-- Subdivision invariance
#print axioms CubeStokes.stokes_two_boxes
#print axioms CubeStokes.subdivision_exterior_add
#print axioms CubeStokes.subdivision_bdry_add
#print axioms CubeStokes.subdivision_stokes_equiv
#print axioms CubeStokes.shared_face_cancel
#print axioms CubeStokes.adjacent_boundary_simplifies
end SubdivisionTheorems

section NaturalityTheorems
-- Pullback / naturality
#print axioms CubeStokes.pullback_smooth
#print axioms CubeStokes.stokes_pullback
#print axioms CubeStokes.pullback_comp
#print axioms CubeStokes.pullback_id
#print axioms CubeStokes.pullback_add
#print axioms CubeStokes.pullback_smul
end NaturalityTheorems

-- Boundary chain operator (∂² = 0)
section BoundaryChainTheorems
#print axioms CubeStokes.double_boundary_cancels
#print axioms CubeStokes.double_boundary_same_face
#print axioms CubeStokes.bdry_sq_zero_combined
#print axioms CubeStokes.boundary_squared_zero
#print axioms CubeStokes.double_boundary_sign_neg
end BoundaryChainTheorems
