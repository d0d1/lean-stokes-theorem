/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoxControlledStokes

/-!
# Axiom verification for the box-controlled domain Stokes layer

Verifies that the domain-layer definitions and theorems for compact regular
sublevel domains depend only on standard Lean/mathlib axioms: `propext`,
`Classical.choice`, and `Quot.sound`.
-/

namespace SmoothDomain

section DomainIntegrals

#print axioms domainIntegral
#print axioms boundaryIntegral
#print axioms chosenBoxControlledPartition
#print axioms chosenBoxControlledPartition_subordinate
#print axioms boxControlledBoundaryIntegral

end DomainIntegrals

section BoxControlledStokes

#print axioms boxControlledBoundaryIntegral_eq_of_contDiff
#print axioms boundaryIntegral_eq_boxControlledBoundaryIntegral_of_contDiff
#print axioms finite_boxControlled_localized_stokes_of_smoothPartition
#print axioms exists_boxControlledBoundaryIntegral_stokes
#print axioms BoxControlledStokesData.of_contDiff
#print axioms stokes_boundaryIntegral

end BoxControlledStokes

end SmoothDomain
