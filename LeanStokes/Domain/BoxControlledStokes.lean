/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoxControlledCover

/-!
# Box-Controlled Global Stokes Assembly

This module packages the existing box-controlled cover existence theorem with
finite localized Stokes assembly.  The boundary side remains a
partition-dependent box-controlled boundary sum: this file proves no
independence of the chosen partition, no chart-independence, and not the final
canonical compact-domain Stokes theorem.
-/

noncomputable section

open Set
open scoped Topology Manifold

namespace SmoothDomain

variable {n : ℕ}

/-- Noncanonical proof data for the box-controlled global Stokes assembly.

The boundary side is the partition-dependent box-controlled boundary sum
`M.boxControlledBoundaryIntegral ρ subordinate ω`.  This structure records no
independence of `ρ`, no chart-independence, and is not the final canonical
compact-domain Stokes theorem. -/
structure BoxControlledStokesData (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) where
  /-- Smooth partition subordinate to the complement-extended box-controlled carrier cover. -/
  ρ : SmoothPartitionOfUnity
    (Option (BoxControlledCoverIndex M)) (𝓘(ℝ, ℝSpace (n + 1)))
    (ℝSpace (n + 1)) univ
  /-- Subordination of `ρ` to the box-controlled cover with complement. -/
  subordinate : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover)
  /-- Stokes equality for this partition-dependent box-controlled boundary sum. -/
  stokes :
    M.domainIntegral (DiffForm.extd ω) =
      M.boxControlledBoundaryIntegral ρ subordinate ω

namespace BoxControlledStokesData

/-- Choose noncanonical box-controlled Stokes data for a smooth form.

The chosen boundary side is still partition-dependent and box-controlled; this
does not assert independence of choices or define the final boundary integral. -/
noncomputable def of_contDiff (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    BoxControlledStokesData M ω := by
  let ρ := Classical.choose M.exists_smoothPartition_subordinate_ambientBoxControlledCover
  let hρ := Classical.choose_spec M.exists_smoothPartition_subordinate_ambientBoxControlledCover
  exact ⟨ρ, hρ, M.finite_boxControlled_localized_stokes_of_smoothPartition ρ hρ hω⟩

end BoxControlledStokesData

/-- Existence of a noncanonical box-controlled boundary sum satisfying Stokes.

This packages global box-controlled cover existence with finite localized
assembly.  The boundary integral here is still partition-dependent and
box-controlled; this theorem does not prove chart/partition independence and is
not the final canonical compact-domain Stokes theorem. -/
theorem exists_boxControlledBoundaryIntegral_stokes
    (M : SmoothDomain (n + 1)) (ω : DiffForm (n + 1) n)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    ∃ ρ : SmoothPartitionOfUnity
        (Option (BoxControlledCoverIndex M)) (𝓘(ℝ, ℝSpace (n + 1)))
        (ℝSpace (n + 1)) univ,
      ∃ hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover),
        M.domainIntegral (DiffForm.extd ω) =
          M.boxControlledBoundaryIntegral ρ hρ ω := by
  rcases M.exists_smoothPartition_subordinate_ambientBoxControlledCover with ⟨ρ, hρ⟩
  exact ⟨ρ, hρ, M.finite_boxControlled_localized_stokes_of_smoothPartition ρ hρ hω⟩

end SmoothDomain

end
