/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.BoxControlledCover

/-!
# Box-Controlled Global Stokes Assembly

This module packages the existing box-controlled cover existence theorem with
finite localized Stokes assembly.  It first exposes noncanonical proof data,
then proves smooth-form independence inside the box-controlled construction and
defines `SmoothDomain.boundaryIntegral` as a fixed chosen box-controlled
boundary sum.  This is not a separate manifold-integration API and does not
claim chart-independence outside the box-controlled construction.
-/

noncomputable section

open Set
open scoped Topology Manifold

namespace SmoothDomain

variable {n : ℕ}

/-- Smooth partitions used by the box-controlled global Stokes assembly. -/
abbrev BoxControlledPartition (M : SmoothDomain (n + 1)) :=
  SmoothPartitionOfUnity (Option (BoxControlledCoverIndex M))
    (𝓘(ℝ, ℝSpace (n + 1))) (ℝSpace (n + 1)) univ

/-- Noncanonical proof data for the box-controlled global Stokes assembly.

The boundary side is the partition-dependent box-controlled boundary sum
`M.boxControlledBoundaryIntegral ρ subordinate ω`.  This structure records no
independence of `ρ`, no chart-independence, and is not the final canonical
compact-domain Stokes theorem. -/
structure BoxControlledStokesData (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) where
  /-- Smooth partition subordinate to the complement-extended box-controlled carrier cover. -/
  ρ : BoxControlledPartition M
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
    ∃ ρ : BoxControlledPartition M,
      ∃ hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover),
        M.domainIntegral (DiffForm.extd ω) =
          M.boxControlledBoundaryIntegral ρ hρ ω := by
  rcases M.exists_smoothPartition_subordinate_ambientBoxControlledCover with ⟨ρ, hρ⟩
  exact ⟨ρ, hρ, M.finite_boxControlled_localized_stokes_of_smoothPartition ρ hρ hω⟩

/-- Any two subordinate box-controlled boundary sums agree for a smooth form.

This is independence inside the box-controlled construction, proved from the
already established box-controlled Stokes theorem; it is not a separate
chart-transition proof for an arbitrary manifold-integration API. -/
theorem boxControlledBoundaryIntegral_eq_of_contDiff
    (M : SmoothDomain (n + 1)) (ω : DiffForm (n + 1) n)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (ρ σ : BoxControlledPartition M)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover))
    (hσ : σ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover)) :
    M.boxControlledBoundaryIntegral ρ hρ ω =
      M.boxControlledBoundaryIntegral σ hσ ω := by
  exact (M.finite_boxControlled_localized_stokes_of_smoothPartition ρ hρ hω).symm.trans
    (M.finite_boxControlled_localized_stokes_of_smoothPartition σ hσ hω)

/-- A fixed chosen smooth partition subordinate to the box-controlled carrier cover. -/
noncomputable def chosenBoxControlledPartition (M : SmoothDomain (n + 1)) :
    BoxControlledPartition M :=
  Classical.choose M.exists_smoothPartition_subordinate_ambientBoxControlledCover

/-- The chosen box-controlled partition is subordinate to the complement-extended cover. -/
theorem chosenBoxControlledPartition_subordinate (M : SmoothDomain (n + 1)) :
    (chosenBoxControlledPartition M).IsSubordinate
      (M.ambientCoverWithComplement M.boxControlledCarrierCover) := by
  simpa [chosenBoxControlledPartition] using
    Classical.choose_spec M.exists_smoothPartition_subordinate_ambientBoxControlledCover

/-- Boundary integral over a smooth regular sublevel-domain boundary, implemented as a fixed
chosen box-controlled boundary sum.

For smooth forms, `boundaryIntegral_eq_boxControlledBoundaryIntegral_of_contDiff`
shows this chosen value agrees with every subordinate box-controlled boundary
sum.  This definition is not a separate manifold-integration API outside the
box-controlled construction. -/
noncomputable def boundaryIntegral (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) : ℝ :=
  M.boxControlledBoundaryIntegral (chosenBoxControlledPartition M)
    (chosenBoxControlledPartition_subordinate M) ω

/-- The chosen boundary integral agrees with any subordinate box-controlled boundary sum for smooth
forms. -/
theorem boundaryIntegral_eq_boxControlledBoundaryIntegral_of_contDiff
    (M : SmoothDomain (n + 1)) (ω : DiffForm (n + 1) n)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    (ρ : BoxControlledPartition M)
    (hρ : ρ.IsSubordinate (M.ambientCoverWithComplement M.boxControlledCarrierCover)) :
    M.boundaryIntegral ω =
      M.boxControlledBoundaryIntegral ρ hρ ω :=
  M.boxControlledBoundaryIntegral_eq_of_contDiff ω hω
    (chosenBoxControlledPartition M) ρ (chosenBoxControlledPartition_subordinate M) hρ

/-- Stokes' theorem for the chosen box-controlled boundary integral.

The boundary integral in this statement is `SmoothDomain.boundaryIntegral`, a
fixed chosen box-controlled boundary sum whose smooth-form independence inside
the box-controlled construction is proved above. -/
theorem stokes_boundaryIntegral (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n) (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    M.domainIntegral (DiffForm.extd ω) = M.boundaryIntegral ω :=
  M.finite_boxControlled_localized_stokes_of_smoothPartition
    (chosenBoxControlledPartition M) (chosenBoxControlledPartition_subordinate M) hω

end SmoothDomain

end
