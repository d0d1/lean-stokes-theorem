/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.Domain.SmoothDomain
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Smooth Partitions of Unity for Smooth Domains

This module contains domain-level smooth partition infrastructure used by
localized Stokes assembly.  The key point is that exterior derivative locality is
ambient: partitions used for `dω` over a carrier must sum to one in ambient
neighborhoods of carrier points, not merely relative neighborhoods.
-/

noncomputable section

open Set
open scoped BigOperators Topology Manifold ContDiff

/-- If the topological support of a function is contained in `U`, then the function is eventually
zero near any point outside `U`. -/
theorem eventuallyEq_zero_of_tsupport_subset_of_notMem
    {X α : Type*} [TopologicalSpace X] [Zero α]
    {f : X → α} {U : Set X} {x : X}
    (hsub : tsupport f ⊆ U) (hx : x ∉ U) :
    f =ᶠ[𝓝 x] fun _ => 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun hxt => hx (hsub hxt))

/-- If the topological support of a function lies in a set disjoint from `S`, then the raw support
is disjoint from `S`. -/
theorem disjoint_support_left_of_tsupport_subset
    {X α : Type*} [TopologicalSpace X] [Zero α]
    {f : X → α} {U S : Set X}
    (hsub : tsupport f ⊆ U) (hdisj : Disjoint U S) :
    Disjoint (Function.support f) S :=
  hdisj.mono_left ((subset_tsupport f).trans hsub)

namespace SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M} {U : ι → Set M}
  {ρ : SmoothPartitionOfUnity ι I M s}

/-- A member of a Euclidean smooth partition of unity is a `C^∞` scalar function. -/
theorem contDiff_apply_infty {d : ℕ} {s : Set (ℝSpace d)}
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace d)) (ℝSpace d) s) (i : ι) :
    ContDiff ℝ ∞ (fun z => ρ i z) :=
  by
    change ContDiff ℝ ∞ ⇑(ρ i)
    exact (ρ i).contMDiff.contDiff

/-- A partition element subordinate to `U i` is eventually zero near points outside `U i`. -/
theorem IsSubordinate.eventuallyEq_zero_of_notMem
    (hρU : ρ.IsSubordinate U) {i : ι} {x : M} (hx : x ∉ U i) :
    (fun z => ρ i z) =ᶠ[𝓝 x] fun _ => 0 :=
  eventuallyEq_zero_of_tsupport_subset_of_notMem (f := fun z => ρ i z) (hρU i) hx

/-- A partition element subordinate to `U i` has raw support disjoint from any set disjoint from
`U i`. -/
theorem IsSubordinate.disjoint_support
    (hρU : ρ.IsSubordinate U) {i : ι} {S : Set M} (hdisj : Disjoint (U i) S) :
    Disjoint (Function.support (fun z => ρ i z)) S :=
  disjoint_support_left_of_tsupport_subset (f := fun z => ρ i z) (hρU i) hdisj

end SmoothPartitionOfUnity

namespace SmoothDomain

variable {d : ℕ}

section SmoothPartition

variable {ι : Type*} (M : SmoothDomain d)

/-- Indices whose topological support meets the compact carrier.

This is the finite active set used to turn a locally finite ambient smooth partition of unity into
the finite local partition hypothesis required by localized Stokes assembly.  The use of
`tsupport`, rather than raw support, is essential near boundary points of the carrier. -/
def compactActiveFinset
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ) : Finset ι :=
  (ρ.toPartitionOfUnity.locallyFinite_tsupport.finite_nonempty_inter_compact
    M.carrier_isCompact).toFinset

@[simp]
theorem mem_compactActiveFinset
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ) {i : ι} :
    i ∈ M.compactActiveFinset ρ ↔ (tsupport (ρ i) ∩ M.carrier).Nonempty := by
  simp [compactActiveFinset]

/-- At a carrier point, every index in the pointwise topological support is globally active. -/
theorem fintsupport_subset_compactActiveFinset
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ)
    {y : ℝSpace d} (hy : y ∈ M.carrier) :
    ρ.fintsupport y ⊆ M.compactActiveFinset ρ := by
  intro i hi
  rw [mem_compactActiveFinset]
  rw [ρ.mem_fintsupport_iff] at hi
  exact ⟨y, hi, hy⟩

/-- Near a carrier point, the pointwise support of an ambient smooth partition is contained in the
compact active set. -/
theorem eventually_finsupport_subset_compactActiveFinset
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ)
    {y : ℝSpace d} (hy : y ∈ M.carrier) :
    ∀ᶠ z in 𝓝 y, ρ.finsupport z ⊆ M.compactActiveFinset ρ :=
  (ρ.eventually_finsupport_subset y).mono fun _ hz =>
    hz.trans (M.fintsupport_subset_compactActiveFinset ρ hy)

/-- A globally defined ambient smooth partition of unity has a finite subfamily whose scalar sum is
equal to one in an ambient neighborhood of every carrier point. -/
theorem smoothPartition_compactActive_eventuallyEq_one
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ)
    {y : ℝSpace d} (hy : y ∈ M.carrier) :
    (fun z => ∑ i ∈ M.compactActiveFinset ρ, ρ i z) =ᶠ[𝓝 y] fun _ => 1 := by
  filter_upwards [M.eventually_finsupport_subset_compactActiveFinset ρ hy] with z hz
  simpa using (ρ.sum_finsupport' z (show z ∈ (univ : Set (ℝSpace d)) by simp) hz)

end SmoothPartition

section AmbientCover

variable {ι : Type*} (M : SmoothDomain d)

/-- Add the carrier complement to an open cover of the carrier, producing an ambient open cover of
the whole Euclidean space. -/
def ambientCoverWithComplement (U : ι → Set (ℝSpace d)) : Option ι → Set (ℝSpace d)
  | none => M.carrierᶜ
  | some i => U i

@[simp]
theorem ambientCoverWithComplement_none (U : ι → Set (ℝSpace d)) :
    M.ambientCoverWithComplement U none = M.carrierᶜ :=
  rfl

@[simp]
theorem ambientCoverWithComplement_some (U : ι → Set (ℝSpace d)) (i : ι) :
    M.ambientCoverWithComplement U (some i) = U i :=
  rfl

/-- The ambient cover with complement is open when the original carrier cover is open. -/
theorem isOpen_ambientCoverWithComplement {U : ι → Set (ℝSpace d)}
    (hUo : ∀ i, IsOpen (U i)) :
    ∀ j, IsOpen (M.ambientCoverWithComplement U j) := by
  intro j
  cases j with
  | none =>
      simpa [ambientCoverWithComplement] using M.isClosed_carrier.isOpen_compl
  | some i =>
      simpa [ambientCoverWithComplement] using hUo i

/-- If `U` covers the carrier, then adding the carrier complement covers the ambient space. -/
theorem univ_subset_iUnion_ambientCoverWithComplement {U : ι → Set (ℝSpace d)}
    (hU : M.carrier ⊆ ⋃ i, U i) :
    (univ : Set (ℝSpace d)) ⊆ ⋃ j, M.ambientCoverWithComplement U j := by
  intro x _
  by_cases hx : x ∈ M.carrier
  · rcases mem_iUnion.mp (hU hx) with ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨some i, by simpa [ambientCoverWithComplement] using hi⟩
  · exact mem_iUnion.mpr ⟨none, by simpa [ambientCoverWithComplement] using hx⟩

/-- A carrier open cover induces a global ambient smooth partition of unity subordinate to the cover
plus the carrier complement. -/
theorem exists_smoothPartition_subordinate_ambientCoverWithComplement
    (U : ι → Set (ℝSpace d)) (hUo : ∀ i, IsOpen (U i))
    (hU : M.carrier ⊆ ⋃ i, U i) :
    ∃ ρ : SmoothPartitionOfUnity (Option ι) (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ,
      ρ.IsSubordinate (M.ambientCoverWithComplement U) :=
  SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝSpace d))
    isClosed_univ (M.ambientCoverWithComplement U)
    (M.isOpen_ambientCoverWithComplement hUo)
    (M.univ_subset_iUnion_ambientCoverWithComplement hU)

/-- The carrier-complement partition index is inactive over the carrier for any subordinate ambient
partition. -/
theorem none_notMem_compactActiveFinset_of_isSubordinate {U : ι → Set (ℝSpace d)}
    (ρ : SmoothPartitionOfUnity (Option ι) (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ)
    (hρU : ρ.IsSubordinate (M.ambientCoverWithComplement U)) :
    none ∉ M.compactActiveFinset ρ := by
  intro hnone
  rw [mem_compactActiveFinset] at hnone
  rcases hnone with ⟨x, hx_support, hx_carrier⟩
  exact (hρU none hx_support) hx_carrier

/-- Every active index of a partition subordinate to the complement-extended cover comes from the
original carrier cover. -/
theorem exists_some_of_mem_compactActiveFinset_of_isSubordinate {U : ι → Set (ℝSpace d)}
    (ρ : SmoothPartitionOfUnity (Option ι) (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ)
    (hρU : ρ.IsSubordinate (M.ambientCoverWithComplement U))
    {j : Option ι} (hj : j ∈ M.compactActiveFinset ρ) :
    ∃ i, j = some i := by
  cases j with
  | none =>
      exact False.elim ((M.none_notMem_compactActiveFinset_of_isSubordinate ρ hρU) hj)
  | some i =>
      exact ⟨i, rfl⟩

/-- An active complement-extended-cover index has topological support inside its original carrier
cover member. -/
theorem tsupport_subset_cover_of_mem_compactActiveFinset_of_isSubordinate
    {U : ι → Set (ℝSpace d)}
    (ρ : SmoothPartitionOfUnity (Option ι) (𝓘(ℝ, ℝSpace d)) (ℝSpace d) univ)
    (hρU : ρ.IsSubordinate (M.ambientCoverWithComplement U))
    {j : Option ι} (hj : j ∈ M.compactActiveFinset ρ) :
    ∃ i, j = some i ∧ tsupport (ρ j) ⊆ U i := by
  rcases M.exists_some_of_mem_compactActiveFinset_of_isSubordinate ρ hρU hj with ⟨i, rfl⟩
  exact ⟨i, rfl, by simpa [ambientCoverWithComplement] using hρU (some i)⟩

end AmbientCover

end SmoothDomain

end
