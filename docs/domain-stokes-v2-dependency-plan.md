# Domain Stokes v2 dependency plan

This document records the dependency plan for a sorry-free Lean 4/mathlib proof of
Stokes' theorem for compact regular sublevel domains in Euclidean space.  It is a
technical plan for the Lean artifact, not a theorem statement substitution.

The target domain is a compact regular sublevel set

```lean
M.carrier = {x : Fin d → ℝ | M.φ x ≤ 0}
M.boundary = {x : Fin d → ℝ | M.φ x = 0}
```

where `M.φ` is smooth and `fderiv ℝ M.φ x ≠ 0` on the boundary.

## Current status

The theorem layer now contains a box-controlled compact regular sublevel-domain
Stokes theorem:

```lean
theorem SmoothDomain.stokes_boundaryIntegral
    (M : SmoothDomain (n + 1))
    (ω : DiffForm (n + 1) n)
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    M.domainIntegral (DiffForm.extd ω) = M.boundaryIntegral ω
```

`M.boundaryIntegral ω` is currently the chosen box-controlled boundary sum from
`LeanStokes.Domain.BoxControlledStokes`.  For smooth forms it agrees with every
subordinate box-controlled boundary sum, as proved by
`SmoothDomain.boundaryIntegral_eq_boxControlledBoundaryIntegral_of_contDiff`.
This discharges the local support, cover, partition, and integrability
hypotheses from the exported box-controlled theorem statement.

This status does not mark the stronger manifold-style integration desiderata
below as complete: no separate general manifold-with-boundary integration API is
claimed, and chart-independence outside the box-controlled Euclidean
construction remains future infrastructure.

## Intended final theorem schema

The intended exported theorem has the following shape, with names to be fixed by
implementation:

```lean
theorem smoothDomain_stokes
    {d : ℕ} [NeZero d]
    (M : SmoothDomain d)
    (ω : DiffForm d (d - 1))
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) :
    DiffForm.integral (DiffForm.extd ω) M.carrier =
      M.boundaryIntegral ω
```

If intermediate development requires support, chart, or integrability hypotheses,
those hypotheses belong to local/intermediate lemmas.  The compact-domain theorem
is complete only after those hypotheses have been discharged from the final
globally smooth compact-domain statement.
The final Lean statement may include explicit degree casts witnessing
`(d - 1) + 1 = d` under `[NeZero d]`; those casts are implementation details, not
extra mathematical assumptions.

Dimension `d = 0` is not part of the boundary theorem above; the main theorem will
use `[NeZero d]`.  A separate zero-dimensional convention may be added only if it
simplifies APIs without weakening the positive-dimensional theorem.

## Available dependencies

### Differential forms

`Mathlib.Analysis.Calculus.DifferentialForm.Basic` provides unbundled
differential forms on normed spaces:

```lean
E → E [⋀^Fin n]→L[𝕜] F
```

Important available API:

* `extDeriv`, `extDerivWithin`;
* `extDeriv_add`, `extDerivWithin_add`;
* `extDeriv_smul`, `extDerivWithin_smul` for constant scalar multiples;
* `extDeriv_apply`, `extDerivWithin_apply`;
* `extDeriv_extDeriv`, `extDerivWithin_extDerivWithin_eqOn`;
* `extDeriv_pullback`, `extDerivWithin_pullback`.

The same file explicitly records that bundled smooth forms and manifold forms are
not yet defined in mathlib.  The v2 proof must therefore stay in a Euclidean
specialization, or build the missing Euclidean layer in this repository; it must
not rely on nonexistent manifold form integration.

### Measure and change of variables

`Mathlib.MeasureTheory.Function.Jacobian` provides scalar Lebesgue
change-of-variables for finite-dimensional real normed spaces:

* `lintegral_image_eq_lintegral_abs_det_fderiv_mul`;
* `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`;
* `integral_image_eq_integral_abs_det_fderiv_smul`;
* `integral_target_eq_integral_abs_det_fderiv_smul` for
  `OpenPartialHomeomorph`.

These theorems use `abs (det _)`.  They are a foundation for chart
independence, but they are not the oriented differential-form change-of-variables
theorem.  The project must build the signed top-form layer that relates pullback
coefficients to determinants and then uses the scalar API under
orientation-preserving or orientation-reversing hypotheses.

`Mathlib.MeasureTheory.Function.LocallyIntegrable` provides compact
integrability tools, including:

* `ContinuousOn.integrableOn_compact`;
* `Continuous.integrable_of_hasCompactSupport`.

### Local flattening

`Mathlib.Analysis.Calculus.Implicit` provides implicit-function and local
partial-homeomorphism infrastructure.  The relevant API includes:

* `ImplicitFunctionData`;
* `HasStrictFDerivAt.implicitFunctionDataOfComplemented`;
* `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`;
* `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_fst`;
* `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply`;
* source/target membership lemmas for the resulting `OpenPartialHomeomorph`.

For a boundary point, regularity of `M.φ` must be upgraded to the hypotheses of
this API: a strict derivative at the point, surjectivity of the derivative
`fderiv ℝ M.φ x : E →L[ℝ] ℝ`, and a complemented kernel.  In finite
dimension the kernel complement should be available, but the exact bridge lemmas
must be proved or located.

### Partitions of unity and bump functions

`Mathlib.Geometry.Manifold.PartitionOfUnity` provides smooth scalar partitions of
unity on finite-dimensional real manifolds:

* `SmoothBumpCovering.exists_isSubordinate`;
* `SmoothBumpCovering.toSmoothPartitionOfUnity`;
* `SmoothPartitionOfUnity.exists_isSubordinate`;
* `SmoothPartitionOfUnity.IsSubordinate`;
* `SmoothPartitionOfUnity.sum_eq_one`;
* `SmoothPartitionOfUnity.contMDiff_finsum_smul`;
* local finite-support API such as `finsupport`, `fintsupport`, and
  `finite_tsupport`.

`Mathlib.Geometry.Manifold.BumpFunction` provides `SmoothBumpFunction` with
support and compact-support control:

* `SmoothBumpFunction.nhds_basis_support`;
* `SmoothBumpFunction.nhds_basis_tsupport`;
* `SmoothBumpFunction.hasCompactSupport`;
* `SmoothBumpFunction.contMDiff`;
* `SmoothBumpFunction.contMDiff_smul`.

The proof may use this Euclidean instance of the manifold API for scalar bump
functions.  The mathlib partition-of-unity file explicitly does not provide
integration of differential forms over manifolds, so only scalar bump functions
and finite/local-finite algebra are reusable.

### Compactness and finite subcovers

`Mathlib.Topology.Compactness.Compact` provides:

* `IsCompact.elim_finite_subcover`;
* `IsCompact.elim_finite_subcover_image`;
* `isCompact_iff_finite_subcover`.

These are needed to pass from local flattening charts to a finite compact-domain
cover.

### Orientation

`Mathlib.LinearAlgebra.Orientation` provides:

* `Orientation`;
* `Module.Oriented`;
* `Basis.orientation`;
* `Basis.orientation_eq_iff_det_pos`;
* `Basis.orientation_comp_linearEquiv_eq_iff_det_pos`.

The standard ambient orientation for `Fin d → ℝ` should be represented using
the standard `Pi.basisFun` basis.  Boundary orientation must be defined from the
ambient orientation by the outward-normal-first rule, not by a standalone
constant sign.

### Existing LeanStokes infrastructure

Reusable existing modules:

* `LeanStokes.DiffForm.Basic` and `LeanStokes.DiffForm.ExteriorDeriv` wrap
  mathlib forms and exterior derivative for `Fin d → ℝ`.
* `LeanStokes.Integration.FormIntegral` defines `DiffForm.topCoeff` and
  top-degree integration over measurable subsets of Euclidean space.
* `LeanStokes.Domain.SmoothDomain` already contains the regular sublevel-domain
  structure and basic carrier/boundary/interior definitions.
* `LeanStokes.CubeStokes.*` proves the existing box Stokes layer and supplies the
  best current route for local half-box Stokes.

Existing smooth singular-cube Stokes is not a dependency of the main domain
theorem unless a later proof explicitly constructs a cubical chain representing
the oriented boundary and proves equality with the chart-defined boundary
integral.  No claim of domain Stokes follows from the singular-cube result alone.

## Infrastructure to build

### 1. Domain API

Build the regular sublevel-domain API around `SmoothDomain`:

* measurability of `carrier`, `boundary`, and `int`;
* `boundary` closed and compact;
* `int = {x | M.φ x < 0}`;
* `boundary = frontier M.carrier` under regularity;
* open-neighborhood lemmas for carrier, interior, and boundary;
* top-form integrability on `M.carrier` for globally smooth forms;
* finite-subcover lemmas specialized to compact carrier and compact boundary.

### 2. Top-form integration and signed pullback

Strengthen `DiffForm.topCoeff` and `DiffForm.integral`:

* coefficient extensionality for top forms in `Fin d → ℝ`;
* continuity and integrability of `topCoeff ω` from smoothness of `ω`;
* finite additivity and finite-sum compatibility of `DiffForm.integral`;
* signed top-form pullback coefficient formula:

  ```lean
  topCoeff (pullback f η) x =
    det (fderiv ℝ f x) * topCoeff η (f x)
  ```

  in standard oriented coordinates, with the exact pullback definition matching
  mathlib's `compContinuousLinearMap`;
* oriented change-of-variables lemmas derived from the scalar absolute-Jacobian
  API under orientation-preserving and orientation-reversing hypotheses;
* analogous signed formulas in dimension `d - 1` for boundary chart domains.

### 3. Local ambient boundary flattening

Boundary-only parametrizations are insufficient.  For each `x in M.boundary`,
construct an ambient local diffeomorphism/`OpenPartialHomeomorph`

```lean
F_x : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)
```

or an equivalent product-coordinate target such that locally:

* one target coordinate is `M.φ`, or a signed positive scalar multiple of
  `M.φ`;
* `F_x '' (M.carrier ∩ U) = HalfSpace d ∩ F_x '' U`;
* `F_x '' (M.boundary ∩ U) = HalfSpaceBdry d ∩ F_x '' U`;
* `F_x` and `F_x.symm` are smooth on the relevant neighborhoods;
* the Jacobian determinant is nonzero on the localized support;
* the chosen sign records whether the flattening sends the domain to
  `{x_0 >= 0}` or `{x_0 <= 0}`.

The preferred construction is to choose a nonzero normal coordinate from
`fderiv ℝ M.φ x ≠ 0`, split the tangent kernel from a normal line, and use
`HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`.

### 4. Boundary orientation and boundary integral

Replace the current placeholder sign with a chart-aware orientation API:

* identify the outward normal vector using the Euclidean inner product/Riesz
  identification, or work covectorially and prove the equivalent tangent-basis
  orientation rule;
* define the induced boundary orientation by:

  ```text
  outward normal, followed by a positive boundary tangent basis,
  is a positive ambient basis.
  ```

* prove the half-space model reduces to the expected `(-1)^(d - 1)` boundary-face
  sign for the chosen first-coordinate convention;
* prove boundary chart transition maps are orientation-preserving with respect
  to this induced orientation;
* define `M.boundaryIntegral ω` by oriented finite local charts and scalar
  bumps;
* prove independence of chart refinements/transition choices using the signed
  boundary change-of-variables lemmas.

### 5. Localization algebra

Build the algebra needed to localize Stokes by scalar bump functions:

* scalar multiplication of forms by smooth scalar functions;
* support and compact-support behavior of `ρ • ω`;
* smoothness of localized forms;
* finite-sum compatibility for forms, exterior derivative, and integrals;
* exterior derivative product rule for scalar multiplication:

  ```lean
  d (ρ • ω) = dρ ∧ ω + ρ • dω
  ```

  with the required wedge/scalar-one-form API either found in mathlib or built
  in this project;
* proof that partition sums equal `1` on the carrier, boundary, and all local
  support regions used in the assembly;
* additivity of both domain and boundary integrals over finite localized sums.

### 6. Local half-space and half-box Stokes

The local model theorem must have precise support hypotheses.  The preferred
route is half-box Stokes reduced to the existing box theorem:

* choose an axis-aligned half-box in flattening coordinates;
* assume the localized form has compact support contained in the interior of the
  half-box except possibly the boundary face;
* prove side and top face integrals vanish because the localized pullback form is
  zero in neighborhoods of those artificial faces;
* identify the remaining face integral with the oriented boundary-chart integral;
* prove the sign agrees with the outward-normal-first convention.

A direct compact-support half-space theorem is acceptable only if it proves the
same boundary-face statement and support control without hiding artificial-face
terms.

### 7. Global assembly

Assemble the compact-domain theorem:

* finite cover of `M.carrier` by interior boxes and boundary-flattening boxes;
* scalar smooth partition of unity subordinate to a cover with support control;
* local Stokes on each localized form;
* finite summation of localized equalities;
* cancellation/reconstruction of `ω` and `dω` on `M.carrier`;
* reconstruction of the boundary integral on `M.boundary`;
* final theorem with no local support, chart, or integrability assumptions beyond
  compact regular sublevel domain and global smoothness of `ω`.

## Completion checks

The v2 theorem layer is complete only when:

* all definitions and the final compact-domain theorem build with `lake build`;
* there are no `sorry` placeholders in the theorem layer;
* `#print axioms` is checked for the final theorem and exported theorem-layer
  results;
* the theorem statement proves the compact regular sublevel-domain result, not a
  chart-dependent or chosen-cover-dependent substitute.
