# LeanStokes

A sorry-free Lean 4/mathlib formalization of Stokes-type theorems for smooth
singular cubes, cubical chains, boxes, and compact regular sublevel domains in
Euclidean space.

## Scope

The repository contains two main theorem layers:

- **Smooth singular cubical Stokes.** For a globally smooth map
  `sigma : R^{n+1} -> R^m` and a smooth `n`-form `omega` on `R^m`, the integral
  of the true differential-form pullback of `d omega` over the unit cube equals
  the alternating sum of pullback integrals over the cube faces.
- **Box-controlled compact regular sublevel-domain Stokes.** For
  `M : SmoothDomain (n + 1)` and a smooth `ω : DiffForm (n + 1) n`,
  `SmoothDomain.stokes_boundaryIntegral` proves
  `M.domainIntegral (DiffForm.extd ω) = M.boundaryIntegral ω`.

Here `SmoothDomain.boundaryIntegral` is implemented as a fixed chosen
box-controlled boundary sum assembled from local boundary chart boxes and a
smooth partition of unity.  For smooth forms, it agrees with every subordinate
box-controlled boundary sum via
`SmoothDomain.boundaryIntegral_eq_boxControlledBoundaryIntegral_of_contDiff`.
This is not a general manifold-with-boundary integration API, and it does not
claim chart-independence outside the box-controlled Euclidean construction.

The repository also contains:

- box Stokes for coordinate `n`-forms on `R^{n+1}`;
- a bridge from the coordinate formula to mathlib's abstract `extDeriv`;
- local half-space and chart-box Stokes infrastructure for regular sublevel
  domains;
- true pullback of forms via `fderiv` for singular cubes;
- singular cubical chains and the linear extension of Stokes;
- chain-level `partial (partial c) = 0` for singular cubical chains;
- dimensional specializations including FTC, rectangular Green, divergence
  consistency, 3D Gauss, integration by parts, and Leibniz.

## Reproducibility

This repository is pinned to Lean 4.29.1 and mathlib `v4.29.1`.

```bash
lake exe cache get
lake build
lake exe diagnostics
```

The checked declarations in `LeanStokes.CubeStokes.Check`,
`LeanStokes.SingularCubeStokes.Check`, and `LeanStokes.Domain.Check` depend only
on Lean's standard axioms used throughout mathlib:

- `propext`
- `Classical.choice`
- `Quot.sound`

## Main declarations

- `SmoothDomain.stokes_boundaryIntegral`
- `SmoothDomain.boundaryIntegral`
- `SmoothDomain.boundaryIntegral_eq_boxControlledBoundaryIntegral_of_contDiff`
- `SmoothDomain.boxControlledBoundaryIntegral_eq_of_contDiff`
- `SmoothDomain.exists_boxControlledBoundaryIntegral_stokes`
- `SingularCubeStokes.singularStokes`
- `SingularCubeStokes.stokes_singular_boundary`
- `SingularCubeStokes.stokes_singular_chain`
- `SingularCubeStokes.stokes_chain`
- `SingularCubeStokes.bdry_bdry_chain_zero`
- `SingularCubeStokes.bdry_bdry_chain_zero_general`
- `CubeStokes.stokes_on_box`
- `CubeStokes.stokes_smooth`
- `CubeStokes.stokes_extDeriv_smooth`
- `CubeStokes.extDeriv_topCoeff_eq_extDerivCoord`
- `CubeStokes.ftc_stokes`
- `CubeStokes.green_stokes`
- `CubeStokes.divergence_stokes`
- `CubeStokes.gauss_3d`
- `CubeStokes.integration_by_parts`

## License

GPL-3.0-only.
