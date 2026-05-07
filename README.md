# LeanStokes

A sorry-free Lean 4/mathlib formalization of Stokes-type theorems for smooth
singular cubes and axis-aligned boxes in arbitrary finite dimension.

## Scope

The main theorem is smooth singular cubical Stokes: for a globally smooth map
`sigma : R^{n+1} -> R^m` and a smooth `n`-form `omega` on `R^m`, the integral
of the true differential-form pullback of `d omega` over the unit cube equals
the alternating sum of pullback integrals over the cube faces.

This repository also contains:

- box Stokes for coordinate `n`-forms on `R^{n+1}`;
- a bridge from the coordinate formula to mathlib's abstract `extDeriv`;
- true pullback of forms via `fderiv` for singular cubes;
- singular cubical chains and the linear extension of Stokes;
- chain-level `partial (partial c) = 0` for singular cubical chains;
- dimensional specializations including FTC, rectangular Green, divergence
  consistency, 3D Gauss, integration by parts, and Leibniz.

The development does not formalize manifold-with-boundary Stokes, integration of
forms over manifolds, partition-of-unity arguments, image-domain semantics, or
boundary orientation for manifolds.

## Reproducibility

This repository is pinned to Lean 4.29.1 and mathlib `v4.29.1`.

```bash
lake exe cache get
lake build
lake exe diagnostics
```

At the audited state, `lake build` completed successfully with 2659 jobs.
The Lean artifact contains 44 Lean source modules under `LeanStokes/`, 4028
source lines, 205 named declarations, and 79 `#print axioms` checks.

The checked declarations depend only on Lean's standard axioms used throughout
mathlib:

- `propext`
- `Classical.choice`
- `Quot.sound`

## Main declarations

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
