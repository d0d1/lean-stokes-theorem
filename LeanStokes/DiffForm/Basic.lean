/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Differential Forms — Basic Definitions

This file provides type aliases and basic infrastructure for working with
differential forms in the context of Stokes' theorem.

We build directly on mathlib's `extDeriv` API, which represents a differential
`n`-form on a normed space `E` as `E → E [⋀^Fin n]→L[𝕜] F`.

## Design decisions

We use `Fin d → ℝ` as our ambient Euclidean space ℝᵈ. This has better
typeclass support than `EuclideanSpace ℝ (Fin d)` for measure theory
(MeasureSpace instance is directly available).
-/

noncomputable section

open Topology Filter Set
open scoped Topology

/-- The ambient Euclidean space ℝᵈ, represented as `Fin d → ℝ`.
Uses pi-type which has direct MeasureSpace instance from Lebesgue measure. -/
abbrev ℝSpace (d : ℕ) := Fin d → ℝ

/-- A differential `n`-form on `ℝᵈ` with values in `ℝ`.
This is the mathlib representation: a function from the space to
continuous alternating maps. -/
abbrev DiffForm (d : ℕ) (n : ℕ) :=
  ℝSpace d → ℝSpace d [⋀^Fin n]→L[ℝ] ℝ

namespace DiffForm

variable {d n : ℕ}

/-- A form is smooth if it is `ContDiff ℝ ⊤`. -/
def IsSmooth (ω : DiffForm d n) : Prop :=
  ContDiff ℝ ⊤ ω

/-- A form is smooth on a set `s`. -/
def IsSmoothOn (ω : DiffForm d n) (s : Set (ℝSpace d)) : Prop :=
  ContDiffOn ℝ ⊤ ω s

/-- A differential form has compact support. -/
def HasCompactSupport (ω : DiffForm d n) : Prop :=
  _root_.HasCompactSupport ω

end DiffForm

end
