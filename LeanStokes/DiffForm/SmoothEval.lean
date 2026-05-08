/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes.DiffForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Smooth Evaluation Helpers

This module contains generic smoothness infrastructure for evaluating smooth
continuous multilinear-map-valued functions on smooth vector-valued arguments.
It is independent of cubes, domains, and Stokes theorems.
-/

noncomputable section

open scoped Topology

namespace DiffForm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- If a smooth function takes values in continuous multilinear maps and each argument function
is smooth, then pointwise evaluation is smooth. -/
theorem contDiff_multilinearMap_apply_of_contDiff (N : ℕ)
    (f : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin N => F) G)
    (g : Fin N → E → F)
    (hf : ContDiff 𝕜 (⊤ : ℕ∞) f) (hg : ∀ k, ContDiff 𝕜 (⊤ : ℕ∞) (g k)) :
    ContDiff 𝕜 (⊤ : ℕ∞) (fun x => (f x) (fun k => g k x)) := by
  have happ : ContDiff 𝕜 (⊤ : ℕ∞)
      (fun p : ContinuousMultilinearMap 𝕜 (fun _ : Fin N => F) G × (Fin N → F) =>
        p.1 p.2) := by
    rw [← contDiffOn_univ]
    exact ((ContinuousLinearMap.id 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin N => F) G)
      ).cpolynomialOn_uncurry_of_multilinear (s := Set.univ)).contDiffOn
  exact happ.comp (hf.prodMk (contDiff_pi' hg))

end DiffForm

end
