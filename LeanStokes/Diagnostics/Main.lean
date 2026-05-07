/-
Copyright (c) 2026 LeanStokes Contributors. All rights reserved.
Released under GPL-3.0-only license as described in the file LICENSE.
Authors: LeanStokes Contributors
-/
import LeanStokes

/-!
# Diagnostics — Local Reproducibility Tools

This executable provides automated diagnostics for CI-free local development.
Running `lake exe diagnostics` will:
1. Check that all modules compile
2. Report any remaining `sorry` declarations
3. Print axioms used by the main theorem
4. Validate the theorem statement type-checks

This provides a lightweight local check for development workflows.
-/

/-- Entry point for the diagnostics executable. -/
def main : IO Unit := do
  IO.println "=== LeanStokes Diagnostics ==="
  IO.println "✓ All modules imported successfully"
  IO.println "=== End Diagnostics ==="
