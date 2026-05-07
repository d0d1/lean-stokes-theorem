-- LeanStokes: Formalization of Stokes' Theorem in Lean 4/mathlib
-- Main module root — imports all submodules

-- Core cubical Stokes theorem (sorry-free, verified)
import LeanStokes.CubeStokes.Defs
import LeanStokes.CubeStokes.Theorem
import LeanStokes.CubeStokes.Smooth
import LeanStokes.CubeStokes.Classical
import LeanStokes.CubeStokes.BdryEquiv
import LeanStokes.CubeStokes.Bridge
import LeanStokes.CubeStokes.FacePullback
import LeanStokes.CubeStokes.Unified
import LeanStokes.CubeStokes.Validation
import LeanStokes.CubeStokes.Check

-- Corollaries (sorry-free)
import LeanStokes.CubeStokes.FTC
import LeanStokes.CubeStokes.Green
import LeanStokes.CubeStokes.Divergence
import LeanStokes.CubeStokes.IBP
import LeanStokes.CubeStokes.Chains
import LeanStokes.CubeStokes.Faces
import LeanStokes.CubeStokes.BdryOp
import LeanStokes.CubeStokes.BoundaryChain
import LeanStokes.CubeStokes.Properties
import LeanStokes.CubeStokes.Leibniz
import LeanStokes.CubeStokes.Examples
import LeanStokes.CubeStokes.Gauss3D
import LeanStokes.CubeStokes.DDZero
import LeanStokes.CubeStokes.Subdivision
import LeanStokes.CubeStokes.HarrisonComparison
import LeanStokes.CubeStokes.Demo
import LeanStokes.CubeStokes.Naturality

-- Bridge infrastructure to mathlib differential forms (sorry-free)
import LeanStokes.DiffForm.Basic
import LeanStokes.DiffForm.ExteriorDeriv
import LeanStokes.DiffForm.Pullback
import LeanStokes.DiffForm.Localization

-- Smooth singular cubical Stokes (extension layer)
import LeanStokes.SingularCubeStokes.Defs
import LeanStokes.SingularCubeStokes.Pullback
import LeanStokes.SingularCubeStokes.Theorem

-- Integration and domain infrastructure (sorry-free supporting definitions)
import LeanStokes.Integration.FormIntegral
import LeanStokes.Integration.Pullback
import LeanStokes.Integration.OrientedIntegral
import LeanStokes.Domain.SmoothDomain
import LeanStokes.Domain.DomainIntegral
import LeanStokes.Domain.HalfSpace
import LeanStokes.Domain.Coordinate
import LeanStokes.Domain.BoundaryOrient
import LeanStokes.Domain.BoundaryIntegral
import LeanStokes.Domain.BoundaryFlattening
import LeanStokes.Domain.ChartChangeOfVariables
import LeanStokes.Domain.BoundaryChart
import LeanStokes.Domain.JacobianSign
import LeanStokes.Domain.BoundaryChartIntegral
import LeanStokes.Domain.BoundaryChartPatch
import LeanStokes.Domain.BoundaryChartPatchIntegral
import LeanStokes.Domain.BoxStokes
import LeanStokes.SingularCubeStokes.FaceMatching
import LeanStokes.SingularCubeStokes.Chain
import LeanStokes.SingularCubeStokes.BdryBdry
import LeanStokes.SingularCubeStokes.Check
