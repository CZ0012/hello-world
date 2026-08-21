import FiberAggregation.Core
import Mathlib.Analysis.Distribution.Sobolev

/-!
# Elliptic-type operators as solution fibers

The Bessel potential is an invertible Fourier-multiplier model of an elliptic operator. Its equation
fibers are therefore determinate. We also expose the standard Sobolev-order loss under the
Laplacian.
-/

universe u v

namespace FiberAggregation
namespace EllipticPDE

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap Laplacian

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section BesselPotential

variable [NormedSpace ℂ F]

/-- The solution aggregate of a Bessel-potential equation. -/
def BesselEquationFiber (s : ℝ) (f : 𝓢'(E, F)) : Type _ :=
  Fiber (TemperedDistribution.besselPotential E F s) f

/-- Bessel potentials of opposite order are mutual inverses. -/
theorem besselPotential_bijective (s : ℝ) :
    Function.Bijective (TemperedDistribution.besselPotential E F s) := by
  constructor
  · intro u v huv
    have h := congrArg (TemperedDistribution.besselPotential E F (-s)) huv
    simpa using h
  · intro f
    refine ⟨TemperedDistribution.besselPotential E F (-s) f, ?_⟩
    exact (TemperedDistribution.besselPotential_neg_apply_eq_iff
      (E := E) (F := F) s f (TemperedDistribution.besselPotential E F (-s) f)).mp rfl

/-- Every Bessel-potential equation has a unique solution in tempered distributions. -/
theorem besselEquationFiber_determinate (s : ℝ) (f : 𝓢'(E, F)) :
    Determinate (BesselEquationFiber s f) :=
  fiber_determinate_of_bijective (besselPotential_bijective (E := E) (F := F) s) f

end BesselPotential

section SobolevRegularity

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Laplacian lowers Sobolev order by two. -/
theorem laplacian_lowers_sobolev_order {s : ℝ} {f : 𝓢'(E, F)}
    (hf : TemperedDistribution.MemSobolev s 2 f) :
    TemperedDistribution.MemSobolev (s - 2) 2 (Δ f) :=
  hf.laplacian

end SobolevRegularity

end EllipticPDE
end FiberAggregation
