import FiberAggregation.Core

/-!
# An abstract Noether schema

The differential-geometric first variation formula is additional structure; it cannot be derived
from bare fibers alone.  Once supplied, conservation on the Euler–Lagrange solution fiber is a
formal consequence.
-/

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace FiberAggregation

/-- Data sufficient for the algebraic core of Noether's first theorem. -/
structure VariationalSystem
    (Configuration : Type u₁) (Equation : Type u₂) (Variation : Type u₃)
    (Current : Type u₄) (Scalar : Type u₅) (Symmetry : Type u₆)
    [Zero Equation] [Zero Scalar] where
  eulerLagrange : Configuration → Equation
  variation : Symmetry → Configuration → Variation
  current : Symmetry → Configuration → Current
  divergence : Current → Scalar
  pairing : Equation → Variation → Scalar
  firstVariation : ∀ s q,
    divergence (current s q) = pairing (eulerLagrange q) (variation s q)
  pairing_zero : ∀ v, pairing 0 v = 0

namespace VariationalSystem

variable {Configuration : Type u₁} {Equation : Type u₂} {Variation : Type u₃}
  {Current : Type u₄} {Scalar : Type u₅} {Symmetry : Type u₆}
  [Zero Equation] [Zero Scalar]

/-- The aggregate of classical solutions is the zero fiber of the Euler–Lagrange rule. -/
def Solutions
    (S : VariationalSystem Configuration Equation Variation Current Scalar Symmetry) : Type u₁ :=
  Fiber S.eulerLagrange 0

/-- The Noether current associated with `s` is conserved at the solution `q`. -/
def IsConservedAt
    (S : VariationalSystem Configuration Equation Variation Current Scalar Symmetry)
    (s : Symmetry) (q : Solutions S) : Prop :=
  S.divergence (S.current s q.1) = 0

/-- Abstract Noether theorem: the first-variation identity restricts to a conservation law on the
Euler–Lagrange fiber. -/
theorem noether_on_solution_fiber
    (S : VariationalSystem Configuration Equation Variation Current Scalar Symmetry)
    (s : Symmetry) (q : Solutions S) :
    S.IsConservedAt s q := by
  rw [IsConservedAt, S.firstVariation, q.2, S.pairing_zero]

end VariationalSystem

end FiberAggregation
