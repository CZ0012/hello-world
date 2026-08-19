import FiberAggregation.Core
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Weierstrass equations as fibers

An affine Weierstrass equation is the zero fiber of its residual rule. The standard elliptic-curve
negation is an involutive self-rule preserving every residual fiber. We also record mathlib's
fundamental relation among `c₄`, `c₆`, and the discriminant as an equalizer-fiber witness.
-/

universe u

namespace FiberAggregation
namespace EllipticAnalysis

variable {R : Type u} [CommRing R]

/-- Residual of the affine Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`. -/
def weierstrassResidual (W : WeierstrassCurve R) (p : R × R) : R :=
  p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 -
    (p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆)

/-- The aggregate of affine solutions is the zero fiber of the residual rule. -/
def AffineSolutionFiber (W : WeierstrassCurve R) : Type u :=
  Fiber (weierstrassResidual W) 0

/-- The standard negation rule on affine Weierstrass coordinates. -/
def negatePoint (W : WeierstrassCurve R) (p : R × R) : R × R :=
  (p.1, -p.2 - W.a₁ * p.1 - W.a₃)

/-- Weierstrass negation preserves the residual, hence every residual fiber. -/
theorem residual_negatePoint (W : WeierstrassCurve R) (p : R × R) :
    weierstrassResidual W (negatePoint W p) = weierstrassResidual W p := by
  rcases p with ⟨x, y⟩
  dsimp [weierstrassResidual, negatePoint]
  ring

/-- Weierstrass negation is involutive. -/
theorem negatePoint_involutive (W : WeierstrassCurve R) :
    Function.Involutive (negatePoint W) := by
  rintro ⟨x, y⟩
  apply Prod.ext
  · rfl
  · dsimp [negatePoint]
    ring

/-- Negation induces a self-equivalence of every residual fiber. -/
def negateFiberEquiv (W : WeierstrassCurve R) (c : R) :
    Fiber (weierstrassResidual W) c ≃ Fiber (weierstrassResidual W) c where
  toFun p :=
    ⟨negatePoint W p.1, by
      rw [residual_negatePoint]
      exact p.2⟩
  invFun p :=
    ⟨negatePoint W p.1, by
      rw [residual_negatePoint]
      exact p.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact negatePoint_involutive W p.1
  right_inv := by
    intro p
    apply Subtype.ext
    exact negatePoint_involutive W p.1

/-- Left side of the fundamental invariant relation. -/
def cRelationLeft (W : WeierstrassCurve R) : R :=
  1728 * W.Δ

/-- Right side of the fundamental invariant relation. -/
def cRelationRight (W : WeierstrassCurve R) : R :=
  W.c₄ ^ 3 - W.c₆ ^ 2

/-- Every Weierstrass curve lies in the equalizer fiber expressing
`1728 Δ = c₄³ - c₆²`. -/
def cRelationWitness (W : WeierstrassCurve R) :
    EqFiber (cRelationLeft : WeierstrassCurve R → R) cRelationRight :=
  ⟨W, W.c_relation⟩

end EllipticAnalysis
end FiberAggregation
