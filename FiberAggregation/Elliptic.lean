import FiberAggregation.Core
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-!
# Weierstrass equations and j-invariant fibers

An affine Weierstrass equation is the zero fiber of its residual rule. The standard elliptic-curve
negation is an involutive self-rule preserving every residual fiber. We also record the fundamental
relation among `c₄`, `c₆`, and the discriminant, and organize elliptic models by fibers of the
j-invariant rule.
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

section JInvariant

variable {F : Type u} [Field F]

/-- Weierstrass models equipped with a proof that their discriminant is invertible. -/
abbrev EllipticModel (F : Type u) [Field F] :=
  {W : WeierstrassCurve F // W.IsElliptic}

/-- The j-invariant as a rule from elliptic models to the base field. -/
noncomputable def jRule (E : EllipticModel F) : F := by
  letI : E.1.IsElliptic := E.2
  exact E.1.j

/-- The aggregate of elliptic models with prescribed j-invariant. -/
def JFiber (j : F) : Type u :=
  Fiber (jRule (F := F)) j

/-- The explicit model supplied by mathlib for a prescribed j-invariant. -/
noncomputable def ofJModel (j : F) : EllipticModel F := by
  classical
  exact ⟨WeierstrassCurve.ofJ j, inferInstance⟩

/-- The explicit model really lies over its prescribed j-invariant. -/
theorem jRule_ofJModel (j : F) :
    jRule (ofJModel j) = j := by
  classical
  change (WeierstrassCurve.ofJ j).j = j
  exact WeierstrassCurve.ofJ_j j

/-- Every j-fiber is inhabited. -/
noncomputable def jFiberWitness (j : F) : JFiber j :=
  ⟨ofJModel j, jRule_ofJModel j⟩

/-- The j-invariant rule on elliptic models is surjective over every field. -/
theorem jRule_surjective : Function.Surjective (jRule (F := F)) := by
  intro j
  exact ⟨ofJModel j, jRule_ofJModel j⟩

/-- Over a separably closed field, every j-fiber is a single orbit under admissible changes of
Weierstrass variables. Thus equal visible j-invariant does not mean literal equality of models, but
it does determine the model up to the specified symmetry rule. -/
theorem jFiber_single_variableChange_orbit [IsSepClosed F] {j : F}
    (E E' : JFiber (F := F) j) :
    ∃ C : WeierstrassCurve.VariableChange F, C • E.1.1 = E'.1.1 := by
  letI : E.1.1.IsElliptic := E.1.2
  letI : E'.1.1.IsElliptic := E'.1.2
  apply WeierstrassCurve.exists_variableChange_of_j_eq
  have hE : E.1.1.j = j := by
    simpa [jRule] using E.2
  have hE' : E'.1.1.j = j := by
    simpa [jRule] using E'.2
  exact hE.trans hE'.symm

end JInvariant

end EllipticAnalysis
end FiberAggregation
