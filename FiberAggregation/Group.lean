import FiberAggregation.Core

/-!
# Group theory as fiber geometry

Stabilizers and kernels are literal fibers. Orbit–stabilizer then becomes a finite aggregation
formula for an orbit rule.
-/

universe u v

namespace FiberAggregation

section GroupAction

variable (G : Type u) {X : Type v} [Group G] [MulAction G X]

/-- The orbit rule based at `x`. -/
def orbitRule (x : X) : G → X :=
  fun g => g • x

/-- The stabilizer written as the fiber of the orbit rule over its base point. -/
abbrev StabilizerFiber (x : X) : Type u :=
  Fiber (orbitRule G x) x

/-- The stabilizer fiber is equivalent to mathlib's bundled stabilizer subgroup. -/
def stabilizerFiberEquiv (x : X) :
    StabilizerFiber G x ≃ MulAction.stabilizer G x where
  toFun g :=
    ⟨g.1, show g.1 • x = x from g.2⟩
  invFun g :=
    ⟨g.1, show (g.1 : G) • x = x from g.2⟩
  left_inv := by
    intro g
    apply Subtype.ext
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    rfl

/-- Fibers over points in the same orbit are equivalent by translation. -/
def orbitFiberEquiv (x : X) (g₀ : G) :
    Fiber (orbitRule G x) x ≃ Fiber (orbitRule G x) (g₀ • x) where
  toFun g :=
    ⟨g₀ * g.1, by
      change (g₀ * g.1) • x = g₀ • x
      have hg : g.1 • x = x := g.2
      rw [mul_smul, hg]⟩
  invFun g :=
    ⟨g₀⁻¹ * g.1, by
      change (g₀⁻¹ * g.1) • x = x
      have hg : g.1 • x = g₀ • x := g.2
      rw [mul_smul, hg, inv_smul_smul]⟩
  left_inv := by
    intro g
    apply Subtype.ext
    simp
  right_inv := by
    intro g
    apply Subtype.ext
    simp

/-- Orbit–stabilizer expressed with the stabilizer fiber rather than a primitive subgroup. -/
theorem card_orbit_mul_card_stabilizerFiber_eq_card_group
    (x : X) [Fintype G] [Fintype (MulAction.orbit G x)] :
    Fintype.card (MulAction.orbit G x) * Fintype.card (StabilizerFiber G x) =
      Fintype.card G := by
  letI : Fintype (MulAction.stabilizer G x) :=
    Fintype.ofEquiv (StabilizerFiber G x) (stabilizerFiberEquiv G x)
  rw [Fintype.card_congr (stabilizerFiberEquiv G x)]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

end GroupAction

section Kernel

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The kernel of a homomorphism written as the fiber over the unit. -/
abbrev KernelFiber (φ : G →* H) : Type u :=
  Fiber φ 1

/-- The kernel fiber is equivalent to the bundled kernel subgroup. -/
def kernelFiberEquiv (φ : G →* H) : KernelFiber φ ≃ φ.ker where
  toFun g :=
    ⟨g.1, show φ g.1 = 1 from g.2⟩
  invFun g :=
    ⟨g.1, show φ g.1 = 1 from g.2⟩
  left_inv := by
    intro g
    apply Subtype.ext
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    rfl

end Kernel

end FiberAggregation
