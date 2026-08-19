import FiberAggregation.Core

/-!
# Linear equations as affine fibers

For a linear or additive operator, every nonempty solution fiber is a torsor for the kernel.  This
is the structural statement underlying uniqueness modulo homogeneous solutions for linear PDEs.
-/

universe u v

namespace FiberAggregation
namespace LinearEquation

variable {U : Type u} {V : Type v} [AddGroup U] [AddGroup V]

/-- The solution aggregate of the equation `L u = f`. -/
def Solutions (L : U →+ V) (f : V) : Type u :=
  Fiber L f

/-- A solution fiber based at `u₀` is equivalent to the homogeneous kernel. -/
def solutionFiberKernelEquiv (L : U →+ V) (u₀ : U) :
    Solutions L (L u₀) ≃ L.ker where
  toFun u :=
    ⟨u.1 - u₀, by
      change L (u.1 - u₀) = 0
      rw [map_sub, u.2, sub_self]⟩
  invFun k :=
    ⟨k.1 + u₀, by
      change L (k.1 + u₀) = L u₀
      rw [map_add, show L k.1 = 0 from k.2, zero_add]⟩
  left_inv := by
    intro u
    apply Subtype.ext
    simp
  right_inv := by
    intro k
    apply Subtype.ext
    simp

/-- Injectivity of the operator makes every solution fiber a subsingleton. -/
theorem solutionFiber_subsingleton_of_injective
    (L : U →+ V) (hL : Function.Injective L) (f : V) :
    Subsingleton (Solutions L f) :=
  fiber_subsingleton_of_injective hL f

/-- If a solution exists and the operator is injective, the solution fiber is determinate. -/
theorem solutionFiber_determinate_of_bijective
    (L : U →+ V) (hL : Function.Bijective L) (f : V) :
    Determinate (Solutions L f) :=
  fiber_determinate_of_bijective hL f

end LinearEquation
end FiberAggregation
