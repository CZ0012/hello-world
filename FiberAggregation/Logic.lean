import FiberAggregation.Core

/-!
# Derived logical operations

The symbols below are not proposed as new primitives.  They demonstrate how dependent products,
dependent sums, and pullback fibers recover the usual logical operations after suitable truncation.
-/

universe u v

namespace FiberAggregation

/-- `All E` is the aggregate of coherent sections of the family `E`. -/
def All {A : Type u} (E : A → Type v) : Type (max u v) :=
  (a : A) → E a

/-- `Some E` keeps both a base witness and a witness in its fiber. -/
def Some {A : Type u} (E : A → Type v) : Type (max u v) :=
  Σ a : A, E a

/-- Membership relative to a proposed subaggregate rule is its pullback fiber. -/
def Membership {A : Type u} {S : Type v} (a : A) (m : S → A) : Type v :=
  Fiber m a

/-- A rule is thin when every membership fiber is a subsingleton. -/
def IsThin {A : Type u} {S : Type v} (m : S → A) : Prop :=
  ∀ a, Subsingleton (Fiber m a)

/-- Thin rules are exactly injective rules. -/
theorem injective_iff_thin {A : Type u} {S : Type v} (m : S → A) :
    Function.Injective m ↔ IsThin m := by
  constructor
  · intro hm a
    exact fiber_subsingleton_of_injective hm a
  · intro hm x y hxy
    let x' : Fiber m (m x) := ⟨x, rfl⟩
    let y' : Fiber m (m x) := ⟨y, hxy.symm⟩
    letI : Subsingleton (Fiber m (m x)) := hm (m x)
    exact congrArg Subtype.val (Subsingleton.elim x' y')

/-- A coherent section is precisely a right inverse of the projection of its total aggregate. -/
def allEquivSections {A : Type u} (E : A → Type v) :
    All E ≃ {s : A → (Σ a, E a) // sigmaProjection E ∘ s = id} where
  toFun s :=
    ⟨fun a => ⟨a, s a⟩, by
      funext a
      rfl⟩
  invFun s := fun a =>
    (show E ((sigmaProjection E ∘ s.1) a) from s.1 a |>.2) |> (by
      rw [s.2]
      exact id)
  left_inv := by
    intro s
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    funext a
    have h := congrFun s.2 a
    cases s.1 a with
    | mk a' e =>
      dsimp [sigmaProjection, Function.comp_def] at h
      cases h
      rfl

end FiberAggregation
