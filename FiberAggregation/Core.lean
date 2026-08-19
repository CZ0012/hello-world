import Mathlib

/-!
# Fiber–aggregation core

This file gives a conservative Lean model of the proposed language:

* an **aggregate** is represented by a Lean type;
* a **fiber rule** is represented by a function;
* the uncertainty over an observable value is the corresponding fiber;
* aggregation of all fibers is a dependent sum.

The development is intentionally relative to Lean's type theory. It does not claim that the two
words `aggregate` and `fiber` have already been installed as a new proof-theoretic foundation.
Instead, it isolates the structural laws that any proposed foundation should validate.
-/

universe u v w

namespace FiberAggregation

/-- A rule from one aggregate to another. -/
abbrev Rule (A : Type u) (B : Type v) := A → B

/-- The fiber of a rule `f` over the visible value `b`. -/
def Fiber {A : Type u} {B : Type v} (f : A → B) (b : B) : Type u :=
  {a : A // f a = b}

/-- Finite domains induce finite fibers. -/
noncomputable instance instFintypeFiber {A : Type u} {B : Type v} [Fintype A]
    (f : A → B) (b : B) : Fintype (Fiber f b) := by
  classical
  unfold Fiber
  infer_instance

/-- The aggregate on which two rules agree. It is the pullback of the diagonal. -/
def EqFiber {A : Type u} {B : Type v} (f g : A → B) : Type u :=
  {a : A // f a = g a}

/-- The dependent aggregation of every fiber of `f`. -/
def TotalFiber {A : Type u} {B : Type v} (f : A → B) : Type (max u v) :=
  Σ b : B, Fiber f b

/-- Aggregating every fiber of a rule reconstructs its domain. -/
def totalFiberEquiv {A : Type u} {B : Type v} (f : A → B) : TotalFiber f ≃ A where
  toFun x := x.2.1
  invFun a := ⟨f a, ⟨a, rfl⟩⟩
  left_inv := by
    rintro ⟨b, ⟨a, h⟩⟩
    subst b
    rfl
  right_inv := by
    intro a
    rfl

/-- The fiber of a composite rule is the aggregation of the upper fibers over the lower fiber. -/
def fiberCompEquiv {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) (c : C) :
    Fiber (g ∘ f) c ≃ Σ y : Fiber g c, Fiber f y.1 where
  toFun x :=
    ⟨⟨f x.1, by simpa [Function.comp_def] using x.2⟩, ⟨x.1, rfl⟩⟩
  invFun y :=
    ⟨y.2.1, by
      change g (f y.2.1) = c
      rw [y.2.2]
      exact y.1.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
    cases ha
    rfl

/-- The projection of a dependent aggregate onto its indexing aggregate. -/
def sigmaProjection {A : Type u} (E : A → Type v) : (Σ a, E a) → A :=
  Sigma.fst

/-- The fiber of a dependent-sum projection is the indexed aggregate itself. -/
def fiberSigmaProjectionEquiv {A : Type u} (E : A → Type v) (a : A) :
    Fiber (sigmaProjection E) a ≃ E a where
  toFun x := x.2 ▸ x.1.2
  invFun e := ⟨⟨a, e⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨a', e⟩, h⟩
    cases h
    rfl
  right_inv := by
    intro e
    rfl

/-- A fiber is structurally determinate when it is inhabited and subsingleton. -/
def Determinate (X : Type u) : Prop :=
  Nonempty X ∧ Subsingleton X

/-- Fibers of an injective rule are subsingletons. -/
theorem fiber_subsingleton_of_injective {A : Type u} {B : Type v}
    {f : A → B} (hf : Function.Injective f) (b : B) :
    Subsingleton (Fiber f b) where
  allEq x y := by
    apply Subtype.ext
    apply hf
    exact x.2.trans y.2.symm

/-- A fiber is inhabited exactly when its base value belongs to the range of the rule. -/
theorem fiber_nonempty_iff_mem_range {A : Type u} {B : Type v}
    {f : A → B} {b : B} :
    Nonempty (Fiber f b) ↔ b ∈ Set.range f := by
  constructor
  · rintro ⟨⟨a, ha⟩⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨⟨a, ha⟩⟩

/-- Every fiber of a bijective rule is determinate. -/
theorem fiber_determinate_of_bijective {A : Type u} {B : Type v}
    {f : A → B} (hf : Function.Bijective f) (b : B) :
    Determinate (Fiber f b) := by
  constructor
  · obtain ⟨a, ha⟩ := hf.2 b
    exact ⟨⟨a, ha⟩⟩
  · exact fiber_subsingleton_of_injective hf.1 b

/-- Finite fiber decomposition: the size of an aggregate is the sum of its fiber sizes. -/
theorem card_eq_sum_fiber {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] (f : A → B) :
    Fintype.card A = ∑ b : B, Fintype.card (Fiber f b) := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (totalFiberEquiv f).symm

/-- For a finite self-rule, total local fiber multiplicity is conserved. -/
theorem self_fiber_card_conservation {A : Type u} [Fintype A] (f : A → A) :
    ∑ a : A, Fintype.card (Fiber f a) = Fintype.card A := by
  simpa using (card_eq_sum_fiber f).symm

end FiberAggregation
