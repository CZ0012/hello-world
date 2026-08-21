import FiberAggregation.Core
import FiberAggregation.Diagonal

/-!
# Stratified universality and self-classification obstructions

This file separates two very different claims:

1. At a fixed universe level, there is a higher-level aggregate whose fibers contain every small
   aggregate.  In Lean this is the universal family

   `Sigma (A : Type u), A -> Type u`.

2. A same-level aggregate cannot, through a Boolean membership/evaluation rule, classify every
   Boolean-valued subaggregate of itself.  This is the direct diagonal obstruction.

The first construction is predicative and stratified.  The second theorem identifies the additional
self-evaluation/comprehension strength that is incompatible with Boolean negation.
-/

universe u v w

namespace FiberAggregation
namespace Universality

/-- The code aggregate for all Lean aggregates in `Type u`.
It lives one universe level above the aggregates it codes. -/
abbrev SmallAggregateUniverse : Type (u + 1) := Type u

/-- The total aggregate of the universal family of `u`-small aggregates. -/
def UniversalFiberTotal : Type (u + 1) :=
  Sigma fun A : Type u => A

/-- The universal fiber rule: its fiber over the code `A` is equivalent to `A`. -/
def universalFiberRule :
    UniversalFiberTotal (u := u) → SmallAggregateUniverse (u := u) :=
  Sigma.fst

/-- Every `u`-small aggregate occurs as a fiber of the universal fiber rule. -/
def universalFiberEquiv (A : Type u) :
    Fiber (universalFiberRule (u := u)) A ≃ A := by
  simpa [UniversalFiberTotal, universalFiberRule] using
    (fiberSigmaProjectionEquiv (fun A : Type u => A) A)

/-- A decoding family codes all `u`-small aggregates when every such aggregate has a code whose
interpretation is equivalent to it. -/
def CodesAllSmallAggregates (Code : Type v) (El : Code → Type u) : Prop :=
  ∀ A : Type u, ∃ code : Code, Nonempty (El code ≃ A)

/-- `Type u`, viewed from the next universe, codes all aggregates in `Type u`. -/
theorem smallAggregateUniverse_codesAll :
    CodesAllSmallAggregates (Type u) (fun A : Type u => A) := by
  intro A
  exact ⟨A, ⟨Equiv.refl A⟩⟩

/-- A rule contains all `u`-small aggregates as fibers when every such aggregate is equivalent to
one of its fibers. -/
def ContainsAllSmallAggregatesAsFibers
    {Base : Type v} {Total : Type w} (π : Total → Base) : Prop :=
  ∀ A : Type u, ∃ b : Base, Nonempty (Fiber π b ≃ A)

/-- The stratified universal fiber rule contains every `u`-small aggregate as a fiber. -/
theorem universalFiberRule_containsAllSmallAggregates :
    ContainsAllSmallAggregatesAsFibers (u := u) (universalFiberRule (u := u)) := by
  intro A
  exact ⟨A, ⟨universalFiberEquiv A⟩⟩

/-- The classifier of the fibers of an arbitrary rule. -/
def fiberClassifier {A : Type u} {B : Type v} (f : A → B) : B → Type u :=
  fun b => Fiber f b

/-- The total aggregate classified by `fiberClassifier f`. -/
abbrev ClassifiedRuleTotal {A : Type u} {B : Type v} (f : A → B) : Type (max u v) :=
  Sigma fun b : B => fiberClassifier f b

/-- Classifying all fibers of a rule and aggregating them reconstructs its domain. -/
def classifiedRuleTotalEquivDomain {A : Type u} {B : Type v} (f : A → B) :
    ClassifiedRuleTotal f ≃ A := by
  simpa [ClassifiedRuleTotal, fiberClassifier] using totalFiberEquiv f

/-- The reconstructed total aggregate still lies over the original base point. -/
theorem classifiedRuleProjection_compatible
    {A : Type u} {B : Type v} (f : A → B) (x : ClassifiedRuleTotal f) :
    x.1 = f (classifiedRuleTotalEquivDomain f x) := by
  rcases x with ⟨b, ⟨a, h⟩⟩
  exact h.symm

/-- Every fiber of every rule with `u`-small domain occurs as a fiber of the universal family. -/
def everyRuleFiberOccursInUniversalFamily
    {A : Type u} {B : Type v} (f : A → B) (b : B) :
    Fiber (universalFiberRule (u := u)) (fiberClassifier f b) ≃ Fiber f b :=
  universalFiberEquiv (Fiber f b)

/-- Self-coding alone is weak: one code may decode to the code aggregate itself. -/
def SelfCodes (Code : Type u) (El : Code → Type u) : Prop :=
  ∃ code : Code, Nonempty (El code ≃ Code)

/-- A trivial self-code exists, demonstrating that self-reference alone is not contradictory. -/
theorem unit_selfCodes : SelfCodes Unit (fun _ : Unit => Unit) :=
  ⟨(), ⟨Equiv.refl Unit⟩⟩

/-- A Boolean membership table classifies all Boolean subaggregates of `U` when every profile
`U → Bool` occurs as one of its rows. -/
def ClassifiesAllBooleanSubaggregates {U : Type u}
    (membership : U → U → Bool) : Prop :=
  ∀ profile : U → Bool, ∃ code : U, membership code = profile

/-- Full Boolean self-classification is exactly weak point-surjectivity of the evaluator. -/
theorem classifiesAllBooleanSubaggregates_iff_weaklyPointSurjective
    {U : Type u} (membership : U → U → Bool) :
    ClassifiesAllBooleanSubaggregates membership ↔ WeaklyPointSurjective membership :=
  Iff.rfl

/-- No aggregate can internally classify every Boolean subaggregate of itself through a same-level
membership/evaluation table. -/
theorem no_sameLevel_fullBooleanSubaggregateClassifier
    {U : Type u} (membership : U → U → Bool) :
    ¬ClassifiesAllBooleanSubaggregates membership :=
  no_complete_bool_self_encoding membership

/-- Consequently there is no same-level Boolean membership rule together with unrestricted
comprehension of all Boolean subaggregates. -/
theorem no_selfContainedBooleanComprehension (U : Type u) :
    ¬∃ membership : U → U → Bool, ClassifiesAllBooleanSubaggregates membership := by
  rintro ⟨membership, hmembership⟩
  exact no_sameLevel_fullBooleanSubaggregateClassifier membership hmembership

end Universality
end FiberAggregation
