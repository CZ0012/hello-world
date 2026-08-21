import FiberAggregation.Core
import FiberAggregation.Diagonal

/-!
# Stratified universality and self-classification obstructions

This file separates several very different claims:

1. At a fixed universe level, there is a higher-level aggregate coding every small aggregate.
2. There is likewise a higher-level aggregate whose points are all small rules between small
   aggregates.
3. The universal family `Sigma (A : Type u), A -> Type u` contains every small aggregate as a
   fiber and classifies the fiber decomposition of every small-domain rule.
4. A same-level aggregate cannot, through an unrestricted self-evaluator, classify every rule into
   an observable aggregate that has a fixed-point-free polarity. Boolean comprehension is the
   clearest instance.

The positive constructions are predicative and stratified. The negative results identify the
additional self-evaluation/comprehension strength that triggers diagonal contradiction.
-/

universe u v w

namespace FiberAggregation
namespace Universality

/-- The code aggregate for all Lean aggregates in `Type u`.
It lives one universe level above the aggregates it codes. -/
abbrev SmallAggregateUniverse : Type (u + 1) := Type u

/-- The aggregate of all rules from a `u`-small aggregate to a `v`-small aggregate. A point keeps
its source, target, and rule together, so no untyped application is introduced. -/
def SmallRuleUniverse :=
  Sigma fun A : Type u => Sigma fun B : Type v => A → B

/-- Package an arbitrary small rule as a point of the stratified rule aggregate. -/
def ruleCode {A : Type u} {B : Type v} (f : A → B) :
    SmallRuleUniverse (u := u) (v := v) :=
  ⟨A, B, f⟩

/-- Source aggregate of a coded rule. -/
def codedRuleSource (r : SmallRuleUniverse (u := u) (v := v)) : Type u :=
  r.1

/-- Target aggregate of a coded rule. -/
def codedRuleTarget (r : SmallRuleUniverse (u := u) (v := v)) : Type v :=
  r.2.1

/-- Decode and apply a coded rule, retaining its dependent source and target. -/
def codedRuleMap (r : SmallRuleUniverse (u := u) (v := v)) :
    codedRuleSource r → codedRuleTarget r :=
  r.2.2

@[simp]
theorem codedRuleSource_ruleCode {A : Type u} {B : Type v} (f : A → B) :
    codedRuleSource (ruleCode f) = A :=
  rfl

@[simp]
theorem codedRuleTarget_ruleCode {A : Type u} {B : Type v} (f : A → B) :
    codedRuleTarget (ruleCode f) = B :=
  rfl

@[simp]
theorem codedRuleMap_ruleCode {A : Type u} {B : Type v} (f : A → B) :
    codedRuleMap (ruleCode f) = f :=
  rfl

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

/-- The classifier of the local fibers of an arbitrary rule. -/
def fiberClassifier {A : Type u} {B : Type v} (f : A → B) : B → Type u :=
  fun b => Fiber f b

/-- The total aggregate classified by `fiberClassifier f`. -/
abbrev ClassifiedRuleTotal {A : Type u} {B : Type v} (f : A → B) : Type (max u v) :=
  Sigma fun b : B => fiberClassifier f b

/-- Classifying all local fibers of a rule and aggregating them reconstructs its domain. -/
def classifiedRuleTotalEquivDomain {A : Type u} {B : Type v} (f : A → B) :
    ClassifiedRuleTotal f ≃ A := by
  simpa [ClassifiedRuleTotal, fiberClassifier] using totalFiberEquiv f

/-- The reconstructed total aggregate still lies over the original base point. -/
theorem classifiedRuleProjection_compatible
    {A : Type u} {B : Type v} (f : A → B) (x : ClassifiedRuleTotal f) :
    x.1 = f (classifiedRuleTotalEquivDomain f x) := by
  rcases x with ⟨b, ⟨a, h⟩⟩
  exact h.symm

/-- Every local fiber of every rule with `u`-small domain occurs as a fiber of the universal
family. -/
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

/-- A same-level evaluator classifies all endorules when every `U → U` rule is one of its rows. -/
def ClassifiesAllEndorules {U : Type u} (evaluate : U → U → U) : Prop :=
  WeaklyPointSurjective evaluate

/-- Complete same-level classification of endorules forces every endorule to have a fixed point. -/
theorem fullSelfRuleClassifier_forcesFixedPoint
    {U : Type u} (evaluate : U → U → U)
    (hcomplete : ClassifiesAllEndorules evaluate) (rule : U → U) :
    ∃ value : U, rule value = value :=
  lawvere_fixedPoint evaluate hcomplete rule

/-- Hence a fixed-point-free self-rule forbids complete same-level classification of all endorules. -/
theorem no_sameLevel_fullRuleClassifier_of_fixedPointFree
    {U : Type u} (evaluate : U → U → U) (polarity : U → U)
    (hpolarity : ∀ value, polarity value ≠ value) :
    ¬ClassifiesAllEndorules evaluate :=
  no_complete_self_encoding_of_fixedPointFree evaluate polarity hpolarity

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
