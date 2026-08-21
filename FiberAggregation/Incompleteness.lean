import FiberAggregation.Core
import FiberAggregation.Diagonal

/-!
# Incompleteness as a fixed point of proof-fiber polarity

A formal proof system supplies two aggregates:

* an aggregate of sentences;
* an aggregate of proof objects, with a conclusion rule into the sentence aggregate.

For a sentence `σ`, its proof fiber is the fiber of the conclusion rule over `σ`.  The two
propositional coordinates

```
(Nonempty (ProofFiber σ), Nonempty (ProofFiber (neg σ)))
```

record whether `σ` is provable and whether it is refutable.  Negation exchanges these coordinates.
A fixed point of this exchange has one of two shapes: both coordinates are empty, or both are
inhabited.  Consistency excludes the second shape, leaving an independent sentence.

The arithmetic work in a Gödel or Rosser theorem is precisely what constructs such a fixed point:
effective coding makes proof-fiber inhabitance internally representable, and diagonal substitution
feeds the resulting predicate its own code.  This file verifies the abstract fiber-theoretic core;
it does not formalize Gödel numbering or recursive enumerability themselves.
-/

universe u v w

namespace FiberAggregation
namespace Incompleteness

/-- A proof system consists of a conclusion rule and a syntactic polarity operation. -/
structure ProofSystem (Sentence : Type u) (Proof : Type v) where
  conclusion : Proof → Sentence
  neg : Sentence → Sentence

namespace ProofSystem

variable {Sentence : Type u} {Proof : Type v}

/-- Proof objects whose visible conclusion is `σ`. -/
def ProofFiber (S : ProofSystem Sentence Proof) (σ : Sentence) : Type v :=
  Fiber S.conclusion σ

/-- A sentence is provable when its proof fiber is inhabited. -/
def Provable (S : ProofSystem Sentence Proof) (σ : Sentence) : Prop :=
  Nonempty (S.ProofFiber σ)

/-- A sentence is refutable when the proof fiber of its syntactic negation is inhabited. -/
def Refutable (S : ProofSystem Sentence Proof) (σ : Sentence) : Prop :=
  S.Provable (S.neg σ)

/-- Consistency forbids simultaneous inhabitants of opposite proof fibers. -/
def Consistent (S : ProofSystem Sentence Proof) : Prop :=
  ∀ σ, S.Provable σ → S.Refutable σ → False

/-- Completeness requires at least one of the two opposite proof fibers to be inhabited. -/
def Complete (S : ProofSystem Sentence Proof) : Prop :=
  ∀ σ, S.Provable σ ∨ S.Refutable σ

/-- A sentence is independent when both opposite proof fibers are empty. -/
def Independent (S : ProofSystem Sentence Proof) (σ : Sentence) : Prop :=
  ¬S.Provable σ ∧ ¬S.Refutable σ

/-- A local inconsistency is simultaneous inhabitation of both opposite proof fibers. -/
def InconsistentAt (S : ProofSystem Sentence Proof) (σ : Sentence) : Prop :=
  S.Provable σ ∧ S.Refutable σ

/-- A proof-status fixed point is a sentence whose two opposite proof fibers have the same
inhabitation status. -/
def StatusFixedPoint (S : ProofSystem Sentence Proof) (σ : Sentence) : Prop :=
  S.Provable σ ↔ S.Refutable σ

/-- The system is incomplete when some sentence has two empty opposite proof fibers. -/
def Incomplete (S : ProofSystem Sentence Proof) : Prop :=
  ∃ σ, S.Independent σ

/-- The diagonal stage of an incompleteness argument produces a proof-status fixed point. -/
def HasStatusFixedPoint (S : ProofSystem Sentence Proof) : Prop :=
  ∃ σ, S.StatusFixedPoint σ

/-- The fixed points of the two-coordinate polarity are exactly the independent and inconsistent
fiber shapes. -/
theorem statusFixedPoint_iff_independent_or_inconsistentAt
    (S : ProofSystem Sentence Proof) (σ : Sentence) :
    S.StatusFixedPoint σ ↔ S.Independent σ ∨ S.InconsistentAt σ := by
  classical
  constructor
  · intro h
    by_cases hp : S.Provable σ
    · exact Or.inr ⟨hp, h.mp hp⟩
    · apply Or.inl
      refine ⟨hp, ?_⟩
      intro hr
      exact hp (h.mpr hr)
  · rintro (h | h)
    · constructor
      · intro hp
        exact False.elim (h.1 hp)
      · intro hr
        exact False.elim (h.2 hr)
    · exact ⟨fun _ => h.2, fun _ => h.1⟩

/-- In a consistent system, every proof-status fixed point is independent. -/
theorem independent_of_consistent_statusFixedPoint
    (S : ProofSystem Sentence Proof) {σ : Sentence}
    (hcon : S.Consistent) (hfix : S.StatusFixedPoint σ) :
    S.Independent σ := by
  constructor
  · intro hp
    exact hcon σ hp (hfix.mp hp)
  · intro hr
    exact hcon σ (hfix.mpr hr) hr

/-- Abstract first incompleteness theorem: consistency plus a diagonal proof-status fixed point
forces an independent sentence. -/
theorem incomplete_of_consistent_hasStatusFixedPoint
    (S : ProofSystem Sentence Proof)
    (hcon : S.Consistent) (hdiag : S.HasStatusFixedPoint) :
    S.Incomplete := by
  obtain ⟨σ, hσ⟩ := hdiag
  exact ⟨σ, S.independent_of_consistent_statusFixedPoint hcon hσ⟩

/-- A consistent complete proof system has no proof-status fixed point. -/
theorem no_statusFixedPoint_of_consistent_complete
    (S : ProofSystem Sentence Proof)
    (hcon : S.Consistent) (hcomplete : S.Complete) (σ : Sentence) :
    ¬S.StatusFixedPoint σ := by
  intro hfix
  have hind := S.independent_of_consistent_statusFixedPoint hcon hfix
  rcases hcomplete σ with hp | hr
  · exact hind.1 hp
  · exact hind.2 hr

/-- Consequently, a consistent system with diagonal closure cannot be complete. -/
theorem not_complete_of_consistent_hasStatusFixedPoint
    (S : ProofSystem Sentence Proof)
    (hcon : S.Consistent) (hdiag : S.HasStatusFixedPoint) :
    ¬S.Complete := by
  intro hcomplete
  obtain ⟨σ, hσ⟩ := hdiag
  exact S.no_statusFixedPoint_of_consistent_complete hcon hcomplete σ hσ

/-- A classical Boolean orientation records whether the positive proof fiber is inhabited.
It is intentionally noncomputable: Gödel's applicability additionally requires that the relevant
status predicate be effectively representable inside the system. -/
noncomputable def proofOrientation
    (S : ProofSystem Sentence Proof) (σ : Sentence) : Bool := by
  classical
  exact if S.Provable σ then true else false

@[simp]
theorem proofOrientation_eq_true_iff
    (S : ProofSystem Sentence Proof) (σ : Sentence) :
    S.proofOrientation σ = true ↔ S.Provable σ := by
  classical
  simp [proofOrientation]

@[simp]
theorem proofOrientation_eq_false_iff
    (S : ProofSystem Sentence Proof) (σ : Sentence) :
    S.proofOrientation σ = false ↔ ¬S.Provable σ := by
  classical
  simp [proofOrientation]

/-- Under consistency and completeness, syntactic negation flips the Boolean proof orientation. -/
theorem proofOrientation_neg
    (S : ProofSystem Sentence Proof)
    (hcon : S.Consistent) (hcomplete : S.Complete) (σ : Sentence) :
    S.proofOrientation (S.neg σ) = Bool.not (S.proofOrientation σ) := by
  classical
  by_cases hp : S.Provable σ
  · have hn : ¬S.Provable (S.neg σ) := by
      intro hneg
      exact hcon σ hp hneg
    simp [proofOrientation, hp, hn]
  · have hn : S.Provable (S.neg σ) := by
      rcases hcomplete σ with h | h
      · exact False.elim (hp h)
      · exact h
    simp [proofOrientation, hp, hn]

/-- A sentence-code `d` represents the anti-diagonal of an evaluator when evaluating `d` at every
code has the opposite Boolean status from evaluating that code at itself. -/
def RepresentsAntiDiagonal
    {Code : Type w} (S : ProofSystem Sentence Proof)
    (evaluate : Code → Code → Sentence) : Prop :=
  ∃ d, ∀ x,
    S.proofOrientation (evaluate d x) =
      Bool.not (S.proofOrientation (evaluate x x))

/-- No two-valued status assignment can represent its own anti-diagonal.  Arithmetic
representability plus completeness would attempt exactly this construction. -/
theorem antiDiagonal_not_representable
    {Code : Type w} (S : ProofSystem Sentence Proof)
    (evaluate : Code → Code → Sentence) :
    ¬S.RepresentsAntiDiagonal evaluate := by
  rintro ⟨d, hd⟩
  have h := hd d
  exact bool_not_fixedPointFree (S.proofOrientation (evaluate d d)) h.symm

end ProofSystem
end Incompleteness
end FiberAggregation
