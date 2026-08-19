import FiberAggregation.Core

/-!
# A Lawvere-style diagonal obstruction

A self-coding rule that represents every observable profile forces every endomorphism of the
observable aggregate to have a fixed point. Hence a fixed-point-free polarity, such as Boolean
negation, rules out complete self-encoding. This is a conditional obstruction, not a proof that a
universal aggregate is impossible in every weaker language.
-/

universe u v

namespace FiberAggregation

/-- Every profile `A → Ω` is represented by one code in `A`. -/
def WeaklyPointSurjective {A : Type u} {Ω : Type v} (encode : A → A → Ω) : Prop :=
  ∀ profile : A → Ω, ∃ code : A, encode code = profile

/-- Lawvere's fixed-point argument in elementary function form. -/
theorem lawvere_fixedPoint {A : Type u} {Ω : Type v}
    (encode : A → A → Ω) (hencode : WeaklyPointSurjective encode)
    (polarity : Ω → Ω) :
    ∃ value : Ω, polarity value = value := by
  let diagonal : A → Ω := fun code => polarity (encode code code)
  obtain ⟨code, hcode⟩ := hencode diagonal
  refine ⟨encode code code, ?_⟩
  have hdiag : encode code code = diagonal code := congrFun hcode code
  simpa [diagonal] using hdiag.symm

/-- Complete self-encoding is impossible in the presence of a fixed-point-free polarity. -/
theorem no_complete_self_encoding_of_fixedPointFree {A : Type u} {Ω : Type v}
    (encode : A → A → Ω) (polarity : Ω → Ω)
    (hpolarity : ∀ value, polarity value ≠ value) :
    ¬ WeaklyPointSurjective encode := by
  intro hencode
  obtain ⟨value, hvalue⟩ := lawvere_fixedPoint encode hencode polarity
  exact hpolarity value hvalue

/-- Boolean negation has no fixed point. -/
theorem bool_not_fixedPointFree : ∀ value : Bool, Bool.not value ≠ value := by
  intro value
  cases value <;> decide

/-- Therefore no Boolean-valued self-evaluation table represents every Boolean profile. -/
theorem no_complete_bool_self_encoding {A : Type u} (encode : A → A → Bool) :
    ¬ WeaklyPointSurjective encode :=
  no_complete_self_encoding_of_fixedPointFree encode Bool.not bool_not_fixedPointFree

end FiberAggregation
