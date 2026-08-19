import FiberAggregation.Core
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Modular forms through equalizer fibers

The slash-invariance condition is an equalizer fiber of two rules: the slash-action profile and the
constant profile.  Holomorphy and cusp conditions are further predicates on this structural fiber.
-/

namespace FiberAggregation
namespace ModularAnalysis

open Complex UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- The complete slash-action profile of a function. -/
def slashProfile (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) (f : ℍ → ℂ) :
    Γ → (ℍ → ℂ) :=
  fun γ => f ∣[k] (γ : GL (Fin 2) ℝ)

/-- The constant profile used to express invariance as an equalizer. -/
def constantProfile (Γ : Subgroup (GL (Fin 2) ℝ)) (f : ℍ → ℂ) :
    Γ → (ℍ → ℂ) :=
  fun _ => f

/-- Functions invariant under the slash action, represented as an equalizer fiber. -/
def SlashInvariantFiber (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) : Type :=
  EqFiber (slashProfile Γ k) (constantProfile Γ)

/-- The equalizer-fiber presentation agrees with mathlib's bundled slash-invariant forms. -/
def slashInvariantFormEquiv (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    SlashInvariantForm Γ k ≃ SlashInvariantFiber Γ k where
  toFun f :=
    ⟨(f : ℍ → ℂ), by
      funext γ
      change ((f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) = (f : ℍ → ℂ)
      exact f.slash_action_eq' γ.1 γ.2⟩
  invFun f :=
    { toFun := f.1
      slash_action_eq' := by
        intro γ hγ
        have h := congrFun f.2 (⟨γ, hγ⟩ : Γ)
        simpa [SlashInvariantFiber, EqFiber, slashProfile, constantProfile] using h }
  left_inv := by
    intro f
    apply SlashInvariantForm.ext
    intro z
    rfl
  right_inv := by
    intro f
    apply Subtype.ext
    rfl

/-- With `-1` in the determinant-one group, odd-weight modular forms form a determinate aggregate:
the only point is the zero form. -/
theorem oddWeightDeterminate
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne]
    (h_neg_one : -1 ∈ Γ) (hk : Odd k) :
    Determinate (ModularForm Γ k) := by
  constructor
  · exact ⟨0⟩
  · constructor
    intro f g
    rw [ModularForm.eq_zero_of_neg_one_mem h_neg_one hk f,
      ModularForm.eq_zero_of_neg_one_mem h_neg_one hk g]

end ModularAnalysis
end FiberAggregation
