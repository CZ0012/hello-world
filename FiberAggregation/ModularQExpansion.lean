import FiberAggregation.Core
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The q-expansion principle as thin fibers

For a positive strict period, the q-expansion of a modular form determines the form. In the
fiber–aggregation language, the q-expansion rule is injective, so every one of its fibers is
subsingleton; every fiber over an actual modular form is therefore determinate.
-/

namespace FiberAggregation
namespace ModularAnalysis

open Complex UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

noncomputable section

/-- The q-expansion as an observation rule on modular forms of fixed weight. -/
def qExpansionRule (Γ : Subgroup (GL (Fin 2) ℝ)) (h : ℝ) (k : ℤ) :
    ModularForm Γ k → PowerSeries ℂ :=
  fun f => qExpansion h f

/-- The q-expansion principle: the observation rule is injective. -/
theorem qExpansionRule_injective
    {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {k : ℤ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Function.Injective (qExpansionRule Γ h k) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (ModularForm.qExpansion_eq_zero_iff hh hΓ (f - g)).mp
  rw [ModularForm.qExpansion_sub hh hΓ f g]
  change qExpansionRule Γ h k f - qExpansionRule Γ h k g = 0
  rw [hfg, sub_self]

/-- The aggregate of modular forms with a prescribed q-expansion. -/
def QExpansionFiber (Γ : Subgroup (GL (Fin 2) ℝ)) (h : ℝ) (k : ℤ)
    (q : PowerSeries ℂ) : Type :=
  Fiber (qExpansionRule Γ h k) q

/-- Every q-expansion fiber is subsingleton. -/
theorem qExpansionFiber_subsingleton
    {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {k : ℤ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (q : PowerSeries ℂ) :
    Subsingleton (QExpansionFiber Γ h k q) :=
  fiber_subsingleton_of_injective (qExpansionRule_injective hh hΓ) q

/-- The q-expansion fiber over an actual modular form is determinate. -/
theorem qExpansionFiber_determinate
    {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {k : ℤ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) :
    Determinate (QExpansionFiber Γ h k (qExpansionRule Γ h k f)) := by
  constructor
  · exact ⟨⟨f, rfl⟩⟩
  · exact qExpansionFiber_subsingleton hh hΓ _

end
end ModularAnalysis
end FiberAggregation
