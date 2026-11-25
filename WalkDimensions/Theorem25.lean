import WalkDimensions.GammaComparison
import WalkDimensions.PositiveGammaStrictness

/-!
# Theorem 2.5 of arXiv:2611.02422v1
-/

open MeasureTheory Set

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure]

/-- The three comparisons and the exclusive alternatives for the normalized
walk exponent. The Poincaré inequality uses the energy measure constructed
from each given energy form. -/
theorem theorem_2_5 {I : Set ℝ} {d : ℝ} {β : ℝ → ℝ}
    (hvol : AhlforsRegular m d) (hCC : ChainCondition X)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    (_hOpen : IsOpen I) (hI : IsPreconnected I) (hne : I.Nonempty)
    (hwalk : ∀ p ∈ I, 0 < β p ∧ ∃ E : PEnergy m p,
      E.Poincare E.energyMeasure (β p) ∧ E.CapacityUpperBound (β p)) :
    MonotoneOn (gamma d β) I ∧
      (∀ p ∈ I, gamma d β p = 1 → ∀ q ∈ I, gamma d β q = 1) ∧
      (∀ p ∈ I, ∀ q ∈ I, p < q →
        (gamma d β p < 1 ↔ gamma d β q < 1) ∧
          (gamma d β p < 1 → gamma d β p < gamma d β q)) ∧
      Xor (∀ p ∈ I, β p = d + p - 1)
        ((∀ p ∈ I, gamma d β p < 1) ∧ StrictMonoOn (gamma d β) I) := by
  have : Nonempty X := by
    by_contra h
    apply hunbounded
    rw [show (univ : Set X) = ∅ from eq_empty_iff_forall_notMem.mpr fun x _ ↦ h ⟨x⟩]
    exact Bornology.isBounded_empty
  have hMass : ∀ p ∈ I, HasWalkExponent m p (β p) := by
    intro p hp
    obtain ⟨hβ, E, hPI, hcap⟩ := hwalk p hp
    exact ⟨hβ, E, E.energyMeasure, E.energyMeasure_univ, hPI, hcap⟩
  have hp₁ (p : ℝ) (hp : p ∈ I) : 1 < p := (hMass p hp).one_lt
  obtain ⟨hMono, hBelow⟩ := gamma_monoOn_and_strict_below_volume hvol hMass hunbounded
  have hOne (p : ℝ) (hp : p ∈ I) : gamma d β p ≤ 1 :=
    gamma_le_one_of_walkExponent rfl hvol hCC (hMass p hp) hunbounded
  have hEnd (p : ℝ) (hp : p ∈ I) (h : gamma d β p = 1) :
      ∀ q ∈ I, gamma d β q = 1 :=
    gamma_eq_one_on_of_eq_one hvol hCC hMass hI hunbounded hp h
  have hStrict (p : ℝ) (hp : p ∈ I) (q : ℝ) (hq : q ∈ I) (hpq : p < q)
      (hlt : gamma d β p < 1) : gamma d β p < gamma d β q := by
    by_cases h : β p ≤ d
    · exact hBelow p hp q hq hpq h
    have hc : 0 < gamma d β p := div_pos (sub_pos.mpr (lt_of_not_ge h)) (sub_pos.mpr (hp₁ p hp))
    refine (hMono hp hq hpq.le).lt_of_ne ?_
    intro he
    have hpEq : β p - d = (p - 1) * gamma d β p := by
      rw [gamma, mul_comm, div_mul_cancel₀ _ (sub_pos.mpr (hp₁ p hp)).ne']
    have hqEq : β q - d = (q - 1) * gamma d β p := by
      rw [he, gamma, mul_comm, div_mul_cancel₀ _ (sub_pos.mpr (hp₁ q hq)).ne']
    have hdiff : β q - β p = (q - p) * gamma d β p := by
      linear_combination hqEq - hpEq
    obtain ⟨_, E, hPI, hcap⟩ := hwalk p hp
    obtain ⟨hβ', F, hPI', hcap'⟩ := hwalk q hq
    exact E.false_of_shared_normalized_exponent F hpq hvol hβ' hpEq hdiff hc hlt
      hPI hPI' hcap hcap' hunbounded
  have hUpper (p : ℝ) (hp : p ∈ I) : β p ≤ d + p - 1 := by
    have hh := (div_le_iff₀ (sub_pos.mpr (hp₁ p hp))).mp (hOne p hp)
    linarith only [hh]
  refine ⟨hMono, hEnd, fun p hp q hq hpq ↦ ⟨?_, hStrict p hp q hq hpq⟩,
    gamma_dichotomy_of_pairwise hne hp₁ hUpper hEnd hStrict⟩
  constructor
  · intro h
    exact (hOne q hq).lt_of_ne (fun he ↦ h.ne (hEnd q hq he p hp))
  · intro h
    exact (hMono hp hq hpq.le).trans_lt h

end WalkDimensions
