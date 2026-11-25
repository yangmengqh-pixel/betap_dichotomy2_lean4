import WalkDimensions.WalkExponent

/-!
# Walk-exponent families on a parameter set
-/

open MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X}

section

variable [IsFiniteMeasureOnCompacts m]

/-- A walk exponent is witnessed by an energy, its Poincaré measure with
the total-mass law, and the ball capacity bound. -/
def HasWalkExponent (m : Measure X) [IsFiniteMeasureOnCompacts m] (p β : ℝ) : Prop :=
  0 < β ∧ ∃ (E : PEnergy m p) (Γ : E.domain → Measure X),
    (∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) ∧ E.Poincare Γ β ∧ E.CapacityUpperBound β

theorem HasWalkExponent.one_lt {p β : ℝ} (h : HasWalkExponent m p β) : 1 < p := by
  obtain ⟨_, E, _⟩ := h
  exact E.one_lt

end

theorem continuousOn_of_mono_ratio_antitone {I : Set ℝ} {β : ℝ → ℝ}
    (hpos : ∀ p ∈ I, 0 < p) (hβ : ∀ p ∈ I, 0 ≤ β p)
    (hmono : MonotoneOn β I) (hanti : AntitoneOn (fun p ↦ β p / p) I) :
    ContinuousOn β I := by
  intro p hp
  have hp₀ := hpos p hp
  let C := β p / p
  have hC : 0 ≤ C := div_nonneg (hβ p hp) hp₀.le
  have hCeq : C * p = β p := div_mul_cancel₀ _ hp₀.ne'
  have hbound (q : ℝ) (hq : q ∈ I) : |β q - β p| ≤ C * |q - p| := by
    rcases le_total p q with hpq | hqp
    · have hmono' := hmono hp hq hpq
      have hanti' := (div_le_iff₀ (hpos q hq)).mp (hanti hp hq hpq)
      rw [abs_of_nonneg (sub_nonneg.mpr hmono'), abs_of_nonneg (sub_nonneg.mpr hpq),
        mul_sub, hCeq]
      exact sub_le_sub_right hanti' _
    · have hmono' := hmono hq hp hqp
      have hanti' := (le_div_iff₀ (hpos q hq)).mp (hanti hq hp hqp)
      rw [abs_of_nonpos (sub_nonpos.mpr hmono'), abs_of_nonpos (sub_nonpos.mpr hqp),
        neg_sub, neg_sub, mul_sub, hCeq]
      exact sub_le_sub_left hanti' _
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨δ, hδ, fun q hq hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hscale := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hdist
  have hcomp : C * |q - p| ≤ |q - p| * (C + 1) := by
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg _)
  exact ((hbound q hq).trans hcomp).trans_lt hscale

variable [Nonempty X] [ProperSpace X] [SecondCountableTopology X] [SFinite m]
  [m.Regular] [m.IsOpenPosMeasure]

theorem walkExponent_family_comparisons {I : Set ℝ} {β : ℝ → ℝ}
    (hvol : VolumeDoubling m) (hwalk : ∀ p ∈ I, HasWalkExponent m p (β p))
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    (∀ p ∈ I, p ≤ β p) ∧ StrictMonoOn β I ∧
      AntitoneOn (fun p ↦ β p / p) I ∧ ContinuousOn β I := by
  have hlower (p : ℝ) (hp : p ∈ I) : p ≤ β p := by
    obtain ⟨hβ, E, Γ, hΓ, hPI, hcap⟩ := hwalk p hp
    exact E.exponent_le_walkExponent hvol hβ hΓ hPI hcap hunbounded
  have hcomp (p q : ℝ) (hp : p ∈ I) (hq : q ∈ I) (hpq : p < q) :
      β p < β q ∧ β q / q ≤ β p / p := by
    obtain ⟨hβp, Ep, Γp, hΓp, hPIp, hcapP⟩ := hwalk p hp
    obtain ⟨hβq, Eq, Γq, hΓq, hPIq, hcapQ⟩ := hwalk q hq
    exact Ep.walkExponent_comparisons Eq hpq hvol hβp hβq
      hΓp hΓq hPIp hPIq hcapP hcapQ hunbounded
  have hmono : StrictMonoOn β I := fun p hp q hq hpq ↦ (hcomp p q hp hq hpq).1
  have hanti : AntitoneOn (fun p ↦ β p / p) I := by
    intro p hp q hq hpq
    rcases hpq.lt_or_eq with h | rfl
    · exact (hcomp p q hp hq h).2
    · exact le_rfl
  exact ⟨hlower, hmono, hanti, continuousOn_of_mono_ratio_antitone
    (fun p hp ↦ zero_lt_one.trans (hwalk p hp).one_lt)
    (fun p hp ↦ (hwalk p hp).1.le) hmono.monotoneOn hanti⟩

end WalkDimensions
