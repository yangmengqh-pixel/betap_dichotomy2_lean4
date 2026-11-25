import WalkDimensions.Exponents
import WalkDimensions.FirstOrderEndpoint
import WalkDimensions.SingularPlateTest

/-!
# Theorem 2.1 of arXiv:2611.02422v1
-/

open MeasureTheory Metric Set

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure]

/-- On the given open interval, the walk exponent either equals the energy
exponent everywhere or has a strictly decreasing ratio greater than one. -/
theorem theorem_2_1 {I : Set ℝ} {β : ℝ → ℝ}
    (hvol : VolumeDoubling m) (hCC : ChainCondition X)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    (_hOpen : IsOpen I) (hI : IsPreconnected I) (hne : I.Nonempty)
    (hwalk : ∀ p ∈ I, 0 < β p ∧ ∃ E : PEnergy m p,
      E.Poincare E.energyMeasure (β p) ∧ E.CapacityUpperBound (β p)) :
    Xor (∀ p ∈ I, β p = p)
      ((∀ p ∈ I, 1 < β p / p) ∧ StrictAntiOn (fun p ↦ β p / p) I) := by
  have : Nonempty X := by
    by_contra h
    apply hunbounded
    rw [show (univ : Set X) = ∅ from eq_empty_iff_forall_notMem.mpr fun x _ ↦ h ⟨x⟩]
    exact Bornology.isBounded_empty
  have hMass : ∀ p ∈ I, HasWalkExponent m p (β p) := by
    intro p hp
    obtain ⟨hβ, E, hPI, hcap⟩ := hwalk p hp
    exact ⟨hβ, E, E.energyMeasure, E.energyMeasure_univ, hPI, hcap⟩
  obtain ⟨hLower, _, hAnti, hCont⟩ := walkExponent_family_comparisons hvol hMass hunbounded
  have hp₁ (p : ℝ) (hp : p ∈ I) : 1 < p := (hMass p hp).one_lt
  have hp₀ (p : ℝ) (hp : p ∈ I) : 0 < p := zero_lt_one.trans (hp₁ p hp)
  have hRight (p : ℝ) (hp : p ∈ I) (he : β p = p) (q : ℝ) (hq : q ∈ I) (hpq : p ≤ q) :
      β q = q := by
    have h := hAnti hp hq hpq
    change β q / q ≤ β p / p at h
    rw [he, div_self (hp₀ p hp).ne'] at h
    exact le_antisymm (by simpa only [one_mul] using (div_le_iff₀ (hp₀ q hq)).mp h) (hLower q hq)
  let J : Set I := {p | β p.val = p.val}
  have hJc : IsClosed J :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hCont) continuous_subtypeVal
  have hJo : IsOpen J := by
    apply Metric.isOpen_iff.mpr
    intro p hp
    have he : β p.val = p.val := hp
    obtain ⟨_, E, hPI, hcap⟩ := hwalk p.val p.property
    rw [he] at hPI hcap
    have hSlope := E.slopePoincare_of_firstOrder hvol hPI hcap
    obtain ⟨C₀, A₀, hC₀, hA₀, hConn⟩ := hSlope.exists_continuousConnectivity E.one_lt.le hvol hCC
    obtain ⟨ε, hε, C, A, hC, _, hLocal⟩ :=
      (hConn.lowerSemicontinuousConnectivity (zero_le_one.trans E.one_lt.le)).exists_lower_exponents
        E.one_lt hC₀ hA₀ hvol hCC
    refine ⟨ε, hε, fun q hq ↦ ?_⟩
    change β q.val = q.val
    by_cases hL : q.val < p.val
    · have hNear : q.val ∈ Ioo (max 1 (p.val - ε)) p.val := by
        refine ⟨max_lt (hp₁ q.val q.property) ?_, hL⟩
        have h : |q.val - p.val| < ε := by
          simpa only [Subtype.dist_eq, Real.dist_eq] using mem_ball.mp hq
        linarith only [(abs_lt.mp h).1]
      obtain ⟨hβ, F, hPI', hcap'⟩ := hwalk q.val q.property
      exact F.walkExponent_eq_of_connectivity hβ hC hvol hPI' hcap' hunbounded (hLocal q.val hNear)
    · exact hRight p.val p.property he q.val q.property (le_of_not_gt hL)
  have hEnd (p : ℝ) (hp : p ∈ I) (he : β p = p) : ∀ q ∈ I, β q = q := by
    let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI
    have hJ : J = univ := IsClopen.eq_univ ⟨hJc, hJo⟩ ⟨⟨p, hp⟩, he⟩
    intro q hq
    change (⟨q, hq⟩ : I) ∈ J
    rw [hJ]
    exact mem_univ _
  refine beta_ratio_dichotomy_of_pairwise hne hp₀ hLower hEnd hAnti ?_
  intro p hp q hq hpq hEq
  by_contra hn
  have hneq : q < β q := (hLower q hq).lt_of_ne (fun h ↦ hn (hEnd q hq h.symm p hp))
  obtain ⟨hβp, E, hPIp, hcapP⟩ := hwalk p hp
  obtain ⟨_, F, hPIq, hcapQ⟩ := hwalk q hq
  exact (walkExponent_ratio_lt_of_superlinear E F hpq hvol hCC hβp hneq hPIp hPIq hcapP hcapQ
    hunbounded).ne hEq

end WalkDimensions
