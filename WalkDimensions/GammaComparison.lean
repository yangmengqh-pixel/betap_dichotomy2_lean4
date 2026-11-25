import WalkDimensions.EndpointPropagation
import WalkDimensions.SupercriticalComparison
import WalkDimensions.WalkExponentFamily
import Mathlib.Topology.Connected.Clopen

/-!
# Monotonicity and upper endpoint for the normalized walk exponent
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [SFinite m] [m.Regular] [m.IsOpenPosMeasure]

theorem gamma_monoOn_and_strict_below_volume {I : Set ℝ} {d : ℝ} {β : ℝ → ℝ}
    (hvol : AhlforsRegular m d) (hwalk : ∀ p ∈ I, HasWalkExponent m p (β p))
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    MonotoneOn (gamma d β) I ∧
      ∀ p ∈ I, ∀ q ∈ I, p < q → β p ≤ d → gamma d β p < gamma d β q := by
  obtain ⟨_, hmono, _, _⟩ := walkExponent_family_comparisons hvol.volumeDoubling hwalk hunbounded
  have hstrict (p : ℝ) (hp : p ∈ I) (q : ℝ) (hq : q ∈ I) (hpq : p < q) (hβp : β p ≤ d) :=
    gamma_lt_gamma_of_beta_le_dimension (hwalk p hp).one_lt hpq (hmono hp hq hpq) hβp
  refine ⟨?_, hstrict⟩
  intro p hp q hq hpq
  rcases hpq.lt_or_eq with hpq | rfl
  · by_cases hβp : β p ≤ d
    · exact (hstrict p hp q hq hpq hβp).le
    · have hd := lt_of_not_ge hβp
      obtain ⟨_, Ep, Γp, hΓp, hPIp, hcapP⟩ := hwalk p hp
      obtain ⟨_, Eq, Γq, hΓq, hPIq, hcapQ⟩ := hwalk q hq
      exact gamma_le_gamma_of_supercritical hvol hpq hd (hd.trans (hmono hp hq hpq))
        Ep Eq hΓp hΓq hPIp hPIq hcapP hcapQ hunbounded
  · exact le_rfl

omit [SFinite m] in
theorem gamma_le_one_of_walkExponent {d p βp : ℝ} {β : ℝ → ℝ} (heq : β p = βp)
    (hvol : AhlforsRegular m d) (hCC : ChainCondition X) (hwalk : HasWalkExponent m p βp)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    gamma d β p ≤ 1 := by
  have hp := hwalk.one_lt
  apply gamma_le_one hp
  rw [heq]
  by_cases hβp : βp ≤ d
  · linarith
  · obtain ⟨_, E, Γ, hΓ, hPI, hcap⟩ := hwalk
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy⟩ : ∃ y : X, y ∉ closedBall x 1 := by
      by_contra! h
      exact hunbounded ((isCompact_closedBall x 1).isBounded.subset fun y _ ↦ h y)
    have hxy : x ≠ y := by
      intro he
      exact hy (he ▸ mem_closedBall_self (by norm_num))
    exact E.walkExponent_le_volume_add_of_supercritical hvol (lt_of_not_ge hβp)
      hPI hΓ hcap hCC hxy

theorem gamma_eq_one_on_of_eq_one {I : Set ℝ} {d : ℝ} {β : ℝ → ℝ}
    (hvol : AhlforsRegular m d) (hCC : ChainCondition X)
    (hwalk : ∀ p ∈ I, HasWalkExponent m p (β p)) (hI : IsPreconnected I)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) {p : ℝ}
    (hp : p ∈ I) (hpγ : gamma d β p = 1) :
    ∀ q ∈ I, gamma d β q = 1 := by
  obtain ⟨_, _, _, hcont⟩ := walkExponent_family_comparisons hvol.volumeDoubling hwalk hunbounded
  have hpβ := (gamma_eq_one_iff (hwalk p hp).one_lt).mp hpγ
  have hpos (q : ℝ) (hq : q ∈ I) : d < β q ↔ β q = d + q - 1 := by
    have hq₀ := (hwalk q hq).one_lt
    refine ⟨fun hqβ ↦ ?_, fun h ↦ by linarith⟩
    obtain ⟨_, Ep, Γp, hΓp, hPIp, hcapP⟩ := hwalk p hp
    obtain ⟨_, Eq, Γq, hΓq, hPIq, hcapQ⟩ := hwalk q hq
    have hEq := upperEndpoint_eq_of_supercritical hvol hCC Ep Eq (by linarith) hqβ
      hPIp hPIq hΓp hΓq hcapP hcapQ hunbounded
    linarith
  let J : Set I := {q | d < β q}
  have hJopen : IsOpen J := isOpen_Ioi.preimage (continuousOn_iff_continuous_domRestrict.mp hcont)
  have hJclosed : IsClosed J := by
    have hJ : J = {q : I | β q = d + q - 1} := Set.ext fun q ↦ hpos q q.property
    rw [hJ]
    exact isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hcont)
      ((continuous_const.add continuous_subtypeVal).sub continuous_const)
  have hJne : J.Nonempty := ⟨⟨p, hp⟩, (hpos p hp).2 hpβ⟩
  let : PreconnectedSpace I := Subtype.preconnectedSpace hI
  have hall : J = univ := IsClopen.eq_univ ⟨hJclosed, hJopen⟩ hJne
  intro q hq
  apply (gamma_eq_one_iff (hwalk q hq).one_lt).mpr
  apply (hpos q hq).mp
  exact show (⟨q, hq⟩ : I) ∈ J from hall.symm ▸ mem_univ _

end WalkDimensions
