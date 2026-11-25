import WalkDimensions.LocalBesov

/-!
# Nonconstant tests in the energy domain

Regularity on an unbounded proper space supplies compactly supported
nonconstant tests. The forward Besov bound then gives one direction of
the critical exponent identity.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

/-- A regular energy domain on an unbounded space contains a nonconstant
continuous compactly supported function. -/
theorem exists_continuous_compact_nonconstant
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    ∃ (f : E.domain) (u : X → ℝ), Continuous u ∧ HasCompactSupport u ∧
      (f : RealLp m p) =ᵐ[m] u ∧ ¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let v : X → ℝ := fun y ↦ max (1 - dist y x) 0
  have hv : Continuous v := (continuous_const.sub (continuous_id.dist continuous_const)).max continuous_const
  have hvc : HasCompactSupport v := by
    apply HasCompactSupport.intro (isCompact_closedBall x 1)
    intro y hy
    exact max_eq_right (sub_nonpos.mpr (le_of_not_ge hy))
  obtain ⟨u, hu, huc, hmem, δ, hδ, hclose⟩ :=
    E.regular_uniform v hv hvc (1 / 2) (by norm_num)
  let f : E.domain := ⟨continuousLp p u hu huc, hmem⟩
  refine ⟨f, u, hu, huc, MemLp.coeFn_toLp (hu.memLp_of_hasCompactSupport huc), ?_⟩
  have hux : 0 < u x := by
    have h := (abs_le.mp (hclose x)).1
    have hx : v x = 1 := by simp [v]
    rw [hx] at h
    linarith
  rintro ⟨c, hconst⟩
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ tsupport u := by
    by_contra! h
    exact hunbounded (huc.isCompact.isBounded.subset (fun y _ ↦ h y))
  have huy : u y = 0 := notMem_support.mp fun h ↦ hy (subset_closure h)
  have he := Measure.eq_of_ae_eq hconst hu continuous_const
  have hzero : u x = 0 := (congrFun he x).trans ((congrFun he y).symm.trans huy)
  exact hux.ne' hzero

variable [SecondCountableTopology X] [SFinite m]

/-- The lower bound in Lemma 3.2 from Poincaré and regularity. -/
theorem scale_le_criticalBesovExponent {β : ℝ} {Γ : E.domain → Measure X}
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    (hβ : 0 < β) (hvol : VolumeDoubling m) (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ENNReal.ofReal (β / p) ≤ criticalBesovExponent m p := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  obtain ⟨f, u, hu, hc, hfu, hnonconst⟩ := E.exists_continuous_compact_nonconstant hunbounded
  obtain ⟨K, _, hK, hbound⟩ := E.global_besov_bound hvol hPI hΓ
  refine le_criticalBesovExponent (div_pos hβ hp) ⟨hu.memLp_of_hasCompactSupport hc, ?_⟩ hnonconst
  rw [show p * (β / p) = β by field_simp]
  simp_rw [← besovEnergy_congr_ae hfu]
  exact (hbound f).trans_lt (ENNReal.mul_ne_top hK ENNReal.coe_ne_top).lt_top

end WalkDimensions.PEnergy
