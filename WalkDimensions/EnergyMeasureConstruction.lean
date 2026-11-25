import WalkDimensions.EnergyMeasureRoot
import WalkDimensions.EnergyMeasureLocality
import WalkDimensions.UniformMeasureLimit

/-!
# The canonical energy measure on the full domain

The local roots extend as seminorms. Their powers give a measure because
the measures of graph approximants converge uniformly on Borel sets.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} (E : PEnergy μ p)

theorem abs_energyMeasureRoot_sub_le {A : Set X} (hA : MeasurableSet A) (f g : E.domain) :
    |E.energyMeasureRoot A hA f - E.energyMeasureRoot A hA g| ≤ E.rootSeminorm (f - g) := by
  let N := E.energyMeasureRoot A hA
  have h₁ := N.add_le' (f - g) g
  have h₂ := N.add_le' (-(f - g)) f
  change N (f - g + g) ≤ N (f - g) + N g at h₁
  change N (-(f - g) + f) ≤ N (-(f - g)) + N f at h₂
  rw [sub_add_cancel] at h₁
  rw [neg_sub, sub_add_cancel] at h₂
  rw [show N (g - f) = N (f - g) by rw [← neg_sub f g, map_neg_eq_map]] at h₂
  apply le_trans _ (E.energyMeasureRoot_le A hA (f - g))
  exact abs_le.mpr ⟨by linarith only [h₂], by linarith only [h₁]⟩

private noncomputable def energyMeasureValue (f : E.domain) (A : Set X) : ℝ := by
  classical
  exact if hA : MeasurableSet A then (E.energyMeasureRoot A hA f) ^ p else 0

private theorem energyMeasureValue_eq (f : E.domain) {A : Set X} (hA : MeasurableSet A) :
    E.energyMeasureValue f A = (E.energyMeasureRoot A hA f) ^ p := by
  unfold energyMeasureValue
  exact dite_eq_left hA

omit [LocallyCompactSpace X] in
theorem exists_core_graph_approximation (f : E.domain) :
    ∃ g : ℕ → E.CompactCore,
      Tendsto (fun n ↦ E.graphSeminorm ((g n).domainElement - f)) atTop (𝓝 0) := by
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  choose v hv hc hmem hD using fun n ↦ E.regular_graph f (ε n) (hε n)
  let g (n : ℕ) : E.CompactCore := ⟨⟨continuousLp p (v n) (hv n) (hc n), hmem n⟩,
    v n, MemLp.coeFn_toLp ((hv n).memLp_of_hasCompactSupport (hc n)), hv n, hc n⟩
  exact ⟨g, squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ (hD n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat⟩

private theorem exists_energyMeasure (f : E.domain) :
    ∃ Γ : Measure X, ∀ A, MeasurableSet A → Γ A = ENNReal.ofReal (E.energyMeasureValue f A) := by
  obtain ⟨g, hg⟩ := E.exists_core_graph_approximation f
  have hg' : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun _ ↦ E.rootSeminorm_le_graphSeminorm _) hg
  apply exists_measure_of_uniform_real_limit (fun n ↦ (g n).coreEnergyMeasure)
  · intro A hA
    rw [E.energyMeasureValue_eq f hA]
    exact Real.rpow_nonneg (apply_nonneg _ _) _
  · intro ε hε
    let C := E.rootSeminorm f + 1
    have hCC : UniformContinuousOn (fun t : ℝ ↦ t ^ p) (Icc 0 C) :=
      isCompact_Icc.uniformContinuousOn_of_continuous
        (Real.continuous_rpow_const (zero_lt_one.trans E.one_lt).le).continuousOn
    obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp hCC ε hε
    filter_upwards [hg'.eventually_lt_const (lt_min hδ zero_lt_one)] with n hn
    intro A hA
    let N := E.energyMeasureRoot A hA
    have hN : N f ∈ Icc (0 : ℝ) C := ⟨apply_nonneg N _, (E.energyMeasureRoot_le A hA f).trans
      (le_add_of_nonneg_right zero_le_one)⟩
    have hdiff := E.abs_energyMeasureRoot_sub_le hA (g n).domainElement f
    change |N (g n).domainElement - N f| ≤ _ at hdiff
    have hB : N (g n).domainElement ∈ Icc (0 : ℝ) C := by
      refine ⟨apply_nonneg N _, ?_⟩
      have h := ((le_abs_self _).trans hdiff).trans_lt (hn.trans_le (min_le_right _ _))
      dsimp only [C]
      linarith only [h, E.energyMeasureRoot_le A hA f]
    have hr : dist (N (g n).domainElement) (N f) < δ := by
      rw [Real.dist_eq]
      exact hdiff.trans_lt (hn.trans_le (min_le_left _ _))
    have hh := hbound _ hB _ hN hr
    rw [Real.dist_eq] at hh
    have hPow : N (g n).domainElement ^ p = ((g n).coreEnergyMeasure A).toReal := by
      change E.energyMeasureRoot A hA (g n).domainElement ^ p = _
      rw [E.energyMeasureRoot_apply_core A hA, CompactCore.localEnergyRoot,
        ← Real.rpow_mul ENNReal.toReal_nonneg,
        inv_mul_cancel₀ (zero_lt_one.trans E.one_lt).ne', Real.rpow_one]
    rw [E.energyMeasureValue_eq f hA]
    rw [hPow] at hh
    exact hh

/-- The finite Borel energy measure associated with an energy-domain element. -/
noncomputable def energyMeasure (f : E.domain) : Measure X := (E.exists_energyMeasure f).choose

theorem energyMeasure_apply (f : E.domain) {A : Set X} (hA : MeasurableSet A) :
    E.energyMeasure f A = ENNReal.ofReal ((E.energyMeasureRoot A hA f) ^ p) := by
  exact ((E.exists_energyMeasure f).choose_spec A hA).trans
    (congrArg ENNReal.ofReal (E.energyMeasureValue_eq f hA))

theorem energyMeasure_univ (f : E.domain) : E.energyMeasure f univ = (E.energy f : ℝ≥0∞) := by
  rw [E.energyMeasure_apply f MeasurableSet.univ, E.energyMeasureRoot_univ,
    ← E.energy_eq_root_rpow, ENNReal.ofReal_coe_nnreal]

instance (f : E.domain) : IsFiniteMeasure (E.energyMeasure f) :=
  ⟨by rw [E.energyMeasure_univ]; exact ENNReal.coe_lt_top⟩

instance [SigmaCompactSpace X] (f : E.domain) : (E.energyMeasure f).Regular := inferInstance

theorem energyMeasure_core (f : E.CompactCore) : E.energyMeasure f.domainElement = f.coreEnergyMeasure := by
  ext A hA
  rw [E.energyMeasure_apply f.domainElement hA, E.energyMeasureRoot_apply_core A hA,
    CompactCore.localEnergyRoot, ← Real.rpow_mul ENNReal.toReal_nonneg,
    inv_mul_cancel₀ (zero_lt_one.trans E.one_lt).ne', Real.rpow_one,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

noncomputable def energyMeasureLaws : E.EnergyMeasureLaws E.energyMeasure where
  total_mass := E.energyMeasure_univ
  root := E.energyMeasureRoot
  root_apply A hA f := by
    rw [measureReal_def, E.energyMeasure_apply f hA,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (apply_nonneg _ _) _),
      ← Real.rpow_mul (apply_nonneg _ _),
      mul_inv_cancel₀ (zero_lt_one.trans E.one_lt).ne', Real.rpow_one]
  local_const := by
    rintro f g u v hu hv huC hvC hfu hgv A hA ⟨a, ha⟩
    let F : E.CompactCore := ⟨f, u, hfu, hu, huC⟩
    let G : E.CompactCore := ⟨g, v, hgv, hv, hvC⟩
    change E.energyMeasure F.domainElement A = E.energyMeasure G.domainElement A
    rw [E.energyMeasure_core F, E.energyMeasure_core G]
    exact F.coreEnergyMeasure_eq_of_eqOn_sub_const G hA ha

end WalkDimensions.PEnergy
