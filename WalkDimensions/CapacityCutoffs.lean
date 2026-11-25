import WalkDimensions.PEnergy

/-!
# Cutoff functions from the capacity bound

The Markov property truncates admissible functions to the unit interval
while preserving both plate conditions and the energy estimate.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem capacity_mono {S₁ S₂ T₁ T₂ : Set X} (h₁ : S₁ ⊆ T₁) (h₂ : S₂ ⊆ T₂) :
    E.capacity S₁ S₂ ≤ E.capacity T₁ T₂ := by
  refine le_iInf fun f ↦ le_iInf fun hf ↦ ?_
  obtain ⟨u, hu, U₁, U₂, ho₁, ho₂, hT₁, hT₂, hval₁, hval₂⟩ := hf
  have hs : E.CapacityAdmissible S₁ S₂ f :=
    ⟨u, hu, U₁, U₂, ho₁, ho₂, h₁.trans hT₁, h₂.trans hT₂, hval₁, hval₂⟩
  exact (iInf_le _ f).trans (iInf_le _ hs)

/-- An admissible cutoff with values in the unit interval and with a
measurable representative attaining its boundary values pointwise. -/
theorem exists_measurable_unit_cutoff_of_capacity_lt {A₁ A₂ : Set X} {b : ℝ≥0∞}
    (hb : E.capacity A₁ A₂ < b) :
    ∃ (f : E.domain) (u : X → ℝ) (U₁ U₂ : Set X),
      (E.energy f : ℝ≥0∞) < b ∧ (f : RealLp m p) =ᵐ[m] u ∧ Measurable u ∧
      (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ A₁ ⊆ U₁ ∧ A₂ ⊆ U₂ ∧
      EqOn u (fun _ ↦ 1) U₁ ∧ EqOn u (fun _ ↦ 0) U₂ := by
  classical
  obtain ⟨f, hadm, hf⟩ := E.exists_admissible_lt_of_capacity_lt hb
  obtain ⟨v, hv, U₁, U₂, hU₁, hU₂, hA₁, hA₂, hv₁, hv₂⟩ := hadm
  let φ : ℝ → ℝ := fun x ↦ min (max x 0) 1
  have hφ : LipschitzWith 1 φ := (LipschitzWith.id.max_const _).min_const _
  have hφ₀ : φ 0 = 0 := by norm_num [φ]
  have hφ₁ : φ 1 = 1 := by norm_num [φ]
  have hφrange (x : ℝ) : φ x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  obtain ⟨g, hg, hEg⟩ := E.markov φ hφ hφ₀ f
  have hgv : (g : RealLp m p) =ᵐ[m] fun x ↦ φ (v x) :=
    hg.trans (hv.mono fun x hx ↦ congrArg φ hx)
  have hgm : AEMeasurable (g : RealLp m p) m := (Lp.aestronglyMeasurable _).aemeasurable
  let w := hgm.mk (g : RealLp m p)
  have hw : (g : RealLp m p) =ᵐ[m] w := hgm.ae_eq_mk
  let u : X → ℝ := U₁.piecewise (fun _ ↦ 1) (U₂.piecewise (fun _ ↦ 0) (φ ∘ w))
  refine ⟨g, u, U₁, U₂, (ENNReal.coe_le_coe.mpr hEg).trans_lt hf, ?_, ?_, ?_,
    hU₁, hU₂, hA₁, hA₂, ?_, ?_⟩
  · filter_upwards [hgv, hw] with x hx hwx
    by_cases hx₁ : x ∈ U₁
    · rw [show u x = 1 from piecewise_eq_of_mem _ _ _ hx₁]
      simpa only [hv₁ hx₁, hφ₁] using hx
    · by_cases hx₂ : x ∈ U₂
      · show (g : RealLp m p) x = u x
        dsimp only [u]
        rw [piecewise_eq_of_notMem _ _ _ hx₁, piecewise_eq_of_mem _ _ _ hx₂]
        simpa only [hv₂ hx₂, hφ₀] using hx
      · dsimp only [u]
        rw [piecewise_eq_of_notMem _ _ _ hx₁, piecewise_eq_of_notMem _ _ _ hx₂]
        have hvx : φ (v x) = w x := hx.symm.trans hwx
        have hwx' := hφrange (v x)
        rw [hvx] at hwx'
        have hwφ : φ (w x) = w x :=
          (show min (max (w x) 0) 1 = w x by
            rw [max_eq_left hwx'.1, min_eq_left hwx'.2])
        exact hwx.trans hwφ.symm
  · exact measurable_const.piecewise hU₁.measurableSet
      (measurable_const.piecewise hU₂.measurableSet (hφ.continuous.measurable.comp hgm.measurable_mk))
  · intro x
    by_cases hx₁ : x ∈ U₁
    · simpa only [u, piecewise_eq_of_mem _ _ _ hx₁] using (right_mem_Icc.mpr zero_le_one)
    · by_cases hx₂ : x ∈ U₂
      · simpa only [u, piecewise_eq_of_notMem _ _ _ hx₁, piecewise_eq_of_mem _ _ _ hx₂]
          using (left_mem_Icc.mpr zero_le_one)
      · simpa only [u, piecewise_eq_of_notMem _ _ _ hx₁, piecewise_eq_of_notMem _ _ _ hx₂, Function.comp_apply]
          using hφrange (w x)
  · intro x hx
    exact piecewise_eq_of_mem _ _ _ hx
  · intro x hx
    have hx₁ : x ∉ U₁ := fun hm ↦ one_ne_zero ((hv₁ hm).symm.trans (hv₂ hx))
    change u x = 0
    rw [show u x = U₂.piecewise (fun _ ↦ 0) (φ ∘ w) x from piecewise_eq_of_notMem _ _ _ hx₁,
      piecewise_eq_of_mem _ _ _ hx]

/-- Pointwise ball cutoffs from the capacity upper bound. The radius dilation
is the one in that bound and the energy constant can be doubled. -/
theorem exists_measurable_ball_cutoff [ProperSpace X] [m.IsOpenPosMeasure] {β : ℝ}
    (hcap : E.CapacityUpperBound β) :
    ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ (x : X) (r : ℝ), 0 < r →
      ∃ (f : E.domain) (u : X → ℝ),
        (f : RealLp m p) =ᵐ[m] u ∧ Measurable u ∧
        HasCompactSupport u ∧ (∀ y, u y ∈ Icc (0 : ℝ) 1) ∧
        EqOn u (fun _ ↦ 1) (ball x r) ∧ EqOn u (fun _ ↦ 0) (ball x (A * r))ᶜ ∧
        (E.energy f : ℝ≥0∞) ≤ ENNReal.ofReal (C * r ^ (-β)) * m (ball x r) := by
  obtain ⟨C, A, hC, hA, hcap⟩ := hcap
  refine ⟨2 * C, A, by positivity, hA, fun x r hr ↦ ?_⟩
  let b := ENNReal.ofReal (C * r ^ (-β)) * m (ball x r)
  have hb0 : 0 < b := pos_iff_ne_zero.mpr (mul_ne_zero
    (ENNReal.ofReal_pos.mpr (mul_pos hC (Real.rpow_pos_of_pos hr _))).ne'
    (measure_ball_pos m x hr).ne')
  have hbfin : b ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top
  have hbb : b < b + b := by
    apply (ENNReal.toReal_lt_toReal hbfin (ENNReal.add_ne_top.mpr ⟨hbfin, hbfin⟩)).1
    rw [ENNReal.toReal_add hbfin hbfin]
    exact lt_add_of_pos_right _ (ENNReal.toReal_pos hb0.ne' hbfin)
  obtain ⟨f, u, U₁, U₂, hE, hfu, hu, hrange, _, _, h₁, h₂, hu₁, hu₂⟩ :=
    E.exists_measurable_unit_cutoff_of_capacity_lt ((hcap x r hr).trans_lt hbb)
  have heq : b + b = ENNReal.ofReal ((2 * C) * r ^ (-β)) * m (ball x r) := by
    dsimp only [b]
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity : 0 ≤ C * r ^ (-β)) (by positivity)]
    congr 2
    ring
  have ho : EqOn u (fun _ ↦ 0) (ball x (A * r))ᶜ := hu₂.mono h₂
  have hc : HasCompactSupport u := by
    apply HasCompactSupport.intro (isCompact_closedBall x (A * r))
    intro y hy
    exact ho (fun hh ↦ hy (ball_subset_closedBall hh))
  exact ⟨f, u, hfu, hu, hc, hrange, hu₁.mono h₁, ho, hE.le.trans_eq heq⟩

end WalkDimensions.PEnergy
