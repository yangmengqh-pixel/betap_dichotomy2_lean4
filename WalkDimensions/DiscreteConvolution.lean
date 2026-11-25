import WalkDimensions.AverageOscillation
import WalkDimensions.CutoffPartition
import WalkDimensions.Besov

/-!
# Discrete convolutions in the energy domain

Averaging on the balls of a compact cover and taking the resulting linear
combination of the capacity weights gives a uniform approximation.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] [ProperSpace X] [m.IsOpenPosMeasure]
  {p : ℝ} (E : PEnergy m p)

omit [IsFiniteMeasureOnCompacts m] [ProperSpace X] [m.IsOpenPosMeasure] in
theorem tsupport_discrete_convolution_subset {u : X → ℝ} {t : Finset X}
    {A r : ℝ} {w : X → X → ℝ}
    (hw : ∀ z, EqOn (w z) (fun _ ↦ 0) (ball z (A * r))ᶜ) :
    tsupport (fun x ↦ ∑ z ∈ t, (⨍ y in ball z r, u y ∂m) * w z x) ⊆
      cthickening ((A + 1) * r) (tsupport u) := by
  let a (z : X) := ⨍ y in ball z r, u y ∂m
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  by_contra hx'
  apply hx
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hxz : x ∈ ball z (A * r)
  · have hu₀ (y : X) (hy : y ∈ ball z r) : u y = 0 := by
      apply notMem_support.mp
      intro hyu
      apply hx'
      apply mem_cthickening_of_dist_le x y _ _ (subset_closure hyu)
      exact (dist_triangle x z y).trans (by
        have hz := mem_ball.mp hxz
        have hy' := mem_ball.mp hy
        rw [dist_comm y z] at hy'
        linarith only [hz, hy'])
    have ha : a z = 0 := by
      dsimp only [a]
      rw [setAverage_eq m u (ball z r)]
      have hI : (∫ y in ball z r, u y ∂m) = 0 := by
        rw [← integral_zero (α := X) (G := ℝ) (μ := m.restrict (ball z r))]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (μ := m) measurableSet_ball] with y hy
        exact hu₀ y hy
      rw [hI, smul_zero]
    change a z * w z x = 0
    rw [ha, zero_mul]
  · rw [show w z x = 0 from hw z hxz, mul_zero]

/-- For every sufficiently small radius, the discrete convolution has an
energy-domain representative uniformly close to the compactly supported
continuous input and supported in a fixed compact set. -/
theorem exists_discrete_convolution {β : ℝ}
    (hvol : VolumeDoubling m) (hcap : E.CapacityUpperBound β) :
    ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ {u : X → ℝ}, Continuous u → HasCompactSupport u →
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), δ ≤ 1 ∧
      ∀ r ∈ Ioo (0 : ℝ) δ, ∃ (t : Finset X) (g : X → E.domain) (w : X → X → ℝ),
        (↑t : Set X) ⊆ cthickening 1 (tsupport u) ∧
        (↑t : Set X).Pairwise (fun y z ↦ r ≤ dist y z) ∧
        (∀ z, (g z : RealLp m p) =ᵐ[m] w z) ∧
        (∀ z, Measurable (w z) ∧ (∀ x, w z x ∈ Icc (0 : ℝ) 1) ∧
          EqOn (w z) (fun _ ↦ 0) (ball z (A * r))ᶜ) ∧
        (∀ x, (∑ z ∈ t, w z x) ≤ 1) ∧
        EqOn (fun x ↦ ∑ z ∈ t, w z x) (fun _ ↦ 1) (cthickening 1 (tsupport u)) ∧
        (∀ z, E.rootSeminorm (g z) ≤ C * (r ^ (-β) * m.real (ball z r)) ^ p⁻¹) ∧
        let v := fun x ↦ ∑ z ∈ t, (⨍ y in ball z r, u y ∂m) * w z x
        ((∑ z ∈ t, (⨍ y in ball z r, u y ∂m) • g z : E.domain) : RealLp m p) =ᵐ[m] v ∧
        (∀ x, |v x - u x| ≤ ε) ∧ tsupport v ⊆ cthickening ((A + 1) * r) (tsupport u) := by
  classical
  obtain ⟨C, A, hC, hA, hpartition⟩ := E.exists_ball_partition hvol hcap
  refine ⟨C, A, hC, hA, fun {u} hu hc ε hε ↦ ?_⟩
  have huc := hu.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  let δ := min 1 (η / (A + 1))
  have hA' : 0 < A := zero_lt_one.trans hA
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hη (by linarith))
  refine ⟨δ, hδ, min_le_left _ _, fun r hr ↦ ?_⟩
  obtain ⟨t, ht, hsep, hcover⟩ := exists_finset_separated_ball_cover (hc.isCompact.cthickening (r := 1)) hr.1
  obtain ⟨g, w, hgw, hw, hsum, hunity, henergy⟩ := hpartition t r hr.1 hsep
  let a := fun z : X ↦ ⨍ y in ball z r, u y ∂m
  let v := fun x : X ↦ ∑ z ∈ t, a z * w z x
  refine ⟨t, g, w, ht, hsep, hgw, fun z ↦ ⟨(hw z).1, (hw z).2.2.1, (hw z).2.2.2⟩,
    hsum, hunity.mono hcover, henergy, ?_, ?_, ?_⟩
  · change ((∑ z ∈ t, a z • g z : E.domain) : RealLp m p) =ᵐ[m] v
    have hterm (z : X) : ((a z • g z : E.domain) : RealLp m p) =ᵐ[m] fun x ↦ a z * w z x := by
      filter_upwards [Lp.coeFn_smul (a z) (g z : RealLp m p), hgw z] with x hx hzx
      change (a z • (g z : RealLp m p)) x = _
      rw [hx, Pi.smul_apply, smul_eq_mul, hzx]
    exact E.coeFn_finsetSum t (fun z ↦ a z • g z) (fun z x ↦ a z * w z x) (fun z _ ↦ hterm z)
  · change ∀ x, |v x - u x| ≤ ε
    intro x
    have hsumu : (∑ z ∈ t, w z x) * u x = u x := by
      by_cases hx : x ∈ tsupport u
      · have he : (∑ z ∈ t, w z x) = 1 := hunity (hcover (self_subset_cthickening (δ := 1) (tsupport u) hx))
        rw [he, one_mul]
      · have hx₀ : u x = 0 := notMem_support.mp (fun h ↦ hx (subset_closure h))
        rw [hx₀, mul_zero]
    have hscale : (A + 1) * r < η := by
      have h := (lt_div_iff₀ (show 0 < A + 1 by positivity)).mp
        (hr.2.trans_le (min_le_right 1 (η / (A + 1))))
      rwa [mul_comm] at h
    calc
      _ = |∑ z ∈ t, (a z - u x) * w z x| := by
        dsimp only [v]
        simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, mul_comm (u x), hsumu]
      _ ≤ ∑ z ∈ t, |(a z - u x) * w z x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ t, ε * w z x := by
        apply Finset.sum_le_sum
        intro z _
        have hnonneg : 0 ≤ w z x := ((hw z).2.2.1 x).1
        rw [abs_mul, abs_of_nonneg hnonneg]
        by_cases hxz : x ∈ ball z (A * r)
        · apply mul_le_mul_of_nonneg_right _ hnonneg
          apply abs_setAverage_sub_le_of_bound measurableSet_ball
            (measure_ball_pos m z hr.1).ne' measure_ball_ne_top
            (hu.integrable_of_hasCompactSupport hc).integrableOn
          intro y hy
          have hdist : dist y x < η := (dist_triangle y z x).trans_lt (by
            have hy' := mem_ball.mp hy
            have hx' := mem_ball.mp hxz
            rw [dist_comm z x]
            linarith)
          simpa only [Real.dist_eq] using (hηu hdist).le
        · have hz : w z x = 0 := (hw z).2.2.2 hxz
          simp only [hz, mul_zero, le_refl]
      _ = ε * (∑ z ∈ t, w z x) := (Finset.mul_sum _ _ _).symm
      _ ≤ ε := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hsum x) hε.le
  · exact tsupport_discrete_convolution_subset (fun z ↦ (hw z).2.2.2)

end WalkDimensions.PEnergy
