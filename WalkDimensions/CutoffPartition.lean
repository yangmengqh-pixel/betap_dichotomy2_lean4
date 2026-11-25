import WalkDimensions.CutoffNormalization
import WalkDimensions.CapacityCutoffs
import WalkDimensions.DoublingCovers
import WalkDimensions.EnergyLocality

/-!
# Finite partitions of unity in the energy domain

Each weight is controlled by the energy of its own cutoff and the energies
of the cutoffs which meet it.
-/

open MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_normalized_cutoff_partition {ι : Type*} (t : Finset ι)
    (f : ι → E.domain) (u : ι → X → ℝ)
    (hfu : ∀ i, (f i : RealLp m p) =ᵐ[m] u i) (hu : ∀ i, Measurable (u i))
    (hrange : ∀ i x, u i x ∈ Icc (0 : ℝ) 1)
    (N : ι → Finset ι) (hN : ∀ i, N i ⊆ t)
    (hoverlap : ∀ i j x, j ∈ t → u i x ≠ 0 → u j x ≠ 0 → j ∈ N i) :
    ∃ (g : ι → E.domain) (w : ι → X → ℝ),
      (∀ i, (g i : RealLp m p) =ᵐ[m] w i) ∧ (∀ i, Measurable (w i)) ∧
      (∀ i x, w i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ i x, u i x = 0 → w i x = 0) ∧
      (∀ x, (∑ i ∈ t, w i x) ≤ 1) ∧
      (∀ x, 1 ≤ ∑ i ∈ t, u i x → (∑ i ∈ t, w i x) = 1) ∧
      (∀ i, E.rootSeminorm (g i) ≤
        2 * E.rootSeminorm (f i) + ∑ j ∈ N i, E.rootSeminorm (f j)) := by
  classical
  let w : ι → X → ℝ := fun i x ↦ u i x / max (∑ j ∈ t, u j x) 1
  have hbounded (i : ι) : eLpNorm (f i : RealLp m p) ∞ m ≤ 1 := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable (f i : RealLp m p))]
    apply eLpNormEssSup_le_of_ae_eNorm_bound
    filter_upwards [hfu i] with x hx
    change ‖(f i : RealLp m p) x‖ₑ ≤ _
    rw [hx, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (hrange i x).1, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hrange i x).2
  choose g hg hgEnergy using fun i ↦ E.exists_div_max_one (f i) (∑ j ∈ N i, f j) (hbounded i)
  refine ⟨g, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have haeSum : ((∑ j ∈ N i, f j : E.domain) : RealLp m p) =ᵐ[m]
        fun x ↦ ∑ j ∈ N i, u j x :=
      E.coeFn_finsetSum (N i) f u (fun j _ ↦ hfu j)
    filter_upwards [hg i, hfu i, haeSum] with x hx hxi hxs
    rw [hx, hxi, hxs]
    dsimp only [w]
    by_cases hzero : u i x = 0
    · simp only [hzero, zero_div]
    · rw [Finset.sum_subset (hN i) fun j hj hjN ↦
        not_ne_iff.mp fun hjzero ↦ hjN (hoverlap i j x hj hzero hjzero)]
  · intro i
    exact (hu i).div ((t.measurable_sum fun j _ ↦ hu j).max measurable_const)
  · intro i x
    have hd : 1 ≤ max (∑ j ∈ t, u j x) 1 := le_max_right _ _
    exact ⟨div_nonneg (hrange i x).1 (zero_le_one.trans hd),
      (div_le_one (zero_lt_one.trans_le hd)).mpr ((hrange i x).2.trans hd)⟩
  · intro i x hx
    simp only [w, hx, zero_div]
  · intro x
    dsimp only [w]
    rw [← Finset.sum_div]
    exact (div_le_one (zero_lt_one.trans_le (le_max_right _ _))).mpr (le_max_left _ _)
  · intro x hx
    dsimp only [w]
    rw [← Finset.sum_div, max_eq_left hx, div_self (zero_lt_one.trans_le hx).ne']
  · have hsum (s : Finset ι) :
        E.rootSeminorm (∑ j ∈ s, f j) ≤ ∑ j ∈ s, E.rootSeminorm (f j) := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        exact (E.rootSeminorm.add_le' _ _).trans (add_le_add_right ih _)
    intro i
    exact (hgEnergy i).trans (add_le_add_right (hsum (N i)) _)

open Metric

/-- Separated balls admit energy-domain weights with bounded supports and a
uniform energy estimate at the scale of the cover. -/
theorem exists_ball_partition [ProperSpace X] [m.IsOpenPosMeasure] {β : ℝ}
    (hvol : VolumeDoubling m) (hcap : E.CapacityUpperBound β) :
    ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ (t : Finset X) (r : ℝ), 0 < r →
      (↑t : Set X).Pairwise (fun x y ↦ r ≤ dist x y) →
      ∃ (g : X → E.domain) (w : X → X → ℝ),
        (∀ z, (g z : RealLp m p) =ᵐ[m] w z) ∧
        (∀ z, Measurable (w z) ∧ HasCompactSupport (w z) ∧
          (∀ x, w z x ∈ Icc (0 : ℝ) 1) ∧ EqOn (w z) (fun _ ↦ 0) (ball z (A * r))ᶜ) ∧
        (∀ x, (∑ z ∈ t, w z x) ≤ 1) ∧
        EqOn (fun x ↦ ∑ z ∈ t, w z x) (fun _ ↦ 1) (⋃ z ∈ t, ball z r) ∧
        (∀ z, E.rootSeminorm (g z) ≤ C * (r ^ (-β) * m.real (ball z r)) ^ p⁻¹) := by
  classical
  obtain ⟨c, A, hc, hA, hcut⟩ := E.exists_measurable_ball_cutoff hcap
  obtain ⟨M, _, hpack⟩ := exists_card_le_of_separated_centres hvol (R := 4 * A) (by linarith)
  obtain ⟨D, hDpos, hD⟩ := hvol
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * A + 1) (show (1 : ℝ) < 2 by norm_num)
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  refine ⟨2 * c ^ p⁻¹ + (M : ℝ) * (c * D ^ n) ^ p⁻¹, A, by positivity, hA,
    fun t r hr hsep ↦ ?_⟩
  choose f u hfu hu _ hrange hone hzero henergy using fun z ↦ hcut z r hr
  let N : X → Finset X := fun z ↦ t.filter (fun y ↦ dist y z ≤ 2 * A * r)
  have hN (z : X) : N z ⊆ t := Finset.filter_subset _ _
  have hdist {z y : X} (hy : y ∈ N z) : dist y z ≤ 2 * A * r :=
    (Finset.mem_filter.mp hy).2
  have hcard (z : X) : (N z).card ≤ M := by
    refine hpack z (r / 2) (by positivity) (N z) (fun y hy ↦ ?_) ?_
    · rw [show 4 * A * (r / 2) = 2 * A * r by ring]
      exact hdist hy
    · intro x hx y hy hxy
      rw [show 2 * (r / 2) = r by ring]
      exact hsep (hN z hx) (hN z hy) hxy
  obtain ⟨g, w, hgw, hw, hwRange, hwZero, hwSum, hwUnity, hwEnergy⟩ :=
    E.exists_normalized_cutoff_partition t f u hfu hu hrange N hN (by
      intro z y x hy hzx hyx
      apply Finset.mem_filter.mpr
      refine ⟨hy, ?_⟩
      have hxz := mem_ball.mp (show x ∈ ball z (A * r) from by
        by_contra h
        exact hzx (hzero z h))
      have hxy := mem_ball.mp (show x ∈ ball y (A * r) from by
        by_contra h
        exact hyx (hzero y h))
      rw [dist_comm x y] at hxy
      exact (dist_triangle y x z).trans (by linarith only [hxz, hxy]))
  refine ⟨g, w, hgw, ?_, hwSum, ?_, ?_⟩
  · intro z
    have hz : EqOn (w z) (fun _ ↦ 0) (ball z (A * r))ᶜ :=
      fun x hx ↦ hwZero z x (hzero z hx)
    refine ⟨hw z, HasCompactSupport.intro (isCompact_closedBall z (A * r)) ?_, hwRange z, hz⟩
    intro x hx
    exact hz (fun h ↦ hx (ball_subset_closedBall h))
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
    apply hwUnity x
    have h := Finset.single_le_sum (fun y _ ↦ (hrange y x).1) hz
    simpa only [hone z hxz] using h
  · have hreal (y : X) : (E.energy (f y) : ℝ) ≤ c * r ^ (-β) * m.real (ball y r) := by
      have hfin : ENNReal.ofReal (c * r ^ (-β)) * m (ball y r) ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top
      simpa only [measureReal_def, ENNReal.coe_toReal, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ c * r ^ (-β))] using
        ENNReal.toReal_mono hfin (henergy y)
    have hown (z : X) : E.rootSeminorm (f z) ≤
        c ^ p⁻¹ * (r ^ (-β) * m.real (ball z r)) ^ p⁻¹ := by
      rw [E.rootSeminorm_apply, ← Real.mul_rpow hc.le (by positivity), ← mul_assoc]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (hreal z) (inv_nonneg.mpr hp.le)
    have hlocal {z y : X} (hy : y ∈ N z) :
        m.real (ball y r) ≤ D ^ n * m.real (ball z r) := by
      have hball := measure_ball_le_of_dist_le hD hr n (y := y) (x := z) (t := r) (by
        calc
          _ ≤ (2 * A + 1) * r := by linarith only [hdist hy]
          _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hr.le)
      have hfin : (ENNReal.ofReal D) ^ n * m (ball z r) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) measure_ball_ne_top
      simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hDpos.le] using
        ENNReal.toReal_mono hfin hball
    intro z
    let B := (r ^ (-β) * m.real (ball z r)) ^ p⁻¹
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hneighbors : (∑ y ∈ N z, E.rootSeminorm (f y)) ≤ (M : ℝ) * ((c * D ^ n) ^ p⁻¹ * B) := by
      calc
        _ ≤ ∑ _ ∈ N z, (c * D ^ n) ^ p⁻¹ * B := by
          apply Finset.sum_le_sum
          intro y hy
          rw [E.rootSeminorm_apply]
          dsimp only [B]
          rw [← Real.mul_rpow (by positivity : 0 ≤ c * D ^ n) (by positivity)]
          apply Real.rpow_le_rpow (NNReal.coe_nonneg _) _ (inv_nonneg.mpr hp.le)
          calc
            _ ≤ c * r ^ (-β) * m.real (ball y r) := hreal y
            _ ≤ c * r ^ (-β) * (D ^ n * m.real (ball z r)) :=
              mul_le_mul_of_nonneg_left (hlocal hy) (by positivity)
            _ = _ := by ring
        _ = ((N z).card : ℝ) * ((c * D ^ n) ^ p⁻¹ * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard z) (by positivity)
    calc
      _ ≤ 2 * E.rootSeminorm (f z) + ∑ y ∈ N z, E.rootSeminorm (f y) := hwEnergy z
      _ ≤ 2 * (c ^ p⁻¹ * B) + (M : ℝ) * ((c * D ^ n) ^ p⁻¹ * B) :=
        add_le_add (mul_le_mul_of_nonneg_left (hown z) (by norm_num)) hneighbors
      _ = _ := by ring

end WalkDimensions.PEnergy
