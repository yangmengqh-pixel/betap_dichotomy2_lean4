import WalkDimensions.MaximalSuperlevel
import WalkDimensions.LowerSemicontinuousWeights

/-!
# Lacunary obstacle weights for the exponent improvement
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

noncomputable def obstacleSet (m : Measure X) (g : X → ℝ≥0∞)
    (q T M τ : ℝ) (i : ℕ) : Set X :=
  {z | ENNReal.ofReal ((M ^ (i + 1) * τ) ^ q) <
    localMaximalAverage m (fun w ↦ g w ^ q) T z}

noncomputable def obstacleWeight (m : Measure X) (g : X → ℝ≥0∞)
    (q T M τ : ℝ) (k : ℕ) (z : X) : ℝ≥0∞ :=
  (k : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range k,
    (obstacleSet m g q T M τ i).indicator (fun _ ↦ ENNReal.ofReal (M ^ (i + 1))) z

theorem isOpen_obstacleSet (g : X → ℝ≥0∞) (q T M τ : ℝ) (i : ℕ) :
    IsOpen (obstacleSet m g q T M τ i) :=
  isOpen_localMaximalAverage_superlevel _ _ _

theorem lowerSemicontinuous_obstacleWeight (g : X → ℝ≥0∞) (q T M τ : ℝ) {k : ℕ}
    (hk : 0 < k) : LowerSemicontinuous (obstacleWeight m g q T M τ k) := by
  let f (i : ℕ) := (obstacleSet m g q T M τ i).indicator (fun _ ↦ ENNReal.ofReal (M ^ (i + 1)))
  have hf (i : ℕ) : LowerSemicontinuous (f i) :=
    (isOpen_obstacleSet g q T M τ i).lowerSemicontinuous_indicator bot_le
  have hsum (t : Finset ℕ) : LowerSemicontinuous (fun z ↦ ∑ i ∈ t, f i z) := by
    classical
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (continuous_const (y := (0 : ℝ≥0∞))).lowerSemicontinuous
    | insert i t hi h =>
      simpa only [Finset.sum_insert hi] using (hf i).add h
  have hc : ((k : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (by exact_mod_cast hk.ne')
  have hmul : Continuous (fun t : ℝ≥0∞ ↦ ((k : ℝ≥0∞)⁻¹ : ℝ≥0∞) * t) :=
    continuous_iff_continuousAt.mpr fun t ↦ ENNReal.continuousAt_const_mul (Or.inl hc)
  exact hmul.comp_lowerSemicontinuous (hsum (Finset.range k))
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left h bot_le)

theorem obstacleWeight_bounded (g : X → ℝ≥0∞) (q T M τ : ℝ) {k : ℕ} (hk : 0 < k) :
    ∃ A ≠ ∞, ∀ z, obstacleWeight m g q T M τ k z ≤ A := by
  refine ⟨(k : ℝ≥0∞)⁻¹ * (∑ i ∈ Finset.range k, ENNReal.ofReal (M ^ (i + 1))), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by exact_mod_cast hk.ne'))
      (ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top)
  · intro z
    apply mul_le_mul_of_nonneg_left _ bot_le
    apply Finset.sum_le_sum
    intro i _
    exact indicator_le_self' (fun _ _ ↦ bot_le) _

private theorem geom_sum_succ_le {M : ℝ} (hM : 2 ≤ M) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), M ^ (i + 1)) ≤ 2 * M ^ (j + 1) := by
  have h₀ : 0 ≤ M := by linarith
  induction j with
  | zero => simp; linarith
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have h := mul_le_mul_of_nonneg_left hM (pow_nonneg h₀ (j + 1))
    rw [← pow_succ] at h
    nlinarith only [h, ih]

private theorem obstacleWeight_rpow_le {p M : ℝ} (hp : 0 < p) (hM : 2 ≤ M)
    (g : X → ℝ≥0∞) (q T τ : ℝ) {k : ℕ} (hk : 0 < k) (z : X) :
    obstacleWeight m g q T M τ k z ^ p ≤ ENNReal.ofReal ((2 / (k : ℝ)) ^ p) *
      ∑ i ∈ Finset.range k, (obstacleSet m g q T M τ i).indicator
        (fun _ ↦ ENNReal.ofReal ((M ^ (i + 1)) ^ p)) z := by
  classical
  have hM₀ : 0 ≤ M := by linarith
  let s := (Finset.range k).filter (fun i ↦ z ∈ obstacleSet m g q T M τ i)
  have hsSum {v : ℕ → ℝ≥0∞} :
      ∑ i ∈ Finset.range k, (obstacleSet m g q T M τ i).indicator (fun _ ↦ v i) z =
        ∑ i ∈ s, v i := by
    rw [Finset.sum_filter]
    rfl
  unfold obstacleWeight
  rw [hsSum, hsSum]
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem _ _
    have hs' : s ⊆ Finset.range (j + 1) :=
      fun i hi ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ _ hi))
    have hSum : (∑ i ∈ s, ENNReal.ofReal (M ^ (i + 1))) ≤ ENNReal.ofReal (2 * M ^ (j + 1)) := by
      refine (Finset.sum_le_sum_of_subset hs').trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ pow_nonneg hM₀ _)]
      exact ENNReal.ofReal_le_ofReal (geom_sum_succ_le hM j)
    have hm : (k : ℝ≥0∞)⁻¹ * ENNReal.ofReal (2 * M ^ (j + 1)) =
        ENNReal.ofReal ((2 / (k : ℝ)) * M ^ (j + 1)) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hk),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    apply (ENNReal.rpow_le_rpow ((mul_le_mul_of_nonneg_left hSum bot_le).trans_eq hm) hp.le).trans
    rw [ENNReal.ofReal_rpow_of_pos (by positivity), Real.mul_rpow (by positivity) (pow_nonneg hM₀ _),
      ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i ↦ ENNReal.ofReal ((M ^ (i + 1)) ^ p)) (fun _ _ ↦ bot_le) hj) bot_le
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he, ENNReal.zero_rpow_of_pos hp]

variable [BorelSpace X] [ProperSpace X] [SecondCountableTopology X]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem localMaximalAverage_obstacleWeight_le {D : ℝ} (hD₀ : 0 < D)
    (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ ENNReal.ofReal D * m (ball x r))
    (g : X → ℝ≥0∞) (hg : Measurable g) (x : X)
    {p q L S T M τ : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) (hM : 2 ≤ M) (hMD : D ^ 2 ≤ M)
    (hτ : 0 < τ) (hSL : 3 * S ≤ L) (hTL : 4 * T ≤ L)
    (hx : localMaximalAverage m (fun z ↦ g z ^ q) L x ≤ ENNReal.ofReal (τ ^ q))
    {k : ℕ} (hk : 0 < k) :
    localMaximalAverage m (fun z ↦ obstacleWeight m g q T M τ k z ^ p) S x ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * D ^ 4 * (k : ℝ) ^ (1 - p) * M ^ ((k : ℝ) * (p - q))) := by
  let E (i : ℕ) := obstacleSet m g q T M τ i
  have hp : 0 < p := zero_lt_one.trans_le (hq.trans hqp)
  have hq₀ : 0 < q := zero_lt_one.trans_le hq
  have hM₁ : 1 ≤ M := by linarith
  have hM₀ : 0 < M := by linarith
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast hk
  have hLevel (i : ℕ) : localMaximalAverage m ((E i).indicator (fun _ ↦ 1)) S x ≤
      ENNReal.ofReal (D ^ 4 / (M ^ (i + 1)) ^ q) := by
    let b := ENNReal.ofReal ((M ^ (i + 1) * τ) ^ q)
    have hb : 0 < (M ^ (i + 1) * τ) ^ q := by positivity
    have hMD' : (ENNReal.ofReal D) ^ 2 * ENNReal.ofReal (τ ^ q) ≤ b := by
      rw [← ENNReal.ofReal_pow hD₀.le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (by positivity) hτ.le]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ M := hMD
        _ ≤ M ^ (i + 1) := by
          rw [pow_succ]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hM₁) hM₀.le
        _ ≤ _ := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hM₁) hq
    have h := localMaximalAverage_indicator_superlevel_le hD (fun z ↦ g z ^ q)
      (hg.pow_const q) x hSL hTL (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top hx hMD'
    refine h.trans_eq ?_
    rw [← ENNReal.ofReal_pow hD₀.le, ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv,
      ← ENNReal.ofReal_inv_of_pos hb, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by positivity) hτ.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hτ q)]
  apply iSup_le
  intro z
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  apply iSup_le
  intro hxz
  let ν := normalizedBall m z s
  let F (i : ℕ) := (E i).indicator (fun _ ↦ ENNReal.ofReal ((M ^ (i + 1)) ^ p))
  let C := ENNReal.ofReal ((2 / (k : ℝ)) ^ p)
  have hF (i : ℕ) : Measurable (F i) :=
    measurable_const.indicator (isOpen_obstacleSet g q T M τ i).measurableSet
  have hFavg (i : ℕ) (hi : i ∈ Finset.range k) : (∫⁻ y, F i y ∂ν) ≤
      ENNReal.ofReal (D ^ 4 * M ^ ((k : ℝ) * (p - q))) := by
    have hEq : F i = fun y ↦ ENNReal.ofReal ((M ^ (i + 1)) ^ p) * (E i).indicator (fun _ ↦ 1) y := by
      funext y
      by_cases hy : y ∈ E i <;> simp [F, hy, indicator_of_mem, indicator_of_notMem]
    rw [hEq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hA := (average_le_localMaximalAverage ((E i).indicator (fun _ ↦ 1)) hs.1 hs.2 hxz).trans (hLevel i)
    apply (mul_le_mul_of_nonneg_left hA bot_le).trans
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : (M ^ (i + 1)) ^ p * (D ^ 4 / (M ^ (i + 1)) ^ q) =
        D ^ 4 * M ^ (((i + 1 : ℕ) : ℝ) * (p - q)) := by
      conv_rhs => rw [Real.rpow_natCast_mul hM₀.le, Real.rpow_sub (pow_pos hM₀ _)]
      ring
    rw [he]
    gcongr
    exact_mod_cast (Finset.mem_range.mp hi)
  change (∫⁻ y, obstacleWeight m g q T M τ k y ^ p ∂ν) ≤ _
  apply (lintegral_mono (obstacleWeight_rpow_le hp hM g q T τ hk)).trans
  change (∫⁻ y, C * ∑ i ∈ Finset.range k, F i y ∂ν) ≤ _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun i _ ↦ hF i)]
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hFavg) bot_le).trans
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hk₀.le, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.div_rpow (by norm_num) hk₀.le, Real.rpow_sub hk₀, Real.rpow_one]
  ring_nf
  exact le_rfl

end WalkDimensions
