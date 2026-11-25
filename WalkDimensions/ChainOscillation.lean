import WalkDimensions.AdjacentAverageDensity
import WalkDimensions.LocalBesov
import WalkDimensions.ChainPaths
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing normalized oscillation at a positive density point
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] [SFinite m]
  {p : ℝ} (E : PEnergy m p)

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] [SecondCountableTopology X] in
private theorem dist_chain_le_mul {z : ℕ → X} {n : ℕ} {s : ℝ}
    (h : ∀ k < n, dist (z (k + 1)) (z k) ≤ s) :
    ∀ k ≤ n, dist (z k) (z 0) ≤ (k : ℝ) * s := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    have hstep := h k (Nat.lt_of_succ_le hk)
    have hOld := ih (Nat.le_of_lt (Nat.lt_of_succ_le hk))
    calc
      _ ≤ dist (z (k + 1)) (z k) + dist (z k) (z 0) := dist_triangle _ _ _
      _ ≤ s + (k : ℝ) * s := add_le_add hstep hOld
      _ = _ := by rw [Nat.cast_succ]; ring

private theorem abs_chain_le_mul {z : ℕ → ℝ} {n : ℕ} {s : ℝ}
    (h : ∀ k < n, |z (k + 1) - z k| ≤ s) : |z n - z 0| ≤ (n : ℝ) * s := by
  simpa only [Real.dist_eq] using dist_chain_le_mul (z := z) (s := s) (fun k hk ↦ by simpa only [Real.dist_eq] using h k hk) n le_rfl

/-- If the energy and reference measures have the same nonzero tangent up
to a constant, a chain with fine links improves the order of the oscillation
bound at that point. -/
theorem eventually_exists_small_normalized_oscillation {β : ℝ} (hβ : p < β)
    (hvol : VolumeDoubling m) (hPI : E.Poincare E.energyMeasure β) (hCC : ChainCondition X)
    (f : E.domain) (x : X) {a : ℝ} (ha : 0 < a)
    (hTang : ∀ ε > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ S ⊆ ball x r, MeasurableSet S →
        |((E.energyMeasure f) S).toReal - a * (m S).toReal| ≤ ε * (m (ball x r)).toReal) :
    ∀ ε > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c : ℝ,
      (∫⁻ y in ball x r, ENNReal.ofReal |(f : RealLp m p) y - c| ^ p ∂m) ≤
        ENNReal.ofReal (ε * r ^ β) * m (ball x r) := by
  have hp := zero_lt_one.trans E.one_lt
  have hβpos := hp.trans hβ
  obtain ⟨C, A, hC, hA, hNear⟩ := E.exists_adjacent_average_bound_of_density hvol hPI
  obtain ⟨_, A', J, _, hA', hJ, hJT, _, hLocal⟩ :=
    E.local_besov_bound hvol hPI E.energyMeasure_univ
  obtain ⟨D, hD, hVD⟩ := hvol
  obtain ⟨L₀, hL₀, hCC⟩ := hCC
  let L := max 1 L₀
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  let R := max ((A + 1) * L + 1) (2 * A' * L + 2)
  have hR : 0 < R := (show 0 < (A + 1) * L + 1 by positivity).trans_le (le_max_left _ _)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R (show (1 : ℝ) < 2 by norm_num)
  let P := (2 : ℝ) ^ p * (2 * a) * L ^ β
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  let F (t : ℝ) := P * (J.toReal * D ^ k * t ^ β + C ^ p * t ^ (β - p))
  have hF : Tendsto F (𝓝 0) (𝓝 0) := by
    have h₁ := (Real.continuousAt_rpow_const 0 β (Or.inr hβpos.le)).tendsto.const_mul (J.toReal * D ^ k)
    have h₂ := (Real.continuousAt_rpow_const 0 (β - p) (Or.inr (sub_pos.mpr hβ).le)).tendsto.const_mul (C ^ p)
    have hh := (h₁.add h₂).const_mul P
    simpa only [F, Real.zero_rpow hβpos.ne', Real.zero_rpow (sub_pos.mpr hβ).ne',
      mul_zero, add_zero] using hh
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := ((hF.comp tendsto_one_div_add_atTop_nhds_zero_nat).eventually_lt_const hε).exists
  let n := n₀ + 1
  have hn : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le _)
  have hn₁ : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hSmall : F (1 / (n : ℝ)) ≤ ε := by
    change F (1 / ((n₀ : ℝ) + 1)) < ε at hn₀
    simpa only [n, Nat.cast_add, Nat.cast_one] using hn₀.le
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((L + R) * (n : ℝ) / (A * L))
    (show (1 : ℝ) < 2 by norm_num)
  let e := a / (D ^ j + 1)
  have he : 0 < e := div_pos ha (by positivity)
  have hea : e ≤ a := by
    apply (div_le_iff₀ (show 0 < D ^ j + 1 by positivity)).mpr
    nlinarith only [mul_nonneg ha.le (pow_nonneg hD.le j)]
  have heD : e * D ^ j ≤ a := by
    dsimp only [e]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < D ^ j + 1 by positivity)).mpr
    nlinarith only [ha.le]
  obtain ⟨δ, hδ, hTang'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hTang e he)
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  have hr₀ : 0 < r := hr.1
  have hRr : R * r ∈ Ioo (0 : ℝ) δ := ⟨mul_pos hR hr₀,
    by simpa only [mul_comm] using (lt_div_iff₀ hR).mp hr.2⟩
  let s := L * r / (n : ℝ)
  have hs : 0 < s := div_pos (mul_pos hL hr₀) hn₁
  have hsL : s ≤ L * r := div_le_self (by positivity) (by exact_mod_cast hn)
  let B := ball x r
  let T := ball x (R * r)
  let u : RealLp m p := f
  let av (y : X) := ⨍ z in ball y s, u z ∂m
  let ν := E.energyMeasure f
  have hTvol : (m T).toReal ≤ D ^ k * (m B).toReal := by
    have h := (measure_mono (ball_subset_ball (mul_le_mul_of_nonneg_right hk.le hr₀.le)) :
      m T ≤ m (ball x ((2 : ℝ) ^ k * r))).trans (measure_ball_two_pow_le hVD x hr₀ k)
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      measure_ball_ne_top) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hD.le] at h'
  have hTmass : (ν T).toReal ≤ (2 * a * D ^ k) * (m B).toReal := by
    have h := abs_le.mp (hTang' hRr T (subset_refl _) measurableSet_ball)
    have hTop : (ν T).toReal - a * (m T).toReal ≤ e * (m T).toReal := h.2
    have h₁ : (ν T).toReal ≤ (a + e) * (m T).toReal := by nlinarith only [hTop]
    apply h₁.trans
    have h₂ := mul_le_mul_of_nonneg_right (show a + e ≤ 2 * a by linarith)
      (show 0 ≤ (m T).toReal from ENNReal.toReal_nonneg)
    exact h₂.trans ((mul_le_mul_of_nonneg_left hTvol (by positivity)).trans_eq (by ring))
  have hLocalMass (y : X) (hy : dist y x ≤ L * r) :
      (ν (ball y (A * s))).toReal ≤ (2 * a) * (m (ball y (A * s))).toReal := by
    let V := ball y (A * s)
    have hVsub : V ⊆ T := by
      intro z hz
      apply mem_ball.mpr
      have hh := (dist_triangle z y x).trans_lt (add_lt_add_of_lt_of_le (mem_ball.mp hz) hy)
      have hAr := mul_le_mul_of_nonneg_left hsL (zero_le_one.trans hA)
      have hR' := mul_le_mul_of_nonneg_right (show (A + 1) * L + 1 ≤ R from le_max_left _ _) hr₀.le
      exact hh.trans_le (by nlinarith only [hAr, hR', hr₀])
    have hRat : m T ≤ (ENNReal.ofReal D) ^ j * m V := by
      apply measure_ball_le_of_dist_le hVD (mul_pos (zero_lt_one.trans_le hA) hs) j
      rw [dist_comm x y]
      have hh := (div_lt_iff₀ (mul_pos (zero_lt_one.trans_le hA) hL)).mp hj
      have he' : (L + R) * r ≤ (2 : ℝ) ^ j * (A * s) := by
        have h := mul_le_mul_of_nonneg_right hh.le hr₀.le
        calc
          _ ≤ ((2 : ℝ) ^ j * (A * L) * r) / (n : ℝ) := (le_div_iff₀ hn₁).mpr
            ((le_of_eq (by ring)).trans h)
          _ = _ := by dsimp only [s]; ring
      exact (add_le_add_left hy _).trans (by rw [← add_mul]; exact he')
    have hRatio := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) measure_ball_ne_top) hRat
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hD.le] at hRatio
    have hA := (abs_le.mp (hTang' hRr V hVsub measurableSet_ball)).2
    have he' : e * (m T).toReal ≤ a * (m V).toReal := by
      apply (mul_le_mul_of_nonneg_left hRatio he.le).trans
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right heD ENNReal.toReal_nonneg
    linarith only [hA, he']
  have hOsc (y : X) (hy : y ∈ B) : |av y - av x| ≤ (n : ℝ) * (C * (2 * a) ^ p⁻¹ * s ^ (β / p)) := by
    obtain ⟨z, hz₀, hzn, hStep⟩ := hCC x y n hn
    have hstep (i : ℕ) (hi : i < n) : dist (z (i + 1)) (z i) ≤ s := by
      refine (hStep i hi).trans ?_
      apply div_le_div_of_nonneg_right _ hn₁.le
      have hh := (mem_ball.mp hy).le
      rw [dist_comm] at hh
      exact mul_le_mul (le_max_right _ _) hh dist_nonneg hL.le
    have hz (i : ℕ) (hi : i ≤ n) : dist (z i) x ≤ L * r := by
      rw [← hz₀]
      apply (dist_chain_le_mul hstep i hi).trans
      exact (mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ n by exact_mod_cast hi) hs.le).trans_eq
        (by dsimp only [s]; rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₁.ne'])
    have he := abs_chain_le_mul (z := av ∘ z) (n := n) (fun i hi ↦
      hNear f (z (i + 1)) (z i) s (2 * a) hs (by positivity) (hstep i hi)
        (hLocalMass (z i) (hz i hi.le)))
    simpa only [Function.comp_apply, hz₀, hzn] using he
  refine ⟨av x, ?_⟩
  have hSubT : thickening (2 * A' * s) B ⊆ T := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
    apply mem_ball.mpr
    have hh := (dist_triangle y z x).trans_lt (add_lt_add hyz (mem_ball.mp hz))
    have hK := mul_le_mul_of_nonneg_left hsL (by positivity : 0 ≤ 2 * A')
    have hR' := mul_le_mul_of_nonneg_right (le_max_right ((A + 1) * L + 1) (2 * A' * L + 2)) hr₀.le
    exact hh.trans_le (by change (2 * A' * L + 2) * r ≤ R * r at hR'; nlinarith only [hK, hR', hr₀])
  have hJensen (y : X) : ENNReal.ofReal |u y - av y| ^ p ≤ ballMoment m p u s y := by
    have h := ofReal_abs_setAverage_sub_rpow_le E.one_lt.le
      (subset_refl (ball y s)) (measure_ball_pos m y hs).ne' measure_ball_ne_top
      ((Lp.memLp u).mono_measure Measure.restrict_le_self) (u y)
    simpa only [av, abs_sub_comm (u y), ballMoment, normalizedBall, lintegral_smul_measure,
      smul_eq_mul] using h
  have hM : (∫⁻ y in B, ballMoment m p u s y ∂m) ≤ (ENNReal.ofReal s) ^ β * (J * ν T) := by
    let q := (ENNReal.ofReal s) ^ β
    have hq := ENNReal.rpow_pos (p := β) (ENNReal.ofReal_pos.mpr hs) ENNReal.ofReal_ne_top
    have hqT : q ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hβpos.le ENNReal.ofReal_ne_top
    have h := mul_le_mul_of_nonneg_left ((hLocal B f s hs).trans
      (mul_le_mul_of_nonneg_left (measure_mono hSubT) bot_le)) (show 0 ≤ q from bot_le)
    rw [besovEnergy, ENNReal.rpow_neg, ← mul_assoc, ENNReal.mul_inv_cancel hq.ne' hqT, one_mul] at h
    exact h
  have hM' : (∫⁻ y in B, ballMoment m p u s y ∂m) ≤
      ENNReal.ofReal (s ^ β * (J.toReal * (2 * a * D ^ k))) * m B := by
    have he := ENNReal.ofReal_le_ofReal hTmass
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal measure_ball_ne_top] at he
    apply hM.trans
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he bot_le) bot_le).trans_eq ?_
    conv_lhs => rw [ENNReal.ofReal_rpow_of_pos hs, ← ENNReal.ofReal_toReal hJT]
    change ENNReal.ofReal (s ^ β) * (ENNReal.ofReal J.toReal *
      (ENNReal.ofReal (2 * a * D ^ k) * m B)) = _
    rw [← mul_assoc (ENNReal.ofReal J.toReal),
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
  let b := (n : ℝ) * (C * (2 * a) ^ p⁻¹ * s ^ (β / p))
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hPower (y : X) (hy : y ∈ B) : ENNReal.ofReal |u y - av x| ^ p ≤
      (2 : ℝ≥0∞) ^ p * (ballMoment m p u s y + ENNReal.ofReal (b ^ p)) := by
    have h := ennreal_abs_sub_rpow_le (u y - av y) (av x - av y) hp.le
    rw [sub_sub_sub_cancel_right, abs_sub_comm (av x) (av y)] at h
    apply h.trans
    rw [← ENNReal.ofReal_rpow_of_nonneg hb hp.le]
    exact mul_le_mul_of_nonneg_left (add_le_add (hJensen y)
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hOsc y hy)) hp.le)) bot_le
  have hMeas : AEMeasurable (fun y ↦ ballMoment m p u s y) (m.restrict B) := by
    have hf : AEMeasurable u m := (Lp.aestronglyMeasurable _).aemeasurable
    apply ((measurable_ballMoment (m := m) hf.measurable_mk p s).aemeasurable
      (μ := m.restrict B)).congr
    filter_upwards [ae_restrict_of_ae hf.ae_eq_mk] with y hy
    unfold ballMoment normalizedBall
    rw [lintegral_smul_measure, lintegral_smul_measure, ← hy]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hf.ae_eq_mk] with z hz
    rw [hz]
  have h'' : (∫⁻ y in B, ENNReal.ofReal |u y - av x| ^ p ∂m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * (s ^ β * (J.toReal * (2 * a * D ^ k)) + b ^ p)) * m B := by
    apply (setLIntegral_mono' measurableSet_ball hPower).trans
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)),
      lintegral_add_left' hMeas, setLIntegral_const]
    refine (mul_le_mul_of_nonneg_left (add_le_add_left hM' _) bot_le).trans_eq ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), ← mul_assoc,
      show (2 : ℝ≥0∞) ^ p = ENNReal.ofReal ((2 : ℝ) ^ p) by
        rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : 0 < (2 : ℝ))]
        norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
  apply h''.trans
  apply mul_le_mul_of_nonneg_right _ bot_le
  apply ENNReal.ofReal_le_ofReal
  have hsPow : s ^ β = L ^ β * (1 / (n : ℝ)) ^ β * r ^ β := by
    have he : s = L * (1 / (n : ℝ)) * r := by dsimp only [s]; ring
    rw [he, Real.mul_rpow (by positivity) hr₀.le, Real.mul_rpow hL.le (by positivity)]
  have hbPow : b ^ p = ((n : ℝ) ^ p * (C ^ p * (2 * a))) * s ^ β := by
    dsimp only [b]
    rw [Real.mul_rpow hn₁.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity : 0 ≤ 2 * a),
      inv_mul_cancel₀ hp.ne', Real.rpow_one, ← Real.rpow_mul hs.le, div_mul_cancel₀ _ hp.ne']
    ring
  rw [hbPow, hsPow]
  have hnPow : (n : ℝ) ^ p * (1 / (n : ℝ)) ^ β = (1 / (n : ℝ)) ^ (β - p) := by
    simp_rw [one_div, Real.inv_rpow hn₁.le, Real.rpow_sub hn₁]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hn₁ β), ne_of_gt (Real.rpow_pos_of_pos hn₁ p)]
  calc
    _ = F (1 / (n : ℝ)) * r ^ β := by
      dsimp only [F, P]
      rw [← hnPow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hSmall (Real.rpow_nonneg hr₀.le _)

end WalkDimensions.PEnergy
