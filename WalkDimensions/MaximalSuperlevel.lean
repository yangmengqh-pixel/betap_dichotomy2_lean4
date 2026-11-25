import WalkDimensions.LocalMaximalAverage
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# Localized measure estimates for maximal superlevel sets
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

theorem localMaximalAverage_indicator_superlevel_le {D : ℝ≥0∞}
    (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    (g : X → ℝ≥0∞) (hg : Measurable g) (x : X) {L S T : ℝ}
    (hSL : 3 * S ≤ L) (hTL : 4 * T ≤ L)
    {a b : ℝ≥0∞} (hb₀ : b ≠ 0) (hbT : b ≠ ∞)
    (hxa : localMaximalAverage m g L x ≤ a) (hab : D ^ 2 * a ≤ b) :
    localMaximalAverage m ({y | b < localMaximalAverage m g T y}.indicator (fun _ ↦ 1)) S x ≤
      D ^ 4 * a / b := by
  let E := {y | b < localMaximalAverage m g T y}
  have hE : MeasurableSet E := (isOpen_localMaximalAverage_superlevel (m := m) g T b).measurableSet
  apply iSup_le
  intro z
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  apply iSup_le
  intro hx
  have hs₀ : 0 < s := hs.1
  have hxs : x ∈ ball z s := hx
  let B := ball z s
  let U := ball z (3 * s)
  have hsU : 0 < 3 * s := by positivity
  have hCx : x ∈ U := ball_subset_ball (by linarith) hxs
  have hCoverVol : m U ≤ D ^ 2 * m B := by
    apply (measure_mono (ball_subset_ball (show 3 * s ≤ (2 : ℝ) ^ (2 : ℕ) * s by nlinarith))).trans
    exact measure_ball_two_pow_le hD z hs₀ 2
  let W := {i : X × ℝ | i.2 ∈ Ioc (0 : ℝ) T ∧ (B ∩ ball i.1 i.2).Nonempty ∧
      b < ∫⁻ y, g y ∂normalizedBall m i.1 i.2}
  have hWsmall (i : X × ℝ) (hi : i ∈ W) : i.2 ≤ s := by
    by_contra! hbig
    let w := i.1
    let t := i.2
    have ht : 0 < t := hi.1.1
    obtain ⟨y, hy, hyw⟩ := hi.2.1
    have hDist : dist x w < 2 * s + t := by
      have h₁ := dist_triangle x z y
      have h₂ := dist_triangle x y w
      have hz := mem_ball.mp (show y ∈ ball z s from hy)
      have hxz := mem_ball.mp hxs
      have hy' := mem_ball.mp hyw
      rw [dist_comm z y] at h₁
      linarith only [h₁, h₂, hz, hxz, hy']
    have hxW : x ∈ ball w (4 * t) := mem_ball.mpr (by linarith only [hDist, hbig, ht])
    have hSub : ball w t ⊆ ball w (4 * t) := ball_subset_ball (by linarith)
    have hBound := (lintegral_mono_set (μ := m) (f := g) hSub).trans
      (lintegral_ball_le_localMaximalAverage g (mul_pos (by norm_num) ht)
        ((mul_le_mul_of_nonneg_left hi.1.2 (by norm_num)).trans hTL) hxW)
    have hVol : m (ball w (4 * t)) ≤ D ^ 2 * m (ball w t) := by
      simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
        measure_ball_two_pow_le hD w ht 2
    have h' := hBound.trans (mul_le_mul hxa hVol bot_le bot_le)
    rw [← mul_assoc, mul_comm a (D ^ 2)] at h'
    have h'' := h'.trans (mul_le_mul_of_nonneg_right hab bot_le)
    have h''' := (ENNReal.div_le_iff (measure_ball_pos m w ht).ne' measure_ball_ne_top).mpr h''
    have hh : b < ∫⁻ y, g y ∂normalizedBall m w t := hi.2.2
    rw [normalizedBall, lintegral_smul_measure, smul_eq_mul, mul_comm, ← div_eq_mul_inv] at hh
    exact hh.not_ge h'''
  have hWsub (i : X × ℝ) (hi : i ∈ W) : ball i.1 i.2 ⊆ U := by
    obtain ⟨y, hy, hy'⟩ := hi.2.1
    intro v hv
    apply mem_ball.mpr
    have hyz := mem_ball.mp (show y ∈ ball z s from hy)
    have h₁ := dist_triangle v i.1 y
    have h₂ := dist_triangle v y z
    have hv' := mem_ball.mp hv
    have hyw := mem_ball.mp hy'
    rw [dist_comm i.1 y] at h₁
    linarith only [h₁, h₂, hyz, hv', hyw, hWsmall i hi]
  obtain ⟨V, hVW, hVdis, hCov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball W Prod.fst Prod.snd s hWsmall 4 (by norm_num)
  have hVc : V.Countable :=
    hVdis.countable_of_isOpen (fun _ _ ↦ isOpen_ball) (fun i hi ↦ ⟨i.1, mem_ball_self (hVW hi).1.1⟩)
  have : Countable V := hVc.to_subtype
  let F (i : V) := ball (i : X × ℝ).1 (i : X × ℝ).2
  let G (i : V) := ball (i : X × ℝ).1 (4 * (i : X × ℝ).2)
  have hInc : B ∩ E ⊆ ⋃ i : V, G i := by
    intro y hy
    have hyE : b < localMaximalAverage m g T y := hy.2
    obtain ⟨w, t, ht, hyt, hm⟩ : ∃ (w : X) (t : ℝ), t ∈ Ioc (0 : ℝ) T ∧
        y ∈ ball w t ∧ b < ∫⁻ v, g v ∂normalizedBall m w t := by
      simpa only [localMaximalAverage, lt_iSup_iff, exists_prop] using hyE
    obtain ⟨i, hi, hSub⟩ := hCov (w, t) ⟨ht, ⟨y, hy.1, hyt⟩, hm⟩
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hSub hyt⟩
  have hFdis : Pairwise (Disjoint on F) :=
    fun i j hij ↦ hVdis i.property j.property (fun he ↦ hij (Subtype.ext he))
  have hGmeasure (i : V) : b * m (G i) ≤ D ^ 2 * ∫⁻ y in F i, g y ∂m := by
    have hVinc : m (G i) ≤ D ^ 2 * m (F i) := by
      simpa only [G, F, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
        measure_ball_two_pow_le hD i.val.1 (hVW i.property).1.1 2
    have h := (hVW i.property).2.2.le
    rw [normalizedBall, lintegral_smul_measure, smul_eq_mul, mul_comm, ← div_eq_mul_inv] at h
    have hB := (ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos m i.val.1 (hVW i.property).1.1).ne')
      (Or.inl measure_ball_ne_top)).mp h
    calc
      _ ≤ b * (D ^ 2 * m (F i)) := mul_le_mul_of_nonneg_left hVinc bot_le
      _ = D ^ 2 * (b * m (F i)) := by ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hB bot_le
  have hCost : b * m (B ∩ E) ≤ D ^ 4 * a * m B := by
    calc
      _ ≤ b * ∑' i : V, m (G i) :=
        mul_le_mul_of_nonneg_left ((measure_mono hInc).trans (measure_iUnion_le G)) bot_le
      _ = ∑' i : V, b * m (G i) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' i : V, D ^ 2 * ∫⁻ y in F i, g y ∂m := tsum_le_tsum hGmeasure
      _ = D ^ 2 * ∫⁻ y in ⋃ i : V, F i, g y ∂m := by
        rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun _ ↦ measurableSet_ball) hFdis]
      _ ≤ D ^ 2 * (a * (D ^ 2 * m B)) := by
        apply mul_le_mul_of_nonneg_left _ bot_le
        exact (lintegral_mono_set (iUnion_subset fun i : V ↦ hWsub i (hVW i.property))).trans
          ((lintegral_ball_le_localMaximalAverage g hsU
            ((mul_le_mul_of_nonneg_left hs.2 (by norm_num)).trans hSL) hCx).trans
            (mul_le_mul hxa hCoverVol bot_le bot_le))
      _ = _ := by rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]; ac_rfl
  change (∫⁻ y, E.indicator (fun _ ↦ 1) y ∂normalizedBall m z s) ≤ _
  rw [normalizedBall, lintegral_smul_measure, smul_eq_mul, lintegral_indicator hE,
    setLIntegral_const, one_mul, Measure.restrict_apply hE, inter_comm, mul_comm, ← div_eq_mul_inv]
  apply (ENNReal.div_le_iff (measure_ball_pos m z hs₀).ne' measure_ball_ne_top).mpr
  calc
    _ ≤ (D ^ 4 * a * m B) / b :=
      (ENNReal.le_div_iff_mul_le (Or.inl hb₀) (Or.inl hbT)).mpr (by rw [mul_comm]; exact hCost)
    _ = _ := by simp only [div_eq_mul_inv]; ac_rfl

end WalkDimensions
