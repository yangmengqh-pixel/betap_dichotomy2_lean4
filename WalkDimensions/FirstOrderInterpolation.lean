import WalkDimensions.LipschitzBallTents
import WalkDimensions.EnergyMeasureConstruction
import WalkDimensions.LocalBesov
import WalkDimensions.CoreCutoffs

/-!
# Lipschitz interpolants of a compact plateau test with small first-order cost
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [SFinite m] [m.IsOpenPosMeasure]
  {q : ℝ} (E : PEnergy m q)

theorem exists_lipschitz_plate_interpolants {β : ℝ} (hβ : 0 < β) (hvol : VolumeDoubling m)
    (hPI : E.Poincare E.energyMeasure β) (o : X) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ r ∈ Ioo (0 : ℝ) (1 / 8), ∃ (v : X → ℝ) (K : ℝ≥0),
      LipschitzWith K v ∧ EqOn v (fun _ ↦ 1) (ball o (1 / 2)) ∧
      EqOn v (fun _ ↦ 0) (ball o 3)ᶜ ∧
      (∫⁻ x, ballSlope v r x ^ q ∂m) ≤ C * ENNReal.ofReal (r ^ (β - q)) := by
  classical
  have hq := zero_lt_one.trans E.one_lt
  obtain ⟨f, u, hu, huc, hfu, _, hu₁, huSupp⟩ :=
    E.exists_core_cutoff_of_isCompact_subset_isOpen (isCompact_closedBall o 1) isOpen_ball
      (closedBall_subset_ball (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨N, hN, hPacking⟩ := exists_card_le_of_separated_centres hvol (R := 6) (by norm_num)
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨Q, hQ, hPairs⟩ := exists_sum_ball_average_oscillation_le hvol (A := 4) (by norm_num)
  obtain ⟨J, _, hJ, hLocal⟩ := E.global_besov_bound hvol hPI E.energyMeasure_univ
  let S := ENNReal.ofReal (((N : ℝ) + 1) ^ q * (N : ℝ) ^ (q - 1))
  let D := S * Q * J * (E.energy f : ℝ≥0∞) * ENNReal.ofReal ((6 : ℝ) ^ β)
  have hD : D ≠ ∞ := by
    dsimp only [D, S]
    finiteness
  refine ⟨D, hD, fun r hr ↦ ?_⟩
  have hr₀ : 0 < r := hr.1
  obtain ⟨t, ht, hsep, hcover⟩ := exists_finset_separated_ball_cover (isCompact_closedBall o 4) hr₀
  let a (z : X) := ⨍ w in ball z r, u w ∂m
  let v := tentInterpolant t r a
  obtain ⟨K, hK⟩ := tentInterpolant_lipschitz t hr₀ a
  have hCover (x : X) (hx : x ∈ closedBall o 4) : ∃ z ∈ t, x ∈ ball z r :=
    let ⟨z, hz, hzX⟩ := mem_iUnion₂.mp (hcover hx)
    ⟨z, hz, hzX⟩
  have hVal (x : X) (hx : x ∈ ball o (1 / 2)) : v x = 1 := by
    obtain ⟨z, hz, hzx⟩ := hCover x (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hx))
    apply tentInterpolant_eq_const t hr₀ a hz hzx
    intro y hy hyt
    have hxy : dist x y < 2 * r := lt_of_not_ge (fun h ↦ hyt (ballTent_eq_zero hr₀ h))
    change (⨍ w in ball y r, u w ∂m) = 1
    have he : u =ᵐ[m.restrict (ball y r)] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [ae_restrict_mem (μ := m) (s := ball y r) measurableSet_ball] with w hw
      apply hu₁
      apply mem_closedBall.mpr
      have h' := dist_triangle w x o
      have h'' := dist_triangle w y x
      rw [dist_comm y x] at h''
      linarith only [h', h'', mem_ball.mp hw, hxy, mem_ball.mp hx, hr.2]
    rw [average_congr he]
    exact setAverage_const (measure_ball_pos m y hr₀).ne' measure_ball_ne_top _
  have hZero (x : X) (hx : 2 + 3 * r ≤ dist x o) : v x = 0 := by
    unfold v tentInterpolant
    apply Finset.sum_eq_zero
    intro y hy
    by_cases hBall : 2 * r ≤ dist x y
    · rw [ballTent_eq_zero hr₀ hBall, zero_div, mul_zero]
    · suffices a y = 0 by rw [this, zero_mul]
      have he : u =ᵐ[m.restrict (ball y r)] (fun _ ↦ (0 : ℝ)) := by
        filter_upwards [ae_restrict_mem (μ := m) (s := ball y r) measurableSet_ball] with w hw
        apply notMem_support.mp
        intro hSupp
        have hh := mem_ball.mp (huSupp (subset_closure hSupp))
        have h' := dist_triangle x y w
        have h'' := dist_triangle x w o
        rw [dist_comm y w] at h'
        linarith only [hh, h', h'', mem_ball.mp hw, lt_of_not_ge hBall, hx]
      change (⨍ w in ball y r, u w ∂m) = 0
      rw [average_congr he]
      exact setAverage_const (measure_ball_pos m y hr₀).ne' measure_ball_ne_top _
  refine ⟨v, K, hK, (fun x hx ↦ hVal x hx), ?_, ?_⟩
  · intro x hx
    exact hZero x (by
      have h : (3 : ℝ) ≤ dist x o := le_of_not_gt (fun h ↦ hx (mem_ball.mpr h))
      linarith only [h, hr.2])
  let nb (z : X) := t.filter (fun y ↦ dist y z ≤ 4 * r)
  let P (z : X) (x : X) : ℝ≥0∞ :=
    (ball z r).indicator (fun _ ↦ ∑ y ∈ nb z, ENNReal.ofReal |a z - a y| ^ q) x
  let C := S * ENNReal.ofReal (r ^ (-q))
  have hBound (x : X) : ballSlope v r x ^ q ≤ C * ∑ z ∈ t, P z x := by
    by_cases hx : x ∈ ball o 3
    · obtain ⟨z, hz, hxz⟩ := hCover x (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hx))
      let B := t.filter (fun y ↦ dist y x ≤ 3 * r)
      have hBsub : B ⊆ t := Finset.filter_subset _ _
      have hBcard : B.card ≤ N := by
        apply hPacking x (r / 2) (by positivity) B
        · intro y hy
          exact (Finset.mem_filter.mp hy).2.trans_eq (by ring)
        · intro y hy w hw hne
          rw [show 2 * (r / 2) = r by ring]
          exact hsep (hBsub hy) (hBsub hw) hne
      have hNB : B ⊆ nb z := by
        intro y hy
        apply Finset.mem_filter.mpr
        refine ⟨hBsub hy, (dist_triangle y x z).trans ?_⟩
        linarith only [(Finset.mem_filter.mp hy).2, mem_ball.mp hxz]
      let L := (((N : ℝ) + 1) / r) * ∑ y ∈ B, |a y - a z|
      have hL : 0 ≤ L := by dsimp only [L]; positivity
      have hSlope : ballSlope v r x ≤ ENNReal.ofReal L := by
        apply iSup_le
        intro y
        let w := (y : X)
        change ENNReal.ofReal (|v x - v w| / dist x w) ≤ _
        by_cases hEq : x = w
        · rw [hEq, sub_self, abs_zero, zero_div, ENNReal.ofReal_zero]
          exact bot_le
        have hdist := dist_pos.mpr hEq
        have hwR : dist w x < r := y.property
        have hwK : w ∈ closedBall o 4 := mem_closedBall.mpr ((dist_triangle w x o).trans
          (by linarith only [hwR, mem_ball.mp hx, hr.2]))
        obtain ⟨j, hj, hwj⟩ := hCover w hwK
        have hZeros (l : X) (hl : l ∈ t) (hlB : l ∉ B) : ballTent r l x = 0 ∧ ballTent r l w = 0 := by
          have hB : 3 * r < dist l x := lt_of_not_ge fun h ↦ hlB (Finset.mem_filter.mpr ⟨hl, h⟩)
          have h' := dist_triangle l w x
          rw [dist_comm l x] at hB
          rw [dist_comm l w, dist_comm l x] at h'
          exact ⟨ballTent_eq_zero hr₀ (by linarith only [hB, hr₀]),
            ballTent_eq_zero hr₀ (by linarith only [hB, h', hwR])⟩
        have h := abs_tentInterpolant_sub_le t B hr₀ a hz hj hxz hwj hBsub hZeros
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_iff₀ hdist).mpr
        apply h.trans
        have hcard : (B.card : ℝ) ≤ N := by exact_mod_cast hBcard
        calc
          _ ≤ ((N : ℝ) + 1) * (dist x w / r) * ∑ l ∈ B, |a l - a z| := by gcongr
          _ = _ := by dsimp only [L]; ring
      refine (ENNReal.rpow_le_rpow hSlope hq.le).trans ?_
      have hsum : (∑ y ∈ B, |a y - a z|) ^ q ≤ (N : ℝ) ^ (q - 1) *
          ∑ y ∈ B, |a y - a z| ^ q :=
        (Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg B E.one_lt.le (fun y _ ↦ abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _)
            (by exact_mod_cast hBcard) (sub_nonneg.mpr E.one_lt.le)) (by positivity))
      have hP : (ENNReal.ofReal L) ^ q ≤ C * P z x := by
        rw [ENNReal.ofReal_rpow_of_nonneg hL hq.le]
        dsimp only [L, C, S, P]
        rw [indicator_of_mem hxz, Real.mul_rpow (by positivity) (by positivity)]
        refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum (by positivity))).trans ?_
        rw [Real.div_rpow (by positivity) hr₀.le, div_eq_mul_inv, ← Real.rpow_neg hr₀.le]
        let K := ((N : ℝ) + 1) ^ q * (N : ℝ) ^ (q - 1) * r ^ (-q)
        have hK₀ : 0 ≤ K := by dsimp only [K]; positivity
        calc
          _ = ENNReal.ofReal K * ∑ y ∈ B, ENNReal.ofReal |a y - a z| ^ q := by
            simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq.le]
            rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ Real.rpow_nonneg (abs_nonneg _) _),
              ← ENNReal.ofReal_mul hK₀]
            congr 1
            dsimp only [K]
            ring
          _ ≤ ENNReal.ofReal K * ∑ y ∈ nb z, ENNReal.ofReal |a z - a y| ^ q := by
            simp_rw [abs_sub_comm (a z)]
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset hNB) bot_le
          _ = _ := by
            dsimp only [K]
            rw [ENNReal.ofReal_mul (by positivity)]
      exact hP.trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum
        (f := fun z ↦ P z x) (fun _ _ ↦ bot_le) hz) bot_le)
    · have hxd : 3 ≤ dist x o := le_of_not_gt (fun h ↦ hx (mem_ball.mpr h))
      have hZ : ballSlope v r x = 0 := by
        apply le_antisymm _ bot_le
        apply iSup_le
        intro y
        change ENNReal.ofReal (|v x - v y| / dist x (y : X)) ≤ 0
        have h' := dist_triangle x (y : X) o
        have hy : dist x (y : X) < r := by rw [dist_comm]; exact y.property
        rw [hZero x (by linarith only [hxd, hr.2]), hZero y (by linarith only [h', hy, hxd, hr.2]),
          sub_self, abs_zero, zero_div, ENNReal.ofReal_zero]
      rw [hZ, ENNReal.zero_rpow_of_pos hq]
      exact bot_le
  have hPm (z : X) : Measurable (P z) := measurable_const.indicator measurableSet_ball
  apply (lintegral_mono hBound).trans
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun z _ ↦ hPm z), lintegral_finsetSum _ (fun z _ ↦ hPm z)]
  have hInt (z : X) : (∫⁻ x, P z x ∂m) =
      ∑ y ∈ nb z, m (ball z r) * ENNReal.ofReal |a z - a y| ^ q := by
    dsimp only [P]
    rw [lintegral_indicator measurableSet_ball, setLIntegral_const, mul_comm, Finset.mul_sum]
  simp_rw [hInt]
  have hPairs' := hPairs E.one_lt.le t r hr₀ hsep nb
    (fun z ↦ Finset.filter_subset _ _) (fun z y hy ↦ (Finset.mem_filter.mp hy).2)
    u hu.measurable (hu.memLp_of_hasCompactSupport huc)
  have hR : 0 < 6 * r := by positivity
  have hM := (le_iSup (fun s : Ioi (0 : ℝ) ↦ besovEnergy m q β univ (f : RealLp m q) s)
    (⟨6 * r, hR⟩ : Ioi (0 : ℝ))).trans (hLocal f)
  dsimp only at hM
  rw [besovEnergy_congr_ae hfu, besovEnergy, Measure.restrict_univ] at hM
  have hMom : (∫⁻ x, ballMoment m q u (6 * r) x ∂m) ≤
      ENNReal.ofReal ((6 * r) ^ β) * (J * (E.energy f : ℝ≥0∞)) := by
    let A := ENNReal.ofReal (6 * r) ^ β
    have hA : A ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hR) ENNReal.ofReal_ne_top).ne'
    have hAT : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hβ.le ENNReal.ofReal_ne_top
    have hh := mul_le_mul_of_nonneg_left hM (show 0 ≤ A from bot_le)
    rw [ENNReal.rpow_neg, ← mul_assoc, ENNReal.mul_inv_cancel hA hAT, one_mul] at hh
    rw [← ENNReal.ofReal_rpow_of_pos hR]
    exact hh
  have hPairs'' := hPairs'
  norm_num at hPairs''
  apply (mul_le_mul_of_nonneg_left hPairs'' bot_le).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMom bot_le) bot_le).trans_eq
  dsimp only [D, C]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hr₀.le, ENNReal.ofReal_mul (by positivity)]
  calc
    _ = (S * Q * J * (E.energy f : ℝ≥0∞) * ENNReal.ofReal ((6 : ℝ) ^ β)) *
        (ENNReal.ofReal (r ^ β) * ENNReal.ofReal (r ^ (-q))) := by ac_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr₀.le _), ← Real.rpow_add hr₀, sub_eq_add_neg]

end WalkDimensions.PEnergy
