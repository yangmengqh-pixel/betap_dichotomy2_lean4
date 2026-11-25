import WalkDimensions.CapacityCutoffs
import WalkDimensions.CoreCutoffs
import WalkDimensions.CoreLatticeConvergence
import WalkDimensions.EnergyMeasureClarkson

/-!
# Continuous quantitative cutoffs from the capacity upper bound
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
  {p : ℝ} (E : PEnergy m p)

set_option maxHeartbeats 3000000 in
theorem exists_core_approx_between {f : E.domain} (lo hi : E.CompactCore)
    (hlo : ∀ᵐ x ∂m, lo.toFun x ≤ (f : RealLp m p) x)
    (hhi : ∀ᵐ x ∂m, (f : RealLp m p) x ≤ hi.toFun x)
    (h01 : ∀ᵐ x ∂m, (f : RealLp m p) x ∈ Icc (0 : ℝ) 1)
    (hOrd : ∀ x, lo.toFun x ≤ hi.toFun x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E.CompactCore, (∀ x, lo.toFun x ≤ u.toFun x ∧ u.toFun x ≤ hi.toFun x) ∧
      (E.energy u.domainElement : ℝ) < E.energy f + ε := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  obtain ⟨g, hg⟩ := E.exists_core_graph_approximation f
  have hgLp : Tendsto (fun n ↦ ‖((g n).domainElement : RealLp m p) - (f : RealLp m p)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ E.norm_le_graphSeminorm _) hg
  have hgRoot : Tendsto (fun n ↦ E.rootSeminorm ((g n).domainElement - f)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun _ ↦ E.rootSeminorm_le_graphSeminorm _) hg
  have hgEnergy := E.tendsto_energyMeasure_real_of_root_sub hgRoot MeasurableSet.univ
  simp only [E.energyMeasure_univ, ENNReal.coe_toReal] at hgEnergy
  let clip := fun t : ℝ ↦ min (max t 0) 1
  have hclip : LipschitzWith 1 clip := (LipschitzWith.id.max_const 0).min_const 1
  have hclip0 : clip 0 = 0 := by norm_num [clip]
  let g₀ (n : ℕ) := (g n).mapLipschitz clip hclip hclip0
  let lower (n : ℕ) := (g₀ n).minAddConst lo (a := 0) le_rfl
  let upper (n : ℕ) := (g₀ n).sup lo
  let outer (n : ℕ) := (upper n).sup hi
  let u (n : ℕ) := (upper n).minAddConst hi (a := 0) le_rfl
  have h0E (n : ℕ) : (E.energy (g₀ n).domainElement : ℝ) ≤ E.energy (g n).domainElement := by
    rw [E.energy_eq_root_rpow, E.energy_eq_root_rpow]
    exact Real.rpow_le_rpow (apply_nonneg _ _) ((g n).root_mapLipschitz_le clip hclip hclip0)
      (zero_lt_one.trans E.one_lt).le
  have h0Lp (n : ℕ) : ‖((g₀ n).domainElement : RealLp m p) - f.val‖ ≤
      ‖((g n).domainElement : RealLp m p) - f.val‖ := by
    apply CompactCore.norm_sub_le_of_ae_abs_sub_le
    filter_upwards [(g₀ n).ae_eq, (g n).ae_eq, h01] with x h0 hx hf
    rw [h0, hx]
    have hh := hclip.dist_le_mul ((g n).toFun x) (f.val x)
    have he : clip (f.val x) = f.val x := by
      dsimp only [clip]
      rw [max_eq_left hf.1, min_eq_left hf.2]
    change |clip ((g n).toFun x) - f.val x| ≤ _
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, he] using hh
  have hUpperLp (n : ℕ) : ‖((upper n).domainElement : RealLp m p) - f.val‖ ≤
      ‖((g₀ n).domainElement : RealLp m p) - f.val‖ := by
    apply CompactCore.norm_sub_le_of_ae_abs_sub_le
    filter_upwards [(upper n).ae_eq, (g₀ n).ae_eq, hlo] with x hu hg hf
    rw [hu, hg, (g₀ n).sup_apply lo x]
    have hh := (LipschitzWith.id.max_const (lo.toFun x)).dist_le_mul ((g₀ n).toFun x) (f.val x)
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq, max_eq_left hf] using hh
  have hLowerLp (n : ℕ) :
      ‖((lower n).domainElement : RealLp m p) - (lo.domainElement : RealLp m p)‖ ≤
        ‖((g₀ n).domainElement : RealLp m p) - f.val‖ := by
    apply CompactCore.norm_sub_le_of_ae_abs_sub_le
    filter_upwards [(lower n).ae_eq, (g₀ n).ae_eq, lo.ae_eq, hlo] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃]
    change |min ((g₀ n).toFun x) (lo.toFun x + 0) - lo.toFun x| ≤ _
    have hh := (LipschitzWith.id.min_const (lo.toFun x)).dist_le_mul ((g₀ n).toFun x) (f.val x)
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq, min_eq_right h₄, add_zero] using hh
  have hOuterLp (n : ℕ) :
      ‖((outer n).domainElement : RealLp m p) - (hi.domainElement : RealLp m p)‖ ≤
        ‖((upper n).domainElement : RealLp m p) - f.val‖ := by
    apply CompactCore.norm_sub_le_of_ae_abs_sub_le
    filter_upwards [(outer n).ae_eq, (upper n).ae_eq, hi.ae_eq, hhi] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, (upper n).sup_apply hi x]
    have hh := (LipschitzWith.id.max_const (hi.toFun x)).dist_le_mul ((upper n).toFun x) (f.val x)
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq, max_eq_right h₄] using hh
  have h₁ := CompactCore.eventually_lt_energy_of_norm_sub_tendsto
    (f := lo) (g := lower) (sub_lt_self (E.energy lo.domainElement : ℝ) (show 0 < ε / 3 by positivity))
    (squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hLowerLp n).trans (h0Lp n)) hgLp)
  have h₂ := CompactCore.eventually_lt_energy_of_norm_sub_tendsto
    (f := hi) (g := outer) (sub_lt_self (E.energy hi.domainElement : ℝ) (show 0 < ε / 3 by positivity))
    (squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hOuterLp n).trans ((hUpperLp n).trans (h0Lp n))) hgLp)
  obtain ⟨n, hn, hn₁, hn₂⟩ := ((hgEnergy.eventually_lt_const (lt_add_of_pos_right _ (show 0 < ε / 3 by
    positivity))).and (h₁.and h₂)).exists
  refine ⟨u n, ?_, ?_⟩
  · intro x
    change lo.toFun x ≤ min ((upper n).toFun x) (hi.toFun x + 0) ∧
      min ((upper n).toFun x) (hi.toFun x + 0) ≤ hi.toFun x
    rw [add_zero, (g₀ n).sup_apply lo x]
    exact ⟨le_min (le_max_right _ _) (hOrd x), min_le_right _ _⟩
  · have he₁ : (E.energy (upper n).domainElement : ℝ) + E.energy (lower n).domainElement =
        E.energy (g₀ n).domainElement + E.energy lo.domainElement :=
      congrArg NNReal.toReal ((g₀ n).energy_sup_add_min lo)
    have he₂ : (E.energy (outer n).domainElement : ℝ) + E.energy (u n).domainElement =
        E.energy (upper n).domainElement + E.energy hi.domainElement :=
      congrArg NNReal.toReal ((upper n).energy_sup_add_min hi)
    linarith only [he₁, he₂, h0E n, hn, hn₁, hn₂]

variable [m.IsOpenPosMeasure]

theorem exists_compact_core_cutoff_of_capacity {β : ℝ} (hcap : E.CapacityUpperBound β)
    (hvol : VolumeDoubling m) :
    ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ (x : X) (r : ℝ), 0 < r →
      ∃ u : E.CompactCore, (∀ y, u.toFun y ∈ Icc (0 : ℝ) 1) ∧
        EqOn u.toFun (fun _ ↦ 1) (ball x r) ∧ tsupport u.toFun ⊆ ball x (A * r) ∧
        (E.energy u.domainElement : ℝ) ≤ C * r ^ (-β) * (m (ball x r)).toReal := by
  obtain ⟨C, A, hC, hA, hCut⟩ := E.exists_measurable_ball_cutoff hcap
  obtain ⟨D, hD, hvol⟩ := hvol
  have hA₀ := zero_lt_one.trans hA
  refine ⟨2 * C * (2 : ℝ) ^ (-β) * D, 3 * A, by positivity, by linarith, fun x r hr ↦ ?_⟩
  obtain ⟨f, v, hfv, _, _, hvRange, hv1, hv0, hvE⟩ := hCut x (2 * r) (by positivity)
  have hloSub : closedBall x r ⊆ ball x (2 * r) := closedBall_subset_ball (by linarith)
  have hhiSub : closedBall x (A * (2 * r)) ⊆ ball x (3 * A * r) :=
    closedBall_subset_ball (by nlinarith only [mul_pos hA₀ hr])
  obtain ⟨a, lo, hlo, hloC, halo, hLoRange, hLoOne, hLoSupp⟩ :=
    E.exists_core_cutoff_of_isCompact_subset_isOpen (isCompact_closedBall x r) isOpen_ball hloSub
  obtain ⟨b, hi, hhi, hhiC, hbhi, hHiRange, hHiOne, hHiSupp⟩ :=
    E.exists_core_cutoff_of_isCompact_subset_isOpen (isCompact_closedBall x (A * (2 * r))) isOpen_ball hhiSub
  let lo₀ : E.CompactCore := ⟨a, lo, halo, hlo, hloC⟩
  let hi₀ : E.CompactCore := ⟨b, hi, hbhi, hhi, hhiC⟩
  have hLo (y : X) : lo y ≤ v y := by
    by_cases hy : y ∈ ball x (2 * r)
    · rw [hv1 hy]
      exact (hLoRange y).2
    · have he := notMem_support.mp (fun hz ↦ hy (hLoSupp (subset_closure hz)))
      rw [he]
      exact (hvRange y).1
  have hHi (y : X) : v y ≤ hi y := by
    by_cases hy : y ∈ closedBall x (A * (2 * r))
    · rw [hHiOne hy]
      exact (hvRange y).2
    · rw [hv0 (fun hz ↦ hy (ball_subset_closedBall hz))]
      exact (hHiRange y).1
  let K := C * (2 * r) ^ (-β) * (m (ball x (2 * r))).toReal
  have hK : 0 < K := mul_pos (mul_pos hC (Real.rpow_pos_of_pos (by positivity : 0 < 2 * r) _))
    (ENNReal.toReal_pos (measure_ball_pos m x (by positivity : 0 < 2 * r)).ne' measure_ball_ne_top)
  have hEf : (E.energy f : ℝ) ≤ K := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top) hvE
    simpa only [ENNReal.coe_toReal, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg (by positivity : 0 ≤ 2 * r) _))] using h
  obtain ⟨u, hu, huE⟩ := E.exists_core_approx_between lo₀ hi₀
    (hfv.mono fun y hy ↦ hy ▸ hLo y) (hfv.mono fun y hy ↦ hy ▸ hHi y)
    (hfv.mono fun y hy ↦ hy ▸ hvRange y)
    (fun y ↦ (hLo y).trans (hHi y)) hK
  have hVol := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top) (hvol x r hr)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le] at hVol
  refine ⟨u, fun y ↦ ⟨(hLoRange y).1.trans (hu y).1, (hu y).2.trans (hHiRange y).2⟩, ?_, ?_, ?_⟩
  · intro y hy
    exact le_antisymm ((hu y).2.trans (hHiRange y).2)
      ((hLoOne (ball_subset_closedBall hy)).ge.trans (hu y).1)
  · apply (closure_mono (show support u.toFun ⊆ support hi from ?_)).trans hHiSupp
    intro y hy h
    exact hy (le_antisymm ((hu y).2.trans_eq h) ((hLoRange y).1.trans (hu y).1))
  · apply huE.le.trans ((add_le_add_left hEf K).trans ?_)
    dsimp only [K]
    rw [← two_mul, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
    have h := mul_le_mul_of_nonneg_left hVol
      (show 0 ≤ 2 * (C * (2 ^ (-β) * r ^ (-β))) by positivity)
    calc
      _ = 2 * (C * ((2 : ℝ) ^ (-β) * r ^ (-β))) * (m (ball x (2 * r))).toReal := by ring
      _ ≤ _ := h.trans_eq (by ring)

end WalkDimensions.PEnergy
