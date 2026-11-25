import WalkDimensions.EnergyClosedness

/-!
# Vanishing energy under a midpoint bound

For a sequence converging to zero in (L^p), a lower bound on the
energy of earlier midpoints forces graph-norm convergence.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem tendsto_of_eventually_le_add_vanishing {u : ℕ → ℝ}
    (hbdd : BddBelow (range u))
    (hupper : ∀ n, ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ m > n, u m ≤ u n + err m) :
    Tendsto u atTop (𝓝 (⨅ n, u n)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun n ↦ hb.trans_le (ciInf_le hbdd n)
  · intro b hb
    obtain ⟨c, hc₁, hc₂⟩ := exists_between hb
    obtain ⟨v, ⟨n, rfl⟩, hn⟩ := exists_lt_of_csInf_lt (range_nonempty u) hc₁
    obtain ⟨err, hErr, hle⟩ := hupper n
    filter_upwards [hErr.eventually_lt_const (sub_pos.mpr hc₂), eventually_gt_atTop n]
      with m hε hm
    linarith only [hle m hm, hε, hn]

theorem tendsto_root_zero_of_midpoint_error (f : ℕ → E.domain)
    (hLp : Tendsto (fun n ↦ ‖(f n : RealLp m p)‖) atTop (𝓝 0))
    (err : ℕ → ℝ) (hErr : Tendsto err atTop (𝓝 0))
    (hmid : ∀ i j n : ℕ, i ≤ n → j ≤ n →
      E.rootSeminorm (f n) ≤ E.rootSeminorm ((1 / 2 : ℝ) • (f i + f j)) + err n) :
    Tendsto (fun n ↦ E.rootSeminorm (f n)) atTop (𝓝 0) := by
  let : SeminormedAddCommGroup E.domain :=
    E.graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : CompleteSpace E.domain := E.graph_complete
  let u (n : ℕ) := E.rootSeminorm (f n)
  have hu₀ (n : ℕ) : 0 ≤ u n := apply_nonneg _ _
  have hb : BddBelow (range u) := ⟨0, forall_mem_range.mpr hu₀⟩
  let a := ⨅ n, u n
  have ha : 0 ≤ a := le_ciInf hu₀
  have halim : Tendsto u atTop (𝓝 a) := tendsto_of_eventually_le_add_vanishing hb fun n ↦ by
    refine ⟨err, hErr, fun m hm ↦ ?_⟩
    have h := hmid n n m hm.le hm.le
    rwa [← two_smul ℝ (f n), smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h
  have hmidlim (i j : ℕ) : a ≤ E.rootSeminorm ((1 / 2 : ℝ) • (f i + f j)) := by
    apply le_of_tendsto_of_tendsto halim
    · simpa only [add_zero] using hErr.const_add (E.rootSeminorm ((1 / 2 : ℝ) • (f i + f j)))
    · filter_upwards [eventually_ge_atTop i, eventually_ge_atTop j] with n hi hj
      exact hmid i j n hi hj
  obtain ⟨q, hq, hclarkson⟩ := E.exists_clarkson_power
  let R (t : ℝ) := (2 * t) ^ q - (2 * a) ^ q
  have hRlim : Tendsto R (𝓝 a) (𝓝 0) := by
    have hcontinuous : Continuous (fun x : ℝ ↦ (2 * x) ^ q - (2 * a) ^ q) :=
      ((Real.continuous_rpow_const hq.le).comp (continuous_const.mul continuous_id)).sub continuous_const
    simpa only [R, sub_self] using hcontinuous.tendsto a
  have hdiff {t : ℝ} {i j : ℕ} (ht : 0 ≤ t) (hi : u i ≤ t) (hj : u j ≤ t) :
      E.rootSeminorm (f i - f j) ^ q ≤ R t := by
    have h := hmidlim i j
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    have hsum : (2 * a) ^ q ≤ E.rootSeminorm (f i + f j) ^ q :=
      Real.rpow_le_rpow (by positivity) (by linarith only [h]) hq.le
    have hClark := hclarkson (f i) (f j) t ht hi hj
    dsimp only [R]
    linarith only [hClark, hsum]
  have hCauchy : CauchySeq f := by
    refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
    let δ := ε / 3
    have hδ : 0 < δ := div_pos hε (by norm_num)
    have hRbound := hRlim.eventually_lt_const (Real.rpow_pos_of_pos hδ q)
    have hRnear : ∀ᶠ t in 𝓝[Set.Ioi a] a, R t < δ ^ q :=
      hRbound.filter_mono nhdsWithin_le_nhds
    obtain ⟨t, hRt, ht⟩ := (hRnear.and self_mem_nhdsWithin).exists
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((halim.eventually_lt_const ht).and (hLp.eventually_lt_const hδ))
    refine ⟨N, fun i hi j hj ↦ ?_⟩
    have hs : E.rootSeminorm (f i - f j) < δ :=
      (Real.rpow_lt_rpow_iff (apply_nonneg _ _) hδ.le hq).mp
        ((hdiff (ha.trans ht.le) (hN i hi).1.le (hN j hj).1.le).trans_lt hRt)
    have hnorm : ‖((f i - f j : E.domain) : RealLp m p)‖ < 2 * δ := by
      let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
      change ‖(f i : RealLp m p) - (f j : RealLp m p)‖ < _
      exact (norm_sub_le _ _).trans_lt (by linarith only [(hN i hi).2, (hN j hj).2])
    rw [dist_eq_norm]
    change E.graphSeminorm (f i - f j) < ε
    exact (E.graphSeminorm_le_add _).trans_lt (by dsimp [δ] at *; linarith only [hs, hnorm])
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hDist : Tendsto (fun n ↦ E.graphSeminorm (g - f n)) atTop (𝓝 0) := by
    change Tendsto (fun n ↦ ‖g - f n‖) atTop (𝓝 0)
    have h := ((continuous_const.dist continuous_id : Continuous (fun x : E.domain ↦ dist g x)).tendsto g).comp hg
    simpa only [dist_self, Function.comp_def, dist_eq_norm] using h
  have hG (n : ℕ) : ‖(g : RealLp m p)‖ ≤
      E.graphSeminorm (g - f n) + ‖(f n : RealLp m p)‖ := by
    let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
    have h := norm_add_le ((g : RealLp m p) - (f n : RealLp m p)) (f n : RealLp m p)
    rw [sub_add_cancel] at h
    exact h.trans (add_le_add_left (E.norm_le_graphSeminorm (g - f n)) _)
  have hzero : ‖(g : RealLp m p)‖ ≤ 0 :=
    ge_of_tendsto (by simpa only [zero_add] using hDist.add hLp) (Eventually.of_forall hG)
  have hg₀ : g = 0 := by
    let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
    exact Subtype.ext (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))
  have hroot : Continuous E.rootSeminorm := Seminorm.continuous_of_le
    (show Continuous E.graphSeminorm from continuous_norm) E.rootSeminorm_le_graphSeminorm
  simpa only [hg₀, map_zero, Function.comp_def] using (hroot.tendsto g).comp hg

theorem tendsto_root_zero_of_midpoint_control (f : ℕ → E.domain)
    (hLp : Tendsto (fun n ↦ ‖(f n : RealLp m p)‖) atTop (𝓝 0))
    (hmid : ∀ i j n : ℕ, i ≤ n → j ≤ n →
      E.rootSeminorm (f n) ≤ E.rootSeminorm ((1 / 2 : ℝ) • (f i + f j))) :
    Tendsto (fun n ↦ E.rootSeminorm (f n)) atTop (𝓝 0) :=
  E.tendsto_root_zero_of_midpoint_error f hLp (fun _ ↦ 0) tendsto_const_nhds
    (fun i j n hi hj ↦ by simpa only [add_zero] using hmid i j n hi hj)

end WalkDimensions.PEnergy
