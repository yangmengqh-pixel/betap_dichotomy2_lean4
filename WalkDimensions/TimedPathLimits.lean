import WalkDimensions.TimedPaths
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Compactness of bounded-duration paths and monotone lower bounds on costs
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace WalkDimensions.TimedPath

variable {X : Type*} [MetricSpace X] [ProperSpace X] {x y : X}

private theorem exists_tendsto_subsequence (γ : ℕ → TimedPath x y) {T : ℝ}
    (hT : ∀ n, (γ n).duration ≤ T) :
    ∃ (η : TimedPath x y) (n : ℕ → ℕ), StrictMono n ∧ η.duration ≤ T ∧
      Tendsto (fun k ↦ (γ (n k)).duration) atTop (𝓝 η.duration) ∧
      ∀ t ∈ Icc 0 T, Tendsto (fun k ↦ (γ (n k)).toFun t) atTop (𝓝 (η.toFun t)) := by
  let I := Icc (0 : ℝ) T
  have hT₀ : 0 ≤ T := (γ 0).duration_nonneg.trans (hT 0)
  have : CompactSpace I := isCompact_iff_compactSpace.mp (isCompact_Icc (a := (0 : ℝ)) (b := T))
  let F (n : ℕ) : I →ᵇ X := BoundedContinuousFunction.mkOfCompact
    ⟨fun t ↦ (γ n).toFun t, (γ n).lipschitz.continuous.comp continuous_subtypeVal⟩
  let S := closedBall x T
  have hRange (n : ℕ) (t : I) : F n t ∈ S := by
    change dist ((γ n).toFun t) x ≤ T
    have h := (γ n).lipschitz.dist_le_mul t 0
    rw [(γ n).source, NNReal.coe_one, one_mul, Real.dist_eq, sub_zero,
      abs_of_nonneg t.property.1] at h
    exact h.trans t.property.2
  have hLip (n : ℕ) : LipschitzWith 1 (F n) :=
    (γ n).lipschitz.comp (LipschitzWith.subtypeVal I) |>.weaken (by norm_num)
  have hEq : Equicontinuous ((↑) : range F → I → X) := by
    apply equicontinuous_of_continuity_modulus id tendsto_id _
    rintro s t ⟨f, n, rfl⟩
    simpa only [id_eq, NNReal.coe_one, one_mul] using (hLip n).dist_le_mul s t
  have hCompact : IsCompact (closure (range F)) := BoundedContinuousFunction.arzela_ascoli
    S (isCompact_closedBall _ _) _ (fun f t ⟨n, hn⟩ ↦ hn ▸ hRange n t) hEq
  obtain ⟨⟨d, G⟩, ⟨hd, hG⟩, σ, hσ, hlim⟩ := (isCompact_Icc.prod hCompact).tendsto_subseq
    (x := fun n ↦ ((γ n).duration, F n)) (fun n ↦
      ⟨⟨(γ n).duration_nonneg, hT n⟩, subset_closure (mem_range_self n)⟩)
  change Tendsto (fun k ↦ ((γ (σ k)).duration, F (σ k))) atTop (𝓝 (d, G)) at hlim
  have hlimD : Tendsto (fun n ↦ (γ (σ n)).duration) atTop (𝓝 d) :=
    (continuous_fst.continuousAt (x := (d, G))).tendsto.comp hlim
  have hlimG : Tendsto (fun n ↦ F (σ n)) atTop (𝓝 G) :=
    (continuous_snd.continuousAt (x := (d, G))).tendsto.comp hlim
  have hPt (t : I) : Tendsto (fun n ↦ (γ (σ n)).toFun t) atTop (𝓝 (G t)) :=
    (BoundedContinuousFunction.lipschitz_eval_const t).continuous.continuousAt.tendsto.comp hlimG
  have hGLip : LipschitzWith 1 G := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    exact le_of_tendsto ((hPt s).dist (hPt t))
      (Eventually.of_forall fun k ↦ (hLip (σ k)).dist_le_mul s t)
  let G' (t : ℝ) := G (projIcc 0 T hT₀ t)
  have hG' : LipschitzWith 1 G' := by
    change LipschitzWith 1 (⇑G ∘ projIcc 0 T hT₀)
    simpa only [one_mul] using hGLip.comp (LipschitzWith.projIcc hT₀)
  have hGa : G' 0 = x := by
    change G (projIcc 0 T hT₀ 0) = x
    rw [projIcc_of_mem _ (left_mem_Icc.mpr hT₀)]
    apply tendsto_nhds_unique (hPt ⟨0, left_mem_Icc.mpr hT₀⟩)
    simpa only [(γ _).source] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))
  have hGz : G' d = y := by
    change G (projIcc 0 T hT₀ d) = y
    rw [projIcc_of_mem _ hd]
    have hDist := (hPt ⟨d, hd⟩).dist (tendsto_const_nhds (x := y))
    have hlim₀ : Tendsto (fun k ↦ |d - (γ (σ k)).duration|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero] using ((tendsto_const_nhds (x := d)).sub hlimD).abs
    have hDist₀ : Tendsto (fun k ↦ dist ((γ (σ k)).toFun d) y) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) hlim₀
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, (γ (σ k)).target] using
        (γ (σ k)).lipschitz.dist_le_mul d (γ (σ k)).duration
    exact dist_eq_zero.mp (tendsto_nhds_unique hDist hDist₀)
  refine ⟨⟨d, hd.1, G', hG', hGa, hGz⟩, σ, hσ, hd.2, hlimD, ?_⟩
  intro t ht
  change Tendsto _ _ (𝓝 (G (projIcc 0 T hT₀ t)))
  rw [projIcc_of_mem _ ht]
  exact hPt ⟨t, ht⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- A bound along increasing continuous approximations to a weight passes
to a single path with the same time budget. -/
theorem exists_cost_le_of_monotone_approx {g : ℕ → X → ℝ≥0∞}
    (hMono : Monotone g) (hg : ∀ k, Continuous (g k)) {T : ℝ} {A : ℝ≥0∞}
    (h : ∀ k, ∃ γ : TimedPath x y, γ.duration ≤ T ∧ γ.cost (g k) ≤ A) :
    ∃ η : TimedPath x y, η.duration ≤ T ∧ η.cost (fun z ↦ ⨆ k, g k z) ≤ A := by
  choose γ hT hCost using h
  obtain ⟨η, n, hn, hη, hdur, hPoint⟩ := exists_tendsto_subsequence γ hT
  refine ⟨η, hη, ?_⟩
  unfold TimedPath.cost
  change (∫⁻ t in Ioc 0 η.duration, ⨆ k, g k (η.toFun t) ∂volume) ≤ A
  rw [lintegral_iSup (f := fun k t ↦ g k (η.toFun t))
    (fun k ↦ (hg k).measurable.comp η.lipschitz.continuous.measurable)
    (fun i j hij t ↦ hMono hij _)]
  apply iSup_le
  intro k
  let Q := Ioo (0 : ℝ) η.duration
  have hvol : volume.restrict (Ioc 0 η.duration) = volume.restrict Q :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  rw [hvol]
  let F (j : ℕ) (t : ℝ) :=
    (Ioc (0 : ℝ) (γ (n j)).duration).indicator (fun s ↦ g (n j) ((γ (n j)).toFun s)) t
  have hF (j : ℕ) : Measurable (F j) :=
    ((hg (n j)).measurable.comp (γ (n j)).lipschitz.continuous.measurable).indicator measurableSet_Ioc
  have hLe : ∀ᵐ t ∂volume.restrict Q, g k (η.toFun t) ≤ liminf (fun j ↦ F j t) atTop := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Q) measurableSet_Ioo] with t ht
    have htI : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le.trans hη⟩
    have hFsub := (hg k).continuousAt.tendsto.comp (hPoint t htI)
    have hNear := hdur.eventually_const_lt ht.2
    have hNk := hn.tendsto_atTop.eventually_ge_atTop k
    have hQl : ∀ᶠ j in atTop, g k ((γ (n j)).toFun t) ≤ F j t := by
      filter_upwards [hNear, hNk] with j hj hjk
      dsimp only [F]
      rw [indicator_of_mem (show t ∈ Ioc 0 (γ (n j)).duration from ⟨ht.1, hj.le⟩)]
      exact hMono hjk _
    exact hFsub.liminf_eq ▸ liminf_le_liminf hQl
  apply (lintegral_mono_ae hLe).trans
  apply (lintegral_liminf_le (fun k ↦ hF k)).trans
  apply liminf_le_of_frequently_le _
    (by isBoundedDefault)
  exact Frequently.of_forall fun j ↦ by
    apply (lintegral_mono_set (subset_univ Q)).trans
    rw [Measure.restrict_univ, show F j = _ from rfl, lintegral_indicator measurableSet_Ioc]
    exact hCost (n j)

end WalkDimensions.TimedPath
