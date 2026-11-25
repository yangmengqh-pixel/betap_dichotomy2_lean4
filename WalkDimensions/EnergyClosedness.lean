import WalkDimensions.EnergyClarkson
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Lower semicontinuity of the p-energy in Lp

A sequence with bounded energy that converges in Lp has a limit in the
energy domain. Clarkson's inequalities give graph-norm convergence of
near-minimizers inside successively smaller Lp balls about the limit.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

private theorem graphSeminorm_rpow (f : E.domain) :
    E.graphSeminorm f ^ p =
      E.rootSeminorm f ^ p + ‖(f : RealLp m p)‖ ^ p := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hN : 0 ≤ ‖(f : RealLp m p)‖ := ENNReal.toReal_nonneg
  have h : 0 ≤ (E.energy f : ℝ) + ‖(f : RealLp m p)‖ ^ p :=
    add_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg hN _)
  rw [E.graphSeminorm_apply, energyGraphNorm, ← Real.rpow_mul h,
    inv_mul_cancel₀ hp.ne', Real.rpow_one, E.energy_eq_root_rpow]

theorem rootSeminorm_le_graphSeminorm (f : E.domain) :
    E.rootSeminorm f ≤ E.graphSeminorm f := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  apply (Real.rpow_le_rpow_iff (apply_nonneg _ _) (apply_nonneg _ _) hp).1
  rw [E.graphSeminorm_rpow]
  have hN : 0 ≤ ‖(f : RealLp m p)‖ := ENNReal.toReal_nonneg
  exact le_add_of_nonneg_right (Real.rpow_nonneg hN _)

theorem norm_le_graphSeminorm (f : E.domain) :
    ‖(f : RealLp m p)‖ ≤ E.graphSeminorm f := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hN : 0 ≤ ‖(f : RealLp m p)‖ := ENNReal.toReal_nonneg
  apply (Real.rpow_le_rpow_iff hN (apply_nonneg _ _) hp).1
  rw [E.graphSeminorm_rpow]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (apply_nonneg _ _) _)

theorem graphSeminorm_le_add (f : E.domain) :
    E.graphSeminorm f ≤ E.rootSeminorm f + ‖(f : RealLp m p)‖ := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hN : 0 ≤ ‖(f : RealLp m p)‖ := ENNReal.toReal_nonneg
  have h := Real.add_rpow_le_rpow_add (apply_nonneg E.rootSeminorm f) hN E.one_lt.le
  apply (Real.rpow_le_rpow_iff (apply_nonneg _ _)
    (add_nonneg (apply_nonneg _ _) hN) hp).1
  rw [E.graphSeminorm_rpow]
  exact h

/-- Closedness of the root-energy sublevel sets in the ambient Lp space. -/
theorem exists_of_bounded_lp_approximation (u : RealLp m p) {M : ℝ}
    (happrox : ∀ ε > (0 : ℝ), ∃ f : E.domain,
      ‖(f : RealLp m p) - u‖ < ε ∧ E.rootSeminorm f ≤ M) :
    ∃ f : E.domain, (f : RealLp m p) = u ∧ E.rootSeminorm f ≤ M := by
  let : SeminormedAddCommGroup E.domain :=
    E.graphSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
  have : CompleteSpace E.domain := E.graph_complete
  have hroot : Continuous E.rootSeminorm :=
    Seminorm.continuous_of_le (show Continuous E.graphSeminorm from continuous_norm)
      E.rootSeminorm_le_graphSeminorm
  obtain ⟨q, hq, hClarkson⟩ := E.exists_clarkson_power
  let e := fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have he_anti : Antitone e := by
    intro n k hnk
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add_left (Nat.cast_le.mpr hnk) 1
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let C := fun n ↦ {f : E.domain | ‖(f : RealLp m p) - u‖ < e n}
  have hC (n : ℕ) : ∃ f ∈ C n, E.rootSeminorm f ≤ M := happrox _ (hepos n)
  let d := fun n : ℕ ↦ sInf (E.rootSeminorm '' C n)
  have hd_below (n : ℕ) : BddBelow (E.rootSeminorm '' C n) :=
    ⟨0, fun _ ⟨f, _, hf⟩ ↦ hf ▸ apply_nonneg _ _⟩
  have hd_ne (n : ℕ) : (E.rootSeminorm '' C n).Nonempty := by
    obtain ⟨f, hf, _⟩ := hC n
    exact ⟨_, mem_image_of_mem _ hf⟩
  have hd_le {n : ℕ} {f : E.domain} (hf : f ∈ C n) : d n ≤ E.rootSeminorm f :=
    csInf_le (hd_below _) (mem_image_of_mem _ hf)
  have hd0 (n : ℕ) : 0 ≤ d n :=
    le_csInf (hd_ne n) (fun _ ⟨f, _, hf⟩ ↦ hf ▸ apply_nonneg _ _)
  have hdM (n : ℕ) : d n ≤ M := by
    obtain ⟨f, hf, hMf⟩ := hC n
    exact (hd_le hf).trans hMf
  have hd_mono : Monotone d := by
    intro n k hnk
    apply le_csInf (hd_ne k)
    rintro _ ⟨f, hf, rfl⟩
    exact hd_le (show ‖(f : RealLp m p) - u‖ < e n from hf.trans_le (he_anti hnk))
  have hd_bdd : BddAbove (range d) := ⟨M, forall_mem_range.mpr hdM⟩
  let a := ⨆ n, d n
  have hda (n : ℕ) : d n ≤ a := le_ciSup hd_bdd n
  have ha0 : 0 ≤ a := (hd0 0).trans (hda 0)
  have haM : a ≤ M := ciSup_le hdM
  have hdlim : Tendsto d atTop (𝓝 a) := tendsto_atTop_ciSup hd_mono hd_bdd
  have hex (n : ℕ) : ∃ f ∈ C n, E.rootSeminorm f < d n + e n := by
    obtain ⟨_, ⟨f, hf, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hd_ne n) (lt_add_of_pos_right _ (hepos n))
    exact ⟨f, hf, hlt⟩
  choose f hf hfd using hex
  have hLp (n : ℕ) : ‖(f n : RealLp m p) - u‖ < e n := hf n
  let b := fun n : ℕ ↦ (2 * (a + e n)) ^ q - (2 * d n) ^ q
  have hblim : Tendsto b atTop (𝓝 0) := by
    have hrpow : Continuous (fun x : ℝ ↦ x ^ q) := Real.continuous_rpow_const hq.le
    have h₁ : Tendsto (fun n ↦ (2 * (a + e n)) ^ q) atTop (𝓝 ((2 * a) ^ q)) := by
      simpa only [Function.comp_def, add_zero] using
        (hrpow.tendsto (2 * (a + 0))).comp (tendsto_const_nhds.mul (tendsto_const_nhds.add helim))
    have h₂ : Tendsto (fun n ↦ (2 * d n) ^ q) atTop (𝓝 ((2 * a) ^ q)) :=
      (hrpow.tendsto (2 * a)).comp (tendsto_const_nhds.mul hdlim)
    simpa only [sub_self] using h₁.sub h₂
  have hdiff {n k l : ℕ} (hnk : n ≤ k) (hnl : n ≤ l) :
      E.rootSeminorm (f k - f l) ^ q ≤ b n := by
    have hmid : (1 / 2 : ℝ) • (f k + f l) ∈ C n := by
      let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
      change ‖(1 / 2 : ℝ) • ((f k : RealLp m p) + (f l : RealLp m p)) - u‖ < e n
      rw [show (1 / 2 : ℝ) • ((f k : RealLp m p) + (f l : RealLp m p)) - u =
        (1 / 2 : ℝ) • (((f k : RealLp m p) - u) + ((f l : RealLp m p) - u)) by module,
        norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hk := (hLp k).trans_le (he_anti hnk)
      have hl := (hLp l).trans_le (he_anti hnl)
      linarith only [norm_add_le ((f k : RealLp m p) - u) ((f l : RealLp m p) - u), hk, hl]
    have hm := hd_le hmid
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hm
    have hmid' : (2 * d n) ^ q ≤ E.rootSeminorm (f k + f l) ^ q :=
      Real.rpow_le_rpow (mul_nonneg (by norm_num) (hd0 n))
        (by linarith only [hm]) hq.le
    have hk : E.rootSeminorm (f k) ≤ a + e n :=
      (hfd k).le.trans (add_le_add (hda k) (he_anti hnk))
    have hl : E.rootSeminorm (f l) ≤ a + e n :=
      (hfd l).le.trans (add_le_add (hda l) (he_anti hnl))
    have hc := hClarkson _ _ _ (add_nonneg ha0 (hepos n).le) hk hl
    change _ ≤ (2 * (a + e n)) ^ q - (2 * d n) ^ q
    linarith only [hc, hmid']
  have hCauchy : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ := ε / 3
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδq : 0 < δ ^ q := Real.rpow_pos_of_pos hδ _
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((hblim.eventually_lt_const hδq).and (helim.eventually_lt_const hδ))
    refine ⟨N, fun k hk l hl ↦ ?_⟩
    have hs : E.rootSeminorm (f k - f l) < δ :=
      (Real.rpow_lt_rpow_iff (apply_nonneg _ _) hδ.le hq).1
        ((hdiff hk hl).trans_lt (hN N le_rfl).1)
    have hLp_diff : ‖((f k - f l : E.domain) : RealLp m p)‖ < 2 * δ := by
      let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
      change ‖(f k : RealLp m p) - (f l : RealLp m p)‖ < 2 * δ
      rw [show (f k : RealLp m p) - (f l : RealLp m p) =
        ((f k : RealLp m p) - u) - ((f l : RealLp m p) - u) by abel]
      exact (norm_sub_le _ _).trans_lt (by
        have hk' := (hLp k).trans (hN k hk).2
        have hl' := (hLp l).trans (hN l hl).2
        linarith only [hk', hl'])
    rw [dist_eq_norm]
    change E.graphSeminorm (f k - f l) < ε
    exact (E.graphSeminorm_le_add _).trans_lt (by dsimp [δ] at *; linarith only [hs, hLp_diff])
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hcongr : (g : RealLp m p) = u := by
    by_contra hne
    have hgraph := Metric.tendsto_atTop.mp hg
    let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
    let ε : ℝ := ‖(g : RealLp m p) - u‖ / 2
    have hε : 0 < ε := half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    obtain ⟨N, hN⟩ := hgraph ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1 (helim.eventually_lt_const hε)
    let n := max N K
    have hNg := hN n (le_max_left _ _)
    rw [dist_eq_norm] at hNg
    have hfirst : ‖(f n : RealLp m p) - (g : RealLp m p)‖ < ε :=
      (E.norm_le_graphSeminorm (f n - g)).trans_lt hNg
    have hsecond := (hLp n).trans (hK n (le_max_right _ _))
    have h := norm_sub_le ((g : RealLp m p) - (f n : RealLp m p)) ((u : RealLp m p) - (f n : RealLp m p))
    rw [sub_sub_sub_cancel_right] at h
    have hfirst' : ‖(g : RealLp m p) - (f n : RealLp m p)‖ < ε :=
      lt_of_le_of_lt (norm_sub_rev _ _).le hfirst
    have hsecond' : ‖u - (f n : RealLp m p)‖ < ε :=
      lt_of_le_of_lt (norm_sub_rev _ _).le hsecond
    dsimp [ε] at hfirst' hsecond'
    linarith only [h, hfirst', hsecond']
  have hlim_root : Tendsto (fun n ↦ E.rootSeminorm (f n)) atTop (𝓝 (E.rootSeminorm g)) :=
    hroot.continuousAt.tendsto.comp hg
  refine ⟨g, hcongr, ?_⟩
  exact (le_of_tendsto_of_tendsto hlim_root (by simpa using hdlim.add helim)
    (Eventually.of_forall fun n ↦ (hfd n).le)).trans haM

theorem isClosed_root_sublevel_in_lp (M : ℝ) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
    IsClosed {u : RealLp m p | ∃ f : E.domain, (f : RealLp m p) = u ∧ E.rootSeminorm f ≤ M} := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  apply isClosed_of_closure_subset
  intro u hu
  apply E.exists_of_bounded_lp_approximation
  intro ε hε
  obtain ⟨_, ⟨f, rfl, hf⟩, hdist⟩ := Metric.mem_closure_iff.mp hu ε hε
  rw [dist_comm, dist_eq_norm] at hdist
  exact ⟨f, hdist, hf⟩

end WalkDimensions.PEnergy
