import WalkDimensions.HausdorffDensityTail
import WalkDimensions.LocalMorrey
import WalkDimensions.LocalBesov
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Lower densities from positive Besov oscillation at a shared Hölder exponent
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

private def oscillationSet (u : X → ℝ) (r b : ℝ) : Set X :=
  {x | ∃ y ∈ ball x r, b < |u x - u y|}

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem isOpen_oscillationSet {u : X → ℝ} (hu : Continuous u) (r b : ℝ) :
    IsOpen (oscillationSet u r b) := by
  have he : oscillationSet u r b = ⋃ y : X,
      (ball y r ∩ {x | b < |u x - u y|}) := by
    ext x
    simp only [oscillationSet, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_ball]
    simp only [dist_comm x]
  rw [he]
  exact isOpen_iUnion fun y ↦ isOpen_ball.inter
    (isOpen_lt continuous_const (hu.sub continuous_const).abs)

variable {m : Measure X}

omit [SecondCountableTopology X] in
private theorem besovEnergy_le_of_holder_scale {p q β β' c t r : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (ht : 0 ≤ t) (hr : 0 < r)
    (he : β' - β = c * (q - p)) {u : X → ℝ} {U : Set X} (hU : MeasurableSet U)
    (h : ∀ x ∈ U, ∀ y ∈ ball x r, |u x - u y| ≤ t * r ^ c) :
    besovEnergy m q β' U u r ≤ (ENNReal.ofReal t) ^ (q - p) * besovEnergy m p β U u r := by
  apply (besovEnergy_le_of_increment_bound_on hp hpq hr hU (fun x hx y hy ↦ h x hx y hy)).trans_eq
  rw [ENNReal.ofReal_mul ht, ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hpq),
    ← ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.rpow_mul, mul_left_comm,
    ← mul_assoc, mul_assoc ((ENNReal.ofReal t) ^ (q - p)),
    ← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top]
  rw [show β - β' + c * (q - p) = 0 by linarith only [he], ENNReal.rpow_zero, mul_one]

omit [SecondCountableTopology X] in
/-- A positive lower bound on the higher-power Besov energies forces a positive mass of
points with large increments on arbitrarily fine scales. -/
theorem exists_positive_measure_fine_oscillation {ν : Measure X} [IsFiniteMeasure ν]
    {p q β β' c : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hc : 0 ≤ c)
    (he : β' - β = c * (q - p)) {u : X → ℝ} (hu : Continuous u)
    {H : ℝ} (hH : 0 < H) (hHolder : ∀ x y, |u x - u y| ≤ H * dist x y ^ c)
    {A : ℝ} {K M : ℝ≥0∞} (hK : 0 < K) (hKT : K ≠ ∞) (hM : M ≠ ∞)
    (hfwd : ∀ U r, 0 < r → besovEnergy m p β U u r ≤ K * ν (thickening (A * r) U))
    (hBound : ∀ r, 0 < r → besovEnergy m p β univ u r ≤ M)
    (hLower : 0 < liminf (besovEnergy m q β' univ u) (𝓝[>] (0 : ℝ))) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ W : Set X, MeasurableSet W ∧ 0 < ν W ∧
      ∀ x ∈ W, ∀ ε > (0 : ℝ), ∃ r ∈ Ioo (0 : ℝ) ε,
        ∃ y ∈ ball x (A * r), ∃ z ∈ ball y r, θ * r ^ c < |u y - u z| := by
  have hpq' : 0 < q - p := sub_pos.mpr hpq
  let L := liminf (besovEnergy m q β' univ u) (𝓝[>] (0 : ℝ))
  obtain ⟨a, ha, haL⟩ := exists_between (show 0 < L from hLower)
  obtain ⟨b, hb, hba⟩ := exists_between ha
  have hlower : ∀ᶠ r in 𝓝[>] (0 : ℝ), a < besovEnergy m q β' univ u r :=
    eventually_lt_of_lt_liminf haL (by isBoundedDefault)
  have hsmallLim : Tendsto (fun t : ℝ ↦ (ENNReal.ofReal t) ^ (q - p) * M)
      (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hM hpq').comp
      (show Tendsto ENNReal.ofReal (𝓝 (0 : ℝ)) (𝓝 0) by
        simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0)
    change Tendsto (fun t : ℝ ↦ M * (ENNReal.ofReal t) ^ (q - p)) (𝓝 0) (𝓝 0) at h
    simpa only [mul_comm M] using h.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨θ, hθ, hsmall⟩ := (eventually_mem_nhdsWithin.and (hsmallLim.eventually_lt_const hb)).exists
  let B (r : ℝ) := oscillationSet u r (θ * r ^ c)
  let S (r : ℝ) := thickening (A * r) (B r)
  let D := (ENNReal.ofReal H) ^ (q - p) * K
  have hD₀ : D ≠ 0 := mul_ne_zero
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hH) ENNReal.ofReal_ne_top).ne' hK.ne'
  have hDT : D ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hpq'.le ENNReal.ofReal_ne_top) hKT
  let v := (a - b) / D
  have hv : 0 < v := ENNReal.div_pos (tsub_pos_of_lt hba).ne' hDT
  have hlarge (r : ℝ) (hr : 0 < r) (h : a < besovEnergy m q β' univ u r) : v ≤ ν (S r) := by
    have hB : MeasurableSet (B r) := (isOpen_oscillationSet hu _ _).measurableSet
    have hpart : besovEnergy m q β' (B r) u r + besovEnergy m q β' (B r)ᶜ u r =
        besovEnergy m q β' univ u r := by
      simp only [besovEnergy, ← mul_add, lintegral_add_compl _ hB, Measure.restrict_univ]
    have hg := besovEnergy_le_of_holder_scale (m := m) hp hpq.le hH.le hr he hB (u := u)
      (fun x _ y hy ↦ (hHolder x y).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (by rw [dist_comm]; exact (mem_ball.mp hy).le) hc) hH.le))
    have hs := besovEnergy_le_of_holder_scale (m := m) hp hpq.le (show 0 ≤ θ from hθ.le) hr he hB.compl
      (fun x hx y hy ↦ le_of_not_gt fun hxy ↦ hx ⟨y, hy, hxy⟩)
    have hmono : besovEnergy m p β (B r)ᶜ u r ≤ besovEnergy m p β univ u r :=
      mul_le_mul_of_nonneg_left (lintegral_mono_set (subset_univ _)) bot_le
    have hbs : besovEnergy m q β' (B r)ᶜ u r ≤ b := hs.trans
      ((mul_le_mul_of_nonneg_left (hmono.trans (hBound r hr)) bot_le).trans hsmall.le)
    have hbg : besovEnergy m q β' (B r) u r ≤ D * ν (S r) := hg.trans (by
      dsimp only [D, S]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hfwd _ r hr) bot_le)
    have hab : a ≤ D * ν (S r) + b := h.le.trans (hpart ▸ add_le_add hbg hbs)
    apply (ENNReal.div_le_iff hD₀ hDT).mpr
    rw [mul_comm]
    exact tsub_le_iff_right.mpr hab
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hs (n : ℕ) : ∃ r ∈ Ioo 0 (ε n), a < besovEnergy m q β' univ u r := by
    have hn : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 (ε n) := Ioo_mem_nhdsGT (hε n)
    exact (hn.and hlower).exists
  choose r hr hlargeQ using hs
  have hm (n : ℕ) : v ≤ ν (S (r n)) := hlarge _ (hr n).1 (hlargeQ n)
  let U (N : ℕ) := ⋃ n : Ici N, S (r n)
  have hU (N : ℕ) : MeasurableSet (U N) :=
    MeasurableSet.iUnion fun n ↦ isOpen_thickening.measurableSet
  have hanti : Antitone U := by
    intro N M hNM x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨n, hNM.trans n.property⟩, hn⟩
  let W := ⋂ N, U N
  have hmt := tendsto_measure_iInter_atTop (μ := ν) (fun N ↦ (hU N).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hMW : v ≤ ν W := ge_of_tendsto hmt (Eventually.of_forall fun N ↦
    (hm N).trans (measure_mono (subset_iUnion (fun n : Ici N ↦ S (r n)) ⟨N, mem_Ici.mpr le_rfl⟩)))
  refine ⟨θ, hθ, W, MeasurableSet.iInter hU, hv.trans_le hMW, ?_⟩
  intro x hx δ hδ
  obtain ⟨N, hN⟩ := (eventually_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hδ))
  obtain ⟨n, hn⟩ := mem_iUnion.mp (mem_iInter.mp hx N)
  refine ⟨r n, ⟨(hr n).1, (hr n).2.trans (hN n n.property)⟩, ?_⟩
  obtain ⟨y, hyB, hxy⟩ := (mem_thickening_iff.mp hn)
  obtain ⟨z, hz, huDiff⟩ := hyB
  exact ⟨y, mem_ball.mpr (by simpa only [dist_comm] using hxy), z, hz, huDiff⟩

end WalkDimensions
