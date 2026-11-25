import WalkDimensions.MidpointContraction
import WalkDimensions.OscillatoryTruncation

/-!
# Vanishing energy of thin sublevel ramps

The offset removes the value at zero, keeping the ramp in the domain.
Its midpoint identities control the energy as the width shrinks.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

def offsetRamp (δ a t : ℝ) : ℝ := sublevelRamp δ a t - sublevelRamp δ a 0

theorem offsetRamp_zero (δ a : ℝ) : offsetRamp δ a 0 = 0 := sub_self _

theorem lipschitzWith_offsetRamp (δ a : ℝ) : LipschitzWith 1 (offsetRamp δ a) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  simpa only [offsetRamp, Real.dist_eq, sub_sub_sub_cancel_right] using
    lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_sublevelRamp δ a) x y

private theorem sublevelRamp_le_cap {δ : ℝ} (hδ : 0 ≤ δ) (a t : ℝ) :
    sublevelRamp δ a t ≤ δ := max_le (min_le_right _ _) hδ

theorem abs_offsetRamp_le {δ : ℝ} (hδ : 0 ≤ δ) (a t : ℝ) :
    |offsetRamp δ a t| ≤ δ := by
  have h₀ := sublevelRamp_nonneg δ a 0
  have h₁ := sublevelRamp_nonneg δ a t
  have h₂ := sublevelRamp_le_cap hδ a 0
  have h₃ := sublevelRamp_le_cap hδ a t
  unfold offsetRamp
  exact abs_le.mpr ⟨by linarith only [h₁, h₂], by linarith only [h₀, h₃]⟩

private theorem sublevelRamp_eq_cap_sub_min {δ : ℝ} (hδ : 0 ≤ δ) (a t : ℝ) :
    sublevelRamp δ a t = δ - min (max (t - a) 0) δ := by
  by_cases h : t ≤ a
  · rw [sublevelRamp_eq_cap hδ h, max_eq_right (sub_nonpos.mpr h), min_eq_left hδ, sub_zero]
  · have h' : a ≤ t := le_of_not_ge h
    rw [max_eq_left (sub_nonneg.mpr h')]
    by_cases ht : a + δ ≤ t
    · rw [sublevelRamp_eq_zero ht, min_eq_right (by linarith : δ ≤ t - a), sub_self]
    · unfold sublevelRamp
      rw [min_eq_left (by linarith : a + δ - t ≤ δ),
        max_eq_left (by linarith : 0 ≤ a + δ - t), min_eq_left (by linarith : t - a ≤ δ)]
      ring

private theorem min_midpoint_min {a b c : ℝ} (hab : a ≤ b) (hac : a ≤ c) (t : ℝ) :
    min ((min t b + min t c) / 2) a = min t a := by
  rcases le_total t a with ha | ha
  · rw [min_eq_left (ha.trans hab), min_eq_left (ha.trans hac), show (t + t) / 2 = t by ring]
  · rw [min_eq_right ha, min_eq_right (by linarith only [le_min ha hab, le_min ha hac])]

theorem offsetRamp_eq_neg_min {δ a : ℝ} (hδ : 0 ≤ δ) (ha : 0 ≤ a) (t : ℝ) :
    offsetRamp δ a t = -min (max (t - a) 0) δ := by
  unfold offsetRamp
  rw [sublevelRamp_eq_cap_sub_min hδ a t, sublevelRamp_eq_cap hδ ha]
  ring

private theorem offsetRamp_eq_ramp {δ a : ℝ} (hδ : δ ≤ -a) (t : ℝ) :
    offsetRamp δ a t = sublevelRamp δ a t := by
  unfold offsetRamp
  rw [sublevelRamp_eq_zero (t := 0) (by linarith), sub_zero]

private theorem offsetRamp_midpoint_contract {a r s t : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hrt : r ≤ t)
    (ha : 0 ≤ a ∨ (s ≤ -a ∧ t ≤ -a)) :
    ∃ φ : ℝ → ℝ, LipschitzWith 1 φ ∧ φ 0 = 0 ∧
      ∀ x, offsetRamp r a x = φ ((offsetRamp s a x + offsetRamp t a x) / 2) := by
  rcases ha with ha | ⟨hsA, htA⟩
  · let φ : ℝ → ℝ := fun v ↦ max v (-r)
    refine ⟨φ, LipschitzWith.id.max_const _, max_eq_left (neg_nonpos.mpr hr), fun x ↦ ?_⟩
    rw [offsetRamp_eq_neg_min hr ha, offsetRamp_eq_neg_min (hr.trans hrs) ha,
      offsetRamp_eq_neg_min (hr.trans hrt) ha]
    unfold φ
    rw [show (-min (max (x - a) 0) s + -min (max (x - a) 0) t) / 2 =
      -((min (max (x - a) 0) s + min (max (x - a) 0) t) / 2) by ring, max_neg_neg,
      min_midpoint_min hrs hrt]
  · let D := (s + t) / 2 - r
    have hD : 0 ≤ D := by dsimp [D]; linarith
    let φ : ℝ → ℝ := fun v ↦ max (v - D) 0
    have hsub : LipschitzWith 1 (fun v : ℝ ↦ v - D) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      simp only [Real.dist_eq, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul, le_refl]
    refine ⟨φ, hsub.max_const 0, ?_, fun x ↦ ?_⟩
    · exact max_eq_right (by linarith)
    · rw [offsetRamp_eq_ramp (hrs.trans hsA), offsetRamp_eq_ramp hsA, offsetRamp_eq_ramp htA,
        sublevelRamp_eq_cap_sub_min hr, sublevelRamp_eq_cap_sub_min (hr.trans hrs),
        sublevelRamp_eq_cap_sub_min (hr.trans hrt)]
      let M := (min (max (x - a) 0) s + min (max (x - a) 0) t) / 2
      have hM : min M r = min (max (x - a) 0) r := min_midpoint_min hrs hrt _
      rw [← hM]
      unfold φ
      rw [show (s - min (max (x - a) 0) s + (t - min (max (x - a) 0) t)) / 2 - D = r - M by
        dsimp [D, M]
        ring]
      rcases le_total M r with h | h
      · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
      · rw [min_eq_right h, sub_self, max_eq_right (sub_nonpos.mpr h)]

namespace PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_ramp_graph_tendsto_zero (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hc : HasCompactSupport u) (a : ℝ)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hanti : Antitone δ) (hlim : Tendsto δ atTop (𝓝 0)) :
    ∃ g : ℕ → E.domain,
      (∀ n, (g n : RealLp m p) =ᵐ[m] offsetRamp (δ n) a ∘ u) ∧
      Tendsto (fun n ↦ E.graphSeminorm (g n)) atTop (𝓝 0) := by
  choose g hg _ using fun n ↦ E.exists_lipschitz_one_comp f hfu (offsetRamp (δ n) a)
    (lipschitzWith_offsetRamp (δ n) a) (offsetRamp_zero (δ n) a)
  refine ⟨g, hg, ?_⟩
  have hthreshold : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ a ∨ δ n ≤ -a := by
    by_cases ha : 0 ≤ a
    · exact ⟨0, fun _ _ ↦ Or.inl ha⟩
    · obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (neg_pos.mpr (lt_of_not_ge ha)))
      exact ⟨N, fun n hn ↦ Or.inr (hN n hn).le⟩
  obtain ⟨N, hN⟩ := hthreshold
  apply (tendsto_add_atTop_iff_nat N).mp
  let S := tsupport u
  let γ (n : ℕ) := δ (n + N)
  apply E.tendsto_graph_zero_of_uniform_bound_midpoint_control
    (fun n ↦ g (n + N)) (fun n ↦ offsetRamp (γ n) a ∘ u) (fun n ↦ hg (n + N))
    (S := S) isClosed_closure.measurableSet (hc.isCompact.measure_lt_top (μ := m)).ne
    γ (fun n ↦ hδ (n + N)) ((tendsto_add_atTop_iff_nat N).mpr hlim)
  · intro n x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact abs_offsetRamp_le (hδ (n + N)) a (u x)
    · have hu : u x = 0 := notMem_support.mp fun h ↦ hx (subset_closure h)
      rw [indicator_of_notMem hx, Function.comp_apply, hu, offsetRamp_zero, abs_zero]
  · intro i j n hi hj
    have rai : γ n ≤ γ i := hanti (Nat.add_le_add_right hi N)
    have raj : γ n ≤ γ j := hanti (Nat.add_le_add_right hj N)
    have ha : 0 ≤ a ∨ (γ i ≤ -a ∧ γ j ≤ -a) := by
      by_cases h : 0 ≤ a
      · exact Or.inl h
      · exact Or.inr ⟨(hN (i + N) (Nat.le_add_left _ _)).resolve_left h,
          (hN (j + N) (Nat.le_add_left _ _)).resolve_left h⟩
    obtain ⟨φ, hφ, hφ₀, hEq⟩ := offsetRamp_midpoint_contract (hδ (n + N)) rai raj ha
    exact E.root_le_midpoint_of_lipschitz_comp _ _ _ (hg (i + N)) (hg (j + N)) (hg (n + N))
      hφ hφ₀ (fun x ↦ hEq (u x))

end PEnergy

end WalkDimensions
