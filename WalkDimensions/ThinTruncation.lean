import WalkDimensions.CompactEnergyLimit
import WalkDimensions.EnergyMidpointLimit
import WalkDimensions.EnergyTruncation

/-!
# Thin truncations

The symmetric truncations of a compactly supported function satisfy the
midpoint bound. Their energy tends to zero as the truncation level
decreases.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

def symmetricClip (a t : ℝ) : ℝ := min (max t (-a)) a

theorem symmetricClip_lipschitz (a : ℝ) : LipschitzWith 1 (symmetricClip a) :=
  (LipschitzWith.id.max_const (-a)).min_const a

theorem symmetricClip_zero {a : ℝ} (ha : 0 ≤ a) : symmetricClip a 0 = 0 := by
  simp only [symmetricClip, max_eq_left (neg_nonpos.mpr ha), min_eq_left ha]

theorem abs_symmetricClip_le {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : |symmetricClip a t| ≤ a := by
  exact abs_le.mpr ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩

private theorem symmetricClip_mean {a b c : ℝ} (hab : a ≤ b) (hac : a ≤ c) (t : ℝ) :
    symmetricClip a ((symmetricClip b t + symmetricClip c t) / 2) = symmetricClip a t := by
  by_cases hLo : t ≤ -a
  · have h (d : ℝ) (had : a ≤ d) : symmetricClip d t ≤ -a :=
      (min_le_left _ _).trans (max_le hLo (neg_le_neg had))
    have havg : (symmetricClip b t + symmetricClip c t) / 2 ≤ -a := by
      linarith only [h b hab, h c hac]
    change min (max ((symmetricClip b t + symmetricClip c t) / 2) (-a)) a =
      min (max t (-a)) a
    rw [max_eq_right havg, max_eq_right hLo]
  by_cases hHi : a ≤ t
  · have h (d : ℝ) (had : a ≤ d) : a ≤ symmetricClip d t :=
      le_min (hHi.trans (le_max_left _ _)) had
    have havg : a ≤ (symmetricClip b t + symmetricClip c t) / 2 := by
      linarith only [h b hab, h c hac]
    change min (max ((symmetricClip b t + symmetricClip c t) / 2) (-a)) a =
      min (max t (-a)) a
    rw [min_eq_right (hHi.trans (le_max_left _ _)), min_eq_right (havg.trans (le_max_left _ _))]
  have h (d : ℝ) (had : a ≤ d) : symmetricClip d t = t := by
    rw [symmetricClip, max_eq_left (le_trans (neg_le_neg had) (le_of_not_ge hLo)),
      min_eq_left ((le_of_not_ge hHi).trans had)]
  rw [h b hab, h c hac, show (t + t) / 2 = t by ring]

/-- Clipping the values of a compactly supported domain element to
shrinking symmetric intervals converges to zero in the graph norm. -/
theorem exists_thin_truncations (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hc : HasCompactSupport u) :
    ∃ h : ℕ → E.domain,
      (∀ n, (h n : RealLp m p) =ᵐ[m] symmetricClip (1 / ((n : ℝ) + 1)) ∘ u) ∧
        Tendsto (fun n ↦ E.graphSeminorm (h n)) atTop (𝓝 0) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let ε (n : ℕ) := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hanti : Antitone ε := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add_left (Nat.cast_le.mpr hij) 1
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose h hh _ using fun n ↦
    E.exists_lipschitz_one_comp f hfu (symmetricClip (ε n)) (symmetricClip_lipschitz _)
      (symmetricClip_zero (hε n).le)
  have hmid (i j n : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
      E.rootSeminorm (h n) ≤ E.rootSeminorm ((1 / 2 : ℝ) • (h i + h j)) := by
    let g := (1 / 2 : ℝ) • (h i + h j)
    let v : X → ℝ := fun x ↦ (symmetricClip (ε i) (u x) + symmetricClip (ε j) (u x)) / 2
    have hv : (g : RealLp m p) =ᵐ[m] v := by
      filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) ((h i : RealLp m p) + (h j : RealLp m p)),
        Lp.coeFn_add (h i : RealLp m p) (h j : RealLp m p), hh i, hh j] with x hx hs hix hjx
      change ((1 / 2 : ℝ) • ((h i : RealLp m p) + (h j : RealLp m p))) x = _
      rw [hx, Pi.smul_apply, smul_eq_mul, hs, Pi.add_apply, hix, hjx]
      dsimp only [v, Function.comp_apply]
      ring
    obtain ⟨k, hk, hkE⟩ := E.exists_lipschitz_one_comp g hv (symmetricClip (ε n))
      (symmetricClip_lipschitz _) (symmetricClip_zero (hε n).le)
    have he : k = h n := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hk, hh n] with x hx hyn
      rw [hx, hyn]
      exact symmetricClip_mean (hanti hi) (hanti hj) (u x)
    rw [← he, E.rootSeminorm_apply, E.rootSeminorm_apply]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _)
      (NNReal.coe_le_coe.mpr hkE) (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
  let S := tsupport u
  let D := (m.real S) ^ p⁻¹
  have hLpBound (n : ℕ) : ‖(h n : RealLp m p)‖ ≤ ε n * D := by
    apply norm_realLp_le_of_ae_abs_bound (zero_lt_one.trans E.one_lt) _ (S := S)
      isClosed_closure.measurableSet (hc.isCompact.measure_lt_top (μ := m)).ne (hε n).le
    filter_upwards [hh n] with x hx
    rw [hx]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      exact abs_symmetricClip_le (hε n).le (u x)
    · rw [indicator_of_notMem hxS]
      have hx₀ : u x = 0 := notMem_support.mp fun h ↦ hxS (subset_closure h)
      rw [Function.comp_apply, hx₀, symmetricClip_zero (hε n).le, abs_zero]
  have hLpNorm : Tendsto (fun n ↦ ‖(h n : RealLp m p)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) hLpBound (by simpa only [zero_mul] using hlim.mul_const D)
  have hE := E.tendsto_root_zero_of_midpoint_control h hLpNorm hmid
  refine ⟨h, hh, ?_⟩
  exact squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun n ↦ E.graphSeminorm_le_add (h n))
    (by simpa only [zero_add] using hE.add hLpNorm)

end WalkDimensions.PEnergy
