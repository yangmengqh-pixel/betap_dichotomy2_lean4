import WalkDimensions.EnergyLattice
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Oscillatory truncations for constructing energy measures

The distance to the even grid is the sawtooth from Sasaya's construction.
A shifted ramp cuts it off outside a sublevel set.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

noncomputable def sawtooth (δ t : ℝ) : ℝ :=
  infDist t (range fun k : ℤ ↦ (2 * δ) * (k : ℝ))

theorem lipschitzWith_sawtooth (δ : ℝ) : LipschitzWith 1 (sawtooth δ) :=
  lipschitz_infDist_pt _

theorem sawtooth_zero (δ : ℝ) : sawtooth δ 0 = 0 := by
  apply infDist_zero_of_mem
  exact ⟨0, by simp⟩

theorem sawtooth_nonneg (δ t : ℝ) : 0 ≤ sawtooth δ t := infDist_nonneg

theorem sawtooth_eq_min_of_mem_cell {δ t : ℝ} (hδ : 0 < δ) (k : ℤ)
    (hleft : 2 * δ * (k : ℝ) ≤ t) (hright : t ≤ 2 * δ * ((k : ℝ) + 1)) :
    sawtooth δ t = min (t - 2 * δ * (k : ℝ)) (2 * δ * ((k : ℝ) + 1) - t) := by
  let S := range fun k : ℤ ↦ (2 * δ) * (k : ℝ)
  change infDist t S = _
  have hδ' : 0 ≤ 2 * δ := by positivity
  have hℓ : 2 * δ * (k : ℝ) ∈ S := mem_range_self k
  have hᵣ : 2 * δ * ((k : ℝ) + 1) ∈ S := by
    exact ⟨k + 1, by simp⟩
  apply le_antisymm
  · apply le_min
    · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hleft)] using
        (infDist_le_dist_of_mem hℓ (x := t))
    · simpa only [Real.dist_eq, abs_sub_comm t, abs_of_nonneg (sub_nonneg.mpr hright)] using
        (infDist_le_dist_of_mem hᵣ (x := t))
  · apply (le_infDist ⟨_, hℓ⟩).mpr
    rintro y ⟨l, rfl⟩
    rcases le_or_gt l k with hl | hl
    · have h := mul_le_mul_of_nonneg_left (show (l : ℝ) ≤ k by exact_mod_cast hl) hδ'
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (h.trans hleft))]
      exact (min_le_left _ _).trans (sub_le_sub_left h _)
    · have hl' : k + 1 ≤ l := Int.add_one_le_iff.mpr hl
      have h := mul_le_mul_of_nonneg_left (show (k : ℝ) + 1 ≤ l by exact_mod_cast hl') hδ'
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hright.trans h))]
      exact (min_le_right _ _).trans (sub_le_sub_right h _)

private theorem exists_sawtooth_cell {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ k : ℤ, 2 * δ * (k : ℝ) ≤ t ∧ t ≤ 2 * δ * ((k : ℝ) + 1) := by
  let k : ℤ := ⌊t / (2 * δ)⌋
  have hD : 0 < 2 * δ := by positivity
  refine ⟨k, ?_, ?_⟩
  · rw [mul_comm]
    exact (le_div_iff₀ hD).mp (Int.floor_le _)
  · rw [mul_comm]
    exact (div_le_iff₀ hD).mp (Int.lt_floor_add_one _).le

theorem sawtooth_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : sawtooth δ t ≤ δ := by
  obtain ⟨k, hleft, hright⟩ := exists_sawtooth_cell hδ t
  rw [sawtooth_eq_min_of_mem_cell hδ k hleft hright]
  by_contra! h
  have h1 := h.trans_le (min_le_left _ _)
  have h2 := h.trans_le (min_le_right _ _)
  linarith only [h1, h2]

theorem sawtooth_eq_abs_of_abs_le {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ) :
    sawtooth δ t = |t| := by
  have h := abs_le.mp ht
  rcases le_total 0 t with h₀ | h₀
  · have he := sawtooth_eq_min_of_mem_cell hδ 0 (t := t) (by simpa using h₀) (by
      norm_num
      linarith only [h.2, hδ])
    simp only [Int.cast_zero, mul_zero, sub_zero, zero_add, mul_one] at he
    rw [he, abs_of_nonneg h₀, min_eq_left (show t ≤ 2 * δ - t by linarith only [h.2])]
  · have he := sawtooth_eq_min_of_mem_cell hδ (-1) (t := t) (by
      norm_num
      linarith only [h.1, hδ]) (by simpa using h₀)
    simp only [Int.cast_neg, Int.cast_one, neg_add_cancel, mul_zero, zero_sub, mul_neg,
      mul_one, sub_neg_eq_add] at he
    rw [he, abs_of_nonpos h₀, min_eq_right (show -t ≤ t + 2 * δ by linarith only [h.1])]

theorem sawtooth_half (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    sawtooth (δ / 2) t = min (sawtooth δ t) (δ - sawtooth δ t) := by
  obtain ⟨k, hleft, hright⟩ := exists_sawtooth_cell hδ t
  have hδ' : 0 < δ / 2 := half_pos hδ
  let l := 2 * δ * (k : ℝ)
  let r := 2 * δ * ((k : ℝ) + 1)
  have hr : r = l + 2 * δ := by dsimp [l, r]; ring
  rw [sawtooth_eq_min_of_mem_cell hδ k hleft hright]
  change sawtooth (δ / 2) t = min (min (t - l) (r - t)) (δ - min (t - l) (r - t))
  by_cases hmid : t ≤ l + δ
  · have hL : 2 * (δ / 2) * ((2 * k : ℤ) : ℝ) = l := by
      push_cast
      dsimp [l]
      ring
    have hR : 2 * (δ / 2) * (((2 * k : ℤ) : ℝ) + 1) = l + δ := by
      push_cast
      dsimp [l]
      ring
    have he := sawtooth_eq_min_of_mem_cell hδ' (2 * k) (hL.symm ▸ hleft) (hR.symm ▸ hmid)
    rw [hL, hR] at he
    rw [he, min_eq_left (by linarith only [hmid, hr] : t - l ≤ r - t)]
    exact congrArg (min (t - l)) (by ring)
  · have hL : 2 * (δ / 2) * ((2 * k + 1 : ℤ) : ℝ) = l + δ := by
      push_cast
      dsimp [l]
      ring
    have hR : 2 * (δ / 2) * (((2 * k + 1 : ℤ) : ℝ) + 1) = r := by
      push_cast
      dsimp [r]
      ring
    have he := sawtooth_eq_min_of_mem_cell hδ' (2 * k + 1)
      (hL.symm ▸ le_of_not_ge hmid) (hR.symm ▸ hright)
    rw [hL, hR] at he
    rw [he, min_eq_right (by linarith only [hmid, hr] : r - t ≤ t - l), min_comm (r - t)]
    congr 1
    linarith only [hr]

def sublevelRamp (δ a t : ℝ) : ℝ := max (min (a + δ - t) δ) 0

theorem lipschitzWith_sublevelRamp (δ a : ℝ) : LipschitzWith 1 (sublevelRamp δ a) := by
  have h : LipschitzWith 1 (fun t : ℝ ↦ a + δ - t) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    simp only [Real.dist_eq, sub_sub_sub_cancel_left, NNReal.coe_one, one_mul, abs_sub_comm s t, le_refl]
  exact (h.min_const δ).max_const 0

theorem sublevelRamp_nonneg (δ a t : ℝ) : 0 ≤ sublevelRamp δ a t := le_max_right _ _

theorem sublevelRamp_eq_cap {δ a t : ℝ} (hδ : 0 ≤ δ) (ht : t ≤ a) :
    sublevelRamp δ a t = δ := by
  rw [sublevelRamp, min_eq_right (by linarith), max_eq_left hδ]

theorem sublevelRamp_eq_zero {δ a t : ℝ} (ht : a + δ ≤ t) :
    sublevelRamp δ a t = 0 := by
  exact max_eq_right ((min_le_left _ _).trans (sub_nonpos.mpr ht))

namespace PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

/-- The localized oscillation is an energy-domain element with a
continuous compactly supported representative. -/
theorem exists_localized_oscillation (f g : E.domain) {u v : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hgv : (g : RealLp m p) =ᵐ[m] v)
    (hu : Continuous u) (hv : Continuous v) (hc : HasCompactSupport u) (δ a : ℝ) :
    ∃ h : E.domain,
      let w : X → ℝ := fun x ↦ min (sawtooth δ (u x)) (sublevelRamp δ a (v x))
      (h : RealLp m p) =ᵐ[m] w ∧ Continuous w ∧ HasCompactSupport w ∧
        E.rootSeminorm h ≤ E.rootSeminorm f + E.rootSeminorm g := by
  obtain ⟨f', hf', hEf⟩ := E.exists_lipschitz_one_comp f hfu (sawtooth δ)
    (lipschitzWith_sawtooth δ) (sawtooth_zero δ)
  let ψ (t : ℝ) := sublevelRamp δ a t - sublevelRamp δ a 0
  have hψ : LipschitzWith 1 ψ := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    have h := lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_sublevelRamp δ a) x y
    simpa only [ψ, Real.dist_eq, sub_sub_sub_cancel_right] using h
  obtain ⟨g', hg', hEg⟩ := E.exists_lipschitz_one_comp g hgv ψ hψ (sub_self _)
  obtain ⟨h, hh, hE⟩ := E.exists_min_add_const f' g' hf' hg' (sublevelRamp_nonneg δ a 0)
  refine ⟨h, hh.mono (fun x hx ↦ ?_), ?_, ?_, ?_⟩
  · rw [hx]
    simp only [Function.comp_apply, ψ, sub_add_cancel]
  · exact ((lipschitzWith_sawtooth δ).continuous.comp hu).min
      ((lipschitzWith_sublevelRamp δ a).continuous.comp hv)
  · apply hc.isCompact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    by_contra h₀
    have he : u x = 0 := notMem_support.mp h₀
    apply hx
    change min (sawtooth δ (u x)) (sublevelRamp δ a (v x)) = 0
    rw [he, sawtooth_zero, min_eq_left (sublevelRamp_nonneg δ a (v x))]
  · apply hE.trans (add_le_add ?_ ?_)
    · rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hEf)
        (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
    · rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hEg)
        (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)

end PEnergy

end WalkDimensions
