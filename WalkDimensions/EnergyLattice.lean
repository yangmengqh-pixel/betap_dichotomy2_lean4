import WalkDimensions.EnergyTruncation

/-!
# Shifted lattice operations

Normal contractions and the seminorm inequality control a pointwise
minimum with a function shifted by a nonnegative constant.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_min_add_const (f g : E.domain) {u v : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hgv : (g : RealLp m p) =ᵐ[m] v)
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ h : E.domain, (h : RealLp m p) =ᵐ[m] (fun x ↦ min (u x) (v x + a)) ∧
      E.rootSeminorm h ≤ E.rootSeminorm f + E.rootSeminorm g := by
  let φ : ℝ → ℝ := fun s ↦ |s - a| - a
  have hφ : LipschitzWith 1 φ := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, φ, sub_sub_sub_cancel_right]
    simpa only [sub_sub_sub_cancel_right] using (abs_abs_sub_abs_le_abs_sub (s - a) (t - a))
  have hφ₀ : φ 0 = 0 := by simp [φ, abs_of_nonneg ha]
  have hsub : ((f - g : E.domain) : RealLp m p) =ᵐ[m] (fun x ↦ u x - v x) := by
    filter_upwards [Lp.coeFn_sub (f : RealLp m p) (g : RealLp m p), hfu, hgv] with x hx hf hg
    change ((f : RealLp m p) - (g : RealLp m p)) x = _
    rw [hx, Pi.sub_apply, hf, hg]
  obtain ⟨k, hk, hkE⟩ := E.exists_lipschitz_one_comp (f - g) hsub φ hφ hφ₀
  refine ⟨(1 / 2 : ℝ) • (f + g - k), ?_, ?_⟩
  · let F := (f : RealLp m p)
    let G := (g : RealLp m p)
    let K := (k : RealLp m p)
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (F + G - K), Lp.coeFn_sub (F + G) K,
      Lp.coeFn_add F G, hfu, hgv, hk] with x hx hsub' hadd' hf hg hkx
    change ((1 / 2 : ℝ) • (F + G - K)) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hsub', Pi.sub_apply, hadd', Pi.add_apply, hf, hg, hkx]
    dsimp only [φ, Function.comp_apply]
    by_cases h : u x ≤ v x + a
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right (le_of_not_ge h), abs_of_nonneg (by linarith [le_of_not_ge h])]
      ring
  · have hk' : E.rootSeminorm k ≤ E.rootSeminorm (f - g) := by
      rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr hkE)
        (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)
    have htriangle (r s : E.domain) : E.rootSeminorm (r - s) ≤ E.rootSeminorm r + E.rootSeminorm s := by
      rw [sub_eq_add_neg]
      have h := E.rootSeminorm.add_le' r (-s)
      change E.rootSeminorm (r + -s) ≤ E.rootSeminorm r + E.rootSeminorm (-s) at h
      rwa [map_neg_eq_map] at h
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have htotal := (htriangle (f + g) k).trans
      (add_le_add (E.rootSeminorm.add_le' f g) (hk'.trans (htriangle f g)))
    change E.rootSeminorm (f + g - k) ≤
      (E.rootSeminorm f + E.rootSeminorm g) + (E.rootSeminorm f + E.rootSeminorm g) at htotal
    linarith only [htotal]

end WalkDimensions.PEnergy
