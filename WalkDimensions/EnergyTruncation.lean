import WalkDimensions.CompactEnergyLimit

/-!
# Splitting energy at a level

Strong locality applies first with a positive gap between the two
truncations. Lower semicontinuity and the Markov property remove the gap.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

theorem exists_lipschitz_one_comp (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (φ : ℝ → ℝ) (hφ : LipschitzWith 1 φ)
    (hzero : φ 0 = 0) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] φ ∘ u ∧ E.energy g ≤ E.energy f := by
  obtain ⟨g, hg, henergy⟩ := E.markov φ hφ hzero f
  refine ⟨g, hg.trans (hfu.mono (fun x hx ↦ ?_)), henergy⟩
  exact congrArg φ hx

theorem exists_lipschitz_comp (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) {L : ℝ≥0} (φ : ℝ → ℝ)
    (hφ : LipschitzWith L φ) (hzero : φ 0 = 0) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] φ ∘ u ∧
      (E.energy g : ℝ) ≤ (L : ℝ) ^ p * (E.energy f : ℝ) := by
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  by_cases hL : L = 0
  · subst L
    have hφ' (t : ℝ) : φ t = 0 := by
      have h := lipschitzWith_iff_dist_le_mul.mp hφ t 0
      rw [hzero, NNReal.coe_zero, zero_mul] at h
      exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
    refine ⟨0, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_zero (E := ℝ) (p := ENNReal.ofReal p) (μ := m)] with x hx
      exact hx.trans (hφ' (u x)).symm
    · simp [E.energy_eq_root_rpow, Real.zero_rpow hp.ne']
  · have hLpos : 0 < (L : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL)
    let ψ : ℝ → ℝ := fun t ↦ (L : ℝ)⁻¹ * φ t
    have hψ : LipschitzWith 1 ψ := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      have h := lipschitzWith_iff_dist_le_mul.mp hφ x y
      simp only [Real.dist_eq] at h
      dsimp only [ψ]
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hLpos.le), NNReal.coe_one, one_mul]
      exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hLpos.le)).trans_eq (by
        rw [← mul_assoc, inv_mul_cancel₀ hLpos.ne', one_mul])
    have hψ₀ : ψ 0 = 0 := by simp [ψ, hzero]
    obtain ⟨g, hg, hgE⟩ := E.exists_lipschitz_one_comp f hfu ψ hψ hψ₀
    refine ⟨(L : ℝ) • g, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul (L : ℝ) (g : RealLp m p), hg] with x hx hgx
      change ((L : ℝ) • (g : RealLp m p)) x = φ (u x)
      rw [hx, Pi.smul_apply, smul_eq_mul, hgx]
      dsimp only [Function.comp_apply, ψ]
      rw [← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul]
    · rw [E.energy_smul_real, abs_of_nonneg hLpos.le]
      exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hgE) (by positivity)

/-- Rescale an interval to ([0,1]\) and truncate outside it. -/
noncomputable def unitClip (a b t : ℝ) : ℝ := min (max ((t - a) / (b - a)) 0) 1

theorem unitClip_mem_Icc (a b t : ℝ) : unitClip a b t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

theorem unitClip_eq_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    unitClip a b t = 0 := by
  unfold unitClip
  rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hab.le)),
    min_eq_left zero_le_one]

theorem unitClip_eq_one {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    unitClip a b t = 1 := by
  have h : 1 ≤ (t - a) / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    simpa only [one_mul] using sub_le_sub_right ht a
  exact min_eq_right (h.trans (le_max_left _ _))

theorem exists_unitClip_comp (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] unitClip a b ∘ u ∧
      (E.energy g : ℝ) ≤ (b - a) ^ (-p) * (E.energy f : ℝ) := by
  let L : ℝ≥0 := ⟨(b - a)⁻¹, inv_nonneg.mpr (sub_nonneg.mpr hab.le)⟩
  have h : LipschitzWith L (fun t : ℝ ↦ (t - a) / (b - a)) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, sub_sub_sub_cancel_right, abs_div,
      abs_of_pos (sub_pos.mpr hab), div_eq_mul_inv, mul_comm]
    exact le_rfl
  have hclip : LipschitzWith L (unitClip a b) := by
    unfold unitClip
    exact (h.max_const 0).min_const 1
  obtain ⟨g, hg, hgE⟩ := E.exists_lipschitz_comp f hfu (unitClip a b) hclip (unitClip_eq_zero hab ha)
  refine ⟨g, hg, ?_⟩
  change (E.energy g : ℝ) ≤ (b - a)⁻¹ ^ p * (E.energy f : ℝ) at hgE
  rwa [Real.inv_rpow (sub_nonneg.mpr hab.le), ← Real.rpow_neg (sub_nonneg.mpr hab.le)] at hgE

/-- The parts below and above a nonnegative level have additive energy. -/
theorem exists_split_energy_at_level (f : E.domain) {u : X → ℝ}
    (hfu : (f : RealLp m p) =ᵐ[m] u) (hu : Continuous u) (hc : HasCompactSupport u)
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ l h : E.domain,
      (l : RealLp m p) =ᵐ[m] (fun x ↦ min (u x) a) ∧
      (h : RealLp m p) =ᵐ[m] (fun x ↦ max (u x - a) 0) ∧
      f = l + h ∧ E.energy f = E.energy l + E.energy h := by
  let low : X → ℝ := fun x ↦ min (u x) a
  let high : X → ℝ := fun x ↦ max (u x - a) 0
  have hmaxLip (t : ℝ) : LipschitzWith 1 (fun s : ℝ ↦ max (s - t) 0) := by
    have hsub : LipschitzWith 1 (fun s : ℝ ↦ s - t) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      simp only [Real.dist_eq, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul, le_refl]
    exact hsub.max_const 0
  have hmax₀ {t : ℝ} (ht : 0 ≤ t) : max (0 - t) 0 = 0 := by
    rw [zero_sub, max_eq_right (neg_nonpos.mpr ht)]
  obtain ⟨l, hl, hleLow⟩ := E.exists_lipschitz_one_comp f hfu (fun t ↦ min t a)
    (LipschitzWith.id.min_const a) (min_eq_left ha)
  obtain ⟨h, hh, _⟩ := E.exists_lipschitz_one_comp f hfu (fun t ↦ max (t - a) 0)
    (hmaxLip a) (hmax₀ ha)
  have haddAE {g k : E.domain} {v w : X → ℝ}
      (hgv : (g : RealLp m p) =ᵐ[m] v) (hkw : (k : RealLp m p) =ᵐ[m] w) :
      ((g + k : E.domain) : RealLp m p) =ᵐ[m] fun x ↦ v x + w x := by
    filter_upwards [Lp.coeFn_add (g : RealLp m p) (k : RealLp m p), hgv, hkw] with x hx hv hw
    change ((g : RealLp m p) + (k : RealLp m p)) x = v x + w x
    rw [hx, Pi.add_apply, hv, hw]
  have hadd (x : X) : low x + high x = u x := by
    by_cases hx : u x ≤ a
    · simp only [low, high, min_eq_left hx, max_eq_right (sub_nonpos.mpr hx), add_zero]
    · simp only [low, high, min_eq_right (le_of_not_ge hx), max_eq_left (sub_nonneg.mpr (le_of_not_ge hx))]
      ring
  refine ⟨l, h, hl, hh, ?_, ?_⟩
  · apply Subtype.ext
    apply Lp.ext
    have hsum : ((l + h : E.domain) : RealLp m p) =ᵐ[m] u :=
      (haddAE hl hh).mono (fun x hx ↦ hx.trans (hadd x))
    exact hfu.trans hsum.symm
  let highGap (ε : ℝ) : X → ℝ := fun x ↦ max (u x - a - ε) 0
  have hgap (ε : ℝ) (hε : 0 < ε) :
      ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] highGap ε ∧
        E.energy g ≤ E.energy h ∧ E.energy (l + g) = E.energy l + E.energy g ∧
        E.energy (l + g) ≤ E.energy f := by
    obtain ⟨g, hg', hgH⟩ := E.exists_lipschitz_one_comp h hh (fun t ↦ max (t - ε) 0)
      (hmaxLip ε) (hmax₀ hε.le)
    have hg : (g : RealLp m p) =ᵐ[m] highGap ε := hg'.mono fun x hx ↦ by
      rw [hx]
      change max (max (u x - a) 0 - ε) 0 = max (u x - a - ε) 0
      by_cases hx' : u x - a ≤ 0
      · rw [max_eq_right hx', zero_sub, max_eq_right (neg_nonpos.mpr hε.le),
          max_eq_right (by linarith)]
      · rw [max_eq_left (le_of_not_ge hx')]
    have hcL : HasCompactSupport low := hc.comp_left (g := fun t : ℝ ↦ min t a) (min_eq_left ha)
    have hcG : HasCompactSupport (highGap ε) :=
      hc.comp_left (g := fun t : ℝ ↦ max (t - a - ε) 0) (by
        exact max_eq_right (by linarith))

    have hGsub : tsupport (highGap ε) ⊆ {x | a < u x} := by
      have hs : tsupport (highGap ε) ⊆ {x | a + ε ≤ u x} := by
        apply closure_minimal _ (isClosed_le continuous_const hu)
        intro x hx
        change a + ε ≤ u x
        by_contra! h
        exact hx (max_eq_right (by linarith))
      exact fun x hx ↦ (lt_add_of_pos_right a hε).trans_le (hs hx)
    have hloc := E.stronglyLocal g l (highGap ε) low hg hl hcG hcL
      ⟨{x | a < u x}, isOpen_lt continuous_const hu, hGsub, a,
        fun x hx ↦ min_eq_right hx.le⟩
    have headd : E.energy (l + g) = E.energy l + E.energy g := by simpa only [add_comm] using hloc
    let φ : ℝ → ℝ := fun t ↦ max (min t a) (t - ε)
    have hsub : LipschitzWith 1 (fun t : ℝ ↦ t - ε) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      simp only [Real.dist_eq, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul, le_refl]
    have hLip : LipschitzWith 1 φ := by
      unfold φ
      simpa only [max_self, id_eq] using (LipschitzWith.id.min_const a).max hsub
    have hφ₀ : φ 0 = 0 := by
      dsimp only [φ]
      rw [min_eq_left ha, zero_sub, max_eq_left (neg_nonpos.mpr hε.le)]
    obtain ⟨k, hk, hkE⟩ := E.exists_lipschitz_one_comp f hfu φ hLip hφ₀
    have hEq (x : X) : low x + highGap ε x = φ (u x) := by
      dsimp only [low, highGap, φ]
      by_cases hx : u x ≤ a
      · rw [min_eq_left hx, max_eq_right (by linarith : u x - a - ε ≤ 0), add_zero,
          max_eq_left (by linarith : u x - ε ≤ u x)]
      · rw [min_eq_right (le_of_not_ge hx)]
        by_cases hεx : u x - a - ε ≤ 0
        · rw [max_eq_right hεx, add_zero, max_eq_left (by linarith : u x - ε ≤ a)]
        · rw [max_eq_left (le_of_not_ge hεx), max_eq_right (by linarith : a ≤ u x - ε)]
          ring
    have hgl : l + g = k := by
      apply Subtype.ext
      apply Lp.ext
      have hh : ((l + g : E.domain) : RealLp m p) =ᵐ[m] φ ∘ u :=
        (haddAE hl hg).mono (fun x hx ↦ hx.trans (hEq x))
      exact hh.trans hk.symm
    exact ⟨g, hg, hgH, headd, hgl ▸ hkE⟩
  let S := tsupport u
  have hS : MeasurableSet S := isClosed_closure.measurableSet
  have hSfin : m S ≠ ∞ := (hc.isCompact.measure_lt_top (μ := m)).ne
  have hbound (ε : ℝ) (hε : 0 < ε) (x : X) :
      |highGap ε x - high x| ≤ S.indicator (fun _ ↦ ε) x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have h := lipschitzWith_iff_dist_le_mul.mp (LipschitzWith.id.max_const (0 : ℝ))
        (u x - a - ε) (u x - a)
      simpa only [id_eq, Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_cancel_left,
        abs_neg, abs_of_pos hε] using h
    · rw [indicator_of_notMem hx]
      have hx₀ : u x = 0 := notMem_support.mp (fun h ↦ hx (subset_closure h))
      simp only [highGap, high, hx₀, zero_sub, max_eq_right (by linarith : -a - ε ≤ 0),
        max_eq_right (neg_nonpos.mpr ha), sub_self, abs_zero, le_refl]
  have hlow' : (E.energy l : ℝ) ≤ E.energy f := NNReal.coe_le_coe.mpr hleLow
  have h₁ : (E.energy h : ℝ) ≤ (E.energy f : ℝ) - (E.energy l : ℝ) := by
    apply E.energy_le_of_uniform_approximation h high hh hS hSfin (sub_nonneg.mpr hlow')
    intro ε hε
    obtain ⟨g, hg, _, heq, he⟩ := hgap ε hε
    have he' : (E.energy (l + g) : ℝ) ≤ (E.energy f : ℝ) := NNReal.coe_le_coe.mpr he
    rw [heq, NNReal.coe_add] at he'
    exact ⟨g, highGap ε, hg, hbound ε hε, by linarith⟩
  have h₂ : (E.energy f : ℝ) ≤ (E.energy l : ℝ) + (E.energy h : ℝ) := by
    apply E.energy_le_of_uniform_approximation f u hfu hS hSfin (by positivity)
    intro ε hε
    obtain ⟨g, hg, hE, heq, _⟩ := hgap ε hε
    refine ⟨l + g, fun x ↦ low x + highGap ε x, haddAE hl hg, fun x ↦ ?_, ?_⟩
    · rw [← hadd x, add_sub_add_left_eq_sub]
      exact hbound ε hε x
    · rw [heq, NNReal.coe_add]
      exact add_le_add_right (NNReal.coe_le_coe.mpr hE) _
  apply NNReal.eq
  rw [NNReal.coe_add]
  linarith only [h₁, h₂]

end WalkDimensions.PEnergy
