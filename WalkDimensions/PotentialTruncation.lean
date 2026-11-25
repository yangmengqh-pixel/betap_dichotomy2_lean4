import WalkDimensions.EnergyTruncation
import WalkDimensions.PlateMinimizer
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Energy of intervals of a capacitary potential

Splitting the energy at one level allows a two-slope variation of the
potential. Optimality forces energy to be proportional to interval length.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} (E : PEnergy m p)

/-- Below a level (a), a minimizing potential has exactly a fraction
(a) of its total energy. -/
theorem exists_minimizer_truncation {K S : Set X} (hS : IsCompact S)
    {f : E.domain} {u : X → ℝ} (hf : E.UnitPlate K S f u)
    (hmin : ∀ g w, E.UnitPlate K S g w → E.energy f ≤ E.energy g)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ∃ l : E.domain, (l : RealLp m p) =ᵐ[m] (fun x ↦ min (u x) a) ∧
      (E.energy l : ℝ) = a * (E.energy f : ℝ) := by
  obtain ⟨hu, hfu, hunit, hu1, hu0⟩ := hf
  have huc : HasCompactSupport u := HasCompactSupport.intro hS hu0
  obtain ⟨l, h, hl, hh, _, hfE⟩ := E.exists_split_energy_at_level f hfu hu huc ha.1
  have htotal : (E.energy f : ℝ) = (E.energy l : ℝ) + (E.energy h : ℝ) := by
    rw [hfE, NNReal.coe_add]
  refine ⟨l, hl, ?_⟩
  by_cases ha₀ : a = 0
  · subst a
    have he : l = 0 := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hl, Lp.coeFn_zero (E := ℝ) (p := ENNReal.ofReal p) (μ := m)] with x hx hz
      change (l : RealLp m p) x = (0 : RealLp m p) x
      rw [hx, hz]
      exact min_eq_right (hunit x).1
    simp [he, E.energy_eq_root_rpow, Real.zero_rpow (zero_lt_one.trans E.one_lt).ne']
  by_cases ha₁ : a = 1
  · subst a
    have he : l = f := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hl, hfu] with x hlx hfx
      rw [hlx, hfx, min_eq_left (hunit x).2]
    simp [he]
  have hb' : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha.2 ha₁)
  let L : ℝ := E.energy l
  let H : ℝ := E.energy h
  have hvariation (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b * a + c * (1 - a) = 1) :
      (E.energy f : ℝ) ≤ b ^ p * L + c ^ p * H := by
    let v : X → ℝ := fun x ↦ b * min (u x) a + c * max (u x - a) 0
    let g := b • l + c • h
    have hv : Continuous v := (continuous_const.mul (hu.min continuous_const)).add
      (continuous_const.mul ((hu.sub continuous_const).max continuous_const))
    have hgv : (g : RealLp m p) =ᵐ[m] v := by
      filter_upwards [Lp.coeFn_add (b • (l : RealLp m p)) (c • (h : RealLp m p)),
        Lp.coeFn_smul b (l : RealLp m p), Lp.coeFn_smul c (h : RealLp m p), hl, hh]
        with x hx hbx hcx hlx hhx
      change (b • (l : RealLp m p) + c • (h : RealLp m p)) x = v x
      rw [hx, Pi.add_apply, hbx, hcx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hlx, hhx]
    have hv0 : EqOn v (fun _ ↦ 0) Sᶜ := by
      intro x hx
      change b * min (u x) a + c * max (u x - a) 0 = 0
      rw [hu0 hx, min_eq_left ha.1, zero_sub, max_eq_right (neg_nonpos.mpr ha.1)]
      ring
    have hvc : HasCompactSupport v := HasCompactSupport.intro hS hv0
    have hv1 : EqOn v (fun _ ↦ 1) K := by
      intro x hx
      change b * min (u x) a + c * max (u x - a) 0 = 1
      rw [hu1 hx, min_eq_right ha.2, max_eq_left hb'.le]
      exact hbc
    have hvRange (x : X) : v x ∈ Icc (0 : ℝ) 1 := by
      change 0 ≤ b * min (u x) a + c * max (u x - a) 0 ∧
        b * min (u x) a + c * max (u x - a) 0 ≤ 1
      refine ⟨add_nonneg (mul_nonneg hb (le_min (hunit x).1 ha.1))
        (mul_nonneg hc (le_max_right _ _)), ?_⟩
      exact (add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
        (mul_le_mul_of_nonneg_left (max_le (sub_le_sub_right (hunit x).2 _) hb'.le) hc)).trans_eq hbc
    obtain ⟨g₁, g₂, hg₁, hg₂, _, hgE⟩ :=
      E.exists_split_energy_at_level g hgv hv hvc (mul_nonneg hb ha.1)
    have hdecomp (x : X) :
        min (v x) (b * a) = b * min (u x) a ∧
        max (v x - b * a) 0 = c * max (u x - a) 0 := by
      by_cases hx : u x ≤ a
      · have hhx : max (u x - a) 0 = 0 := max_eq_right (sub_nonpos.mpr hx)
        have heb : b * u x ≤ b * a := mul_le_mul_of_nonneg_left hx hb
        have hvx : v x = b * u x := by simp only [v, min_eq_left hx, hhx, mul_zero, add_zero]
        rw [hvx, min_eq_left heb, min_eq_left hx, max_eq_right (sub_nonpos.mpr heb), hhx, mul_zero]
        exact ⟨rfl, rfl⟩
      · have hx' : a ≤ u x := le_of_not_ge hx
        have vv : v x = b * a + c * (u x - a) := by
          simp only [v, min_eq_right hx', max_eq_left (sub_nonneg.mpr hx')]
        have hhx : 0 ≤ c * (u x - a) := mul_nonneg hc (sub_nonneg.mpr hx')
        rw [vv, min_eq_right (by linarith : b * a ≤ b * a + c * (u x - a)),
          min_eq_right hx', add_sub_cancel_left, max_eq_left hhx, max_eq_left (sub_nonneg.mpr hx')]
        exact ⟨rfl, rfl⟩
    have h₁ : g₁ = b • l := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hg₁, Lp.coeFn_smul b (l : RealLp m p), hl] with x hx hs hlx
      change (g₁ : RealLp m p) x = (b • (l : RealLp m p)) x
      rw [hx, hs, Pi.smul_apply, smul_eq_mul, hlx]
      exact (hdecomp x).1
    have h₂ : g₂ = c • h := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [hg₂, Lp.coeFn_smul c (h : RealLp m p), hh] with x hx hs hhx
      change (g₂ : RealLp m p) x = (c • (h : RealLp m p)) x
      rw [hx, hs, Pi.smul_apply, smul_eq_mul, hhx]
      exact (hdecomp x).2
    have heg : (E.energy g : ℝ) = b ^ p * L + c ^ p * H := by
      rw [hgE, NNReal.coe_add, h₁, h₂, E.energy_smul_real, E.energy_smul_real,
        abs_of_nonneg hb, abs_of_nonneg hc]
    rw [← heg]
    exact NNReal.coe_le_coe.mpr (hmin g v ⟨hv, hgv, hvRange, hv1, hv0⟩)
  let b (t : ℝ) := 1 + t * (1 - a)
  let c (t : ℝ) := 1 - t * a
  let G (t : ℝ) := b t ^ p * L + c t ^ p * H
  have b₀ : b 0 = 1 := by simp [b]
  have c₀ : c 0 = 1 := by simp [c]
  have hb : HasDerivAt b (1 - a) 0 := by
    simpa only [b, id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (1 - a)).const_add 1
  have hc : HasDerivAt c (-a) 0 := by
    simpa only [c, id_eq, one_mul, zero_sub] using
      ((hasDerivAt_id (0 : ℝ)).mul_const a).const_sub 1
  have hG : HasDerivAt G (p * (1 - a) * L + p * (-a) * H) 0 := by
    have hb' := (hb.rpow_const (p := p) (Or.inl (b₀ ▸ one_ne_zero))).mul_const L
    have hc' := (hc.rpow_const (p := p) (Or.inl (c₀ ▸ one_ne_zero))).mul_const H
    convert hb'.add hc' using 1
    simp only [b₀, c₀, Real.one_rpow]
    ring
  have hminG : IsLocalMin G 0 := by
    have hbPos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < b t :=
      hb.continuousAt.eventually (lt_mem_nhds (by simp [b₀]))
    have hcPos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c t :=
      hc.continuousAt.eventually (lt_mem_nhds (by simp [c₀]))
    filter_upwards [hbPos, hcPos] with t hbt hct
    have hbc : b t * a + c t * (1 - a) = 1 := by dsimp [b, c]; ring
    have hG₀ : G 0 = (E.energy f : ℝ) := by
      dsimp only [G]
      rw [b₀, c₀, Real.one_rpow, one_mul, one_mul, htotal]
    rw [hG₀]
    exact hvariation (b t) (c t) hbt.le hct.le hbc
  have hcrit := hminG.hasDerivAt_eq_zero hG
  have hz : (1 - a) * L + (-a) * H = 0 := by
    apply (mul_eq_zero.mp (show p * ((1 - a) * L + (-a) * H) = 0 by linear_combination hcrit))
      |>.resolve_left (zero_lt_one.trans E.one_lt).ne'
  change L = a * (E.energy f : ℝ)
  change (E.energy f : ℝ) = L + H at htotal
  rw [htotal]
  linarith only [hz]


/-- Truncating a minimizing potential to an interval gives energy equal to
the interval length times the original energy. -/
theorem exists_minimizer_interval_truncation {K S : Set X} (hS : IsCompact S)
    {f : E.domain} {u : X → ℝ} (hf : E.UnitPlate K S f u)
    (hmin : ∀ g w, E.UnitPlate K S g w → E.energy f ≤ E.energy g)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
    ∃ g : E.domain, (g : RealLp m p) =ᵐ[m] (fun x ↦ max (min (u x) b - a) 0) ∧
      (E.energy g : ℝ) = (b - a) * (E.energy f : ℝ) := by
  obtain ⟨fₐ, hfₐ, hEₐ⟩ := E.exists_minimizer_truncation hS hf hmin ha
  obtain ⟨fᵦ, hfᵦ, hEᵦ⟩ := E.exists_minimizer_truncation hS hf hmin hb
  have huc : HasCompactSupport u := HasCompactSupport.intro hS hf.2.2.2.2
  have hc : HasCompactSupport (fun x ↦ min (u x) b) :=
    huc.comp_left (g := fun t : ℝ ↦ min t b) (min_eq_left hb.1)
  obtain ⟨l, g, hl, hg, _, hgE⟩ :=
    E.exists_split_energy_at_level fᵦ hfᵦ (hf.1.min continuous_const) hc ha.1
  have he : l = fₐ := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hl, hfₐ] with x hx hxa
    rw [hx, hxa, min_assoc, min_eq_right hab]
  rw [he] at hgE
  have h := congrArg (fun n : NNReal ↦ (n : ℝ)) hgE
  simp only [NNReal.coe_add] at h
  refine ⟨g, hg, ?_⟩
  rw [hEᵦ, hEₐ] at h
  linarith only [h,
    show (b - a) * (E.energy f : ℝ) = b * (E.energy f : ℝ) - a * (E.energy f : ℝ) by ring]

variable [ProperSpace X] [SecondCountableTopology X] [m.IsOpenPosMeasure]

/-- A minimizing potential is Hölder continuous with the resistance
exponent. The preceding interval-energy identity supplies the sharper
exponent than the general Morrey estimate. -/
theorem exists_minimizer_holder_bound {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ M > (0 : ℝ), ∀ {K S : Set X}, IsCompact S → ∀ {f : E.domain} {u : X → ℝ},
      E.UnitPlate K S f u → (∀ g w, E.UnitPlate K S g w → E.energy f ≤ E.energy g) →
      ∀ x y, |u x - u y| ≤ M * (E.energy f : ℝ) ^ (p - 1)⁻¹ * dist x y ^ ((β - d) / (p - 1)) := by
  obtain ⟨H, hH, hholder⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hp' : 0 < p - 1 := sub_pos.mpr E.one_lt
  refine ⟨(H ^ p) ^ (p - 1)⁻¹, by positivity, fun {K S} hS {f u} hf hmin x y ↦ ?_⟩
  have hdir (x y : X) (hxy : u y < u x) :
      u x - u y ≤ (H ^ p) ^ (p - 1)⁻¹ * (E.energy f : ℝ) ^ (p - 1)⁻¹ *
        dist x y ^ ((β - d) / (p - 1)) := by
    let a := u y
    let b := u x
    let δ := b - a
    have hδ : 0 < δ := sub_pos.mpr hxy
    obtain ⟨g, hg, hgE⟩ := E.exists_minimizer_interval_truncation hS hf hmin
      (hf.2.2.1 y) (hf.2.2.1 x) hxy.le
    let w : X → ℝ := fun z ↦ max (min (u z) b - a) 0
    have hw : Continuous w := ((hf.1.min continuous_const).sub continuous_const).max continuous_const
    obtain ⟨v, hv, hgv, hvbound⟩ := hholder g
    have he : v = w := Measure.eq_of_ae_eq (hgv.symm.trans hg) hv hw
    have hx : w x = δ := by
      dsimp only [w, b, a, δ]
      rw [min_self, max_eq_left (sub_nonneg.mpr hxy.le)]
    have hy : w y = 0 := by
      dsimp only [w, b, a]
      rw [min_eq_left hxy.le, sub_self, max_self]
    have h := hvbound x y
    rw [he, hx, hy, sub_zero, abs_of_pos hδ] at h
    have he := Real.rpow_le_rpow hδ.le h hp.le
    change (E.energy g : ℝ) = δ * (E.energy f : ℝ) at hgE
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg dist_nonneg _),
      Real.mul_rpow hH.le (apply_nonneg _ _), ← E.energy_eq_root_rpow, hgE,
      ← Real.rpow_mul dist_nonneg, div_mul_cancel₀ _ hp.ne'] at he
    have heq : δ ^ p = δ * δ ^ (p - 1) := by
      nth_rw 2 [← Real.rpow_one δ]
      rw [← Real.rpow_add hδ, show (1 : ℝ) + (p - 1) = p by ring]
    rw [heq, mul_left_comm (H ^ p) δ] at he
    have hpow : δ ^ (p - 1) ≤ H ^ p * (E.energy f : ℝ) * dist x y ^ (β - d) := by
      apply (mul_le_mul_iff_right₀ hδ).mp
      simpa only [mul_assoc] using he
    have hc := Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hpow (inv_nonneg.mpr hp'.le)
    rw [← Real.rpow_mul hδ.le, mul_inv_cancel₀ hp'.ne', Real.rpow_one,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (NNReal.coe_nonneg _),
      ← Real.rpow_mul dist_nonneg, ← div_eq_mul_inv] at hc
    exact hc
  rcases lt_trichotomy (u x) (u y) with h | h | h
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr h), dist_comm x y]
    exact hdir y x h
  · rw [h, sub_self, abs_zero]
    positivity
  · rw [abs_of_pos (sub_pos.mpr h)]
    exact hdir x y h

end WalkDimensions.PEnergy
