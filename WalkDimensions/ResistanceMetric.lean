import WalkDimensions.ResistanceTriangle
import WalkDimensions.SmallCutoffs

/-!
# The power of point resistance is a metric

Small-energy cutoffs supply symmetry. The capacity bounds identify the
topology induced by the resulting distance.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

theorem singleton_capacity_comm {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β) (x y : X) :
    E.capacity {x} {y} = E.capacity {y} {x} := by
  by_cases he : x = y
  · rw [he]
  obtain ⟨_, U, _, _, hC⟩ := E.singleton_capacity_bounds hvol hβ hPI hΓ hcap
  have hfin (a b : X) (hab : a ≠ b) : E.capacity {a} {b} ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC a b hab).2
  have hdir (a b : X) (hab : a ≠ b) : E.capacity {b} {a} ≤ E.capacity {a} {b} := by
    apply (ENNReal.toReal_le_toReal (hfin b a hab.symm) (hfin a b hab)).mp
    apply le_of_forall_pos_le_add
    intro ε hε
    let R := (E.capacity {a} {b}).toReal
    have hR : 0 ≤ R := ENNReal.toReal_nonneg
    have hlt : E.capacity {a} {b} < ENNReal.ofReal (R + ε / 2) := by
      rw [← ENNReal.ofReal_toReal (hfin a b hab)]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨lt_add_of_pos_right _ (half_pos hε), by positivity⟩
    obtain ⟨f, u, hu, huc, hfu, _, ha, hb, hE⟩ :=
      E.exists_compact_singleton_capacity_approximant hvol hβ hPI hΓ hlt
    let K := tsupport u ∪ ({a, b} : Set X)
    have hK : IsCompact K := huc.isCompact.union (isCompact_singleton.insert a)
    obtain ⟨g, v, W, hv, hvc, hgv, hW, hKW, hconst, hEg⟩ :=
      E.exists_small_energy_cutoff hvol hβ hPI hΓ hcap hK a (half_pos hε)
    have hneg : ((-f : E.domain) : RealLp m p) =ᵐ[m] fun t ↦ -u t := by
      filter_upwards [Lp.coeFn_neg (f : RealLp m p), hfu] with t ht htu
      change (-(f : RealLp m p)) t = _
      rw [ht, Pi.neg_apply, htu]
    have hnegC : HasCompactSupport (fun t ↦ -u t) :=
      huc.comp_left (g := fun q : ℝ ↦ -q) neg_zero
    have hnegS : tsupport (fun t ↦ -u t) ⊆ tsupport u := by
      apply closure_mono
      intro t ht
      exact fun htu ↦ ht (by simp [htu])
    have hloc := E.stronglyLocal (-f) g (fun t ↦ -u t) v hneg hgv hnegC hvc
      ⟨W, hW, hnegS.trans (subset_union_left.trans hKW), 1, hconst⟩
    have hnegE : (E.energy (-f) : ℝ) = (E.energy f : ℝ) := by
      rw [E.energy_eq_root_rpow, E.energy_eq_root_rpow, map_neg_eq_map]
    let w : X → ℝ := fun t ↦ v t - u t
    have hw : ((-f + g : E.domain) : RealLp m p) =ᵐ[m] w := by
      filter_upwards [Lp.coeFn_add ((-f : E.domain) : RealLp m p) (g : RealLp m p), hneg, hgv]
        with t ht htneg htv
      change (((-f : E.domain) : RealLp m p) + (g : RealLp m p)) t = _
      rw [ht, Pi.add_apply, htneg, htv]
      dsimp [w]
      ring
    have hv_a := hconst (hKW (Or.inr (mem_insert _ _)) : a ∈ W)
    have hv_b := hconst (hKW (Or.inr (mem_insert_of_mem _ (mem_singleton b))) : b ∈ W)
    have hwb : w b = 1 := by simp only [w, hv_b, hb, sub_zero]
    have hwa : w a = 0 := by simp only [w, hv_a, ha, sub_self]
    have hcap' := ENNReal.toReal_mono ENNReal.coe_ne_top
      (E.singleton_capacity_le_of_point_values hw (hv.sub hu) hwb hwa)
    rw [ENNReal.coe_toReal, hloc, NNReal.coe_add, hnegE] at hcap'
    exact hcap'.trans (by linarith only [hE, hEg])
  exact le_antisymm (hdir y x (fun h ↦ he h.symm)) (hdir x y he)

theorem pointResistanceLength_comparable {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x y,
      c * dist x y ^ ((β - d) / (p - 1)) ≤ E.pointResistanceLength x y ∧
      E.pointResistanceLength x y ≤ C * dist x y ^ ((β - d) / (p - 1)) := by
  obtain ⟨L, U, hL, hU, hb⟩ := E.singleton_capacity_bounds hvol hβ hPI hΓ hcap
  let e := (p - 1)⁻¹
  have he : 0 < e := inv_pos.mpr (sub_pos.mpr E.one_lt)
  have hγ : 0 < (β - d) / (p - 1) := div_pos (sub_pos.mpr hβ) (sub_pos.mpr E.one_lt)
  refine ⟨(U⁻¹) ^ e, (L⁻¹) ^ e, by positivity, by positivity, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    simp only [dist_self, E.pointResistanceLength_self, Real.zero_rpow hγ.ne', mul_zero, le_refl, and_self]
  have hr : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨hLo, hHi⟩ := hb x y hxy
  have hfin : E.capacity {x} {y} ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hHi
  have hl := ENNReal.toReal_mono hfin hLo
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hHi
  rw [ENNReal.toReal_ofReal (by positivity)] at hl hh
  have hc : 0 < (E.capacity {x} {y}).toReal := (by positivity : 0 < L * dist x y ^ (d - β)).trans_le hl
  have hlow := one_div_le_one_div_of_le hc hh
  have hhigh := one_div_le_one_div_of_le (by positivity : 0 < L * dist x y ^ (d - β)) hl
  have hPow (K : ℝ) (hK : 0 < K) :
      (1 / (K * dist x y ^ (d - β))) ^ e = (K⁻¹) ^ e * dist x y ^ ((β - d) / (p - 1)) := by
    rw [one_div, mul_inv, ← Real.rpow_neg hr.le, show -(d - β) = β - d by ring,
      Real.mul_rpow (inv_nonneg.mpr hK.le) (by positivity), ← Real.rpow_mul hr.le, div_eq_mul_inv]
  rw [pointResistanceLength, resistance, ENNReal.toReal_inv]
  have hLo' := Real.rpow_le_rpow (by positivity) hlow he.le
  have hHi' := Real.rpow_le_rpow (by positivity) hhigh he.le
  rw [hPow U hU, one_div] at hLo'
  rw [hPow L hL, one_div] at hHi'
  exact ⟨hLo', hHi'⟩


/-- The resistance distance defines a metric with the original topology. -/
theorem exists_pointResistanceMetric {d β : ℝ}
    (hvol : AhlforsRegular m d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β) :
    let ρ := E.pointResistanceLength
    let T := (inferInstance : TopologicalSpace X)
    ∃ D : MetricSpace X, @Dist.dist X D.toDist = ρ ∧
      D.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = T := by
  obtain ⟨c, C, hc, hC, hcompare⟩ := E.pointResistanceLength_comparable hvol hβ hPI hΓ hcap
  let e := (β - d) / (p - 1)
  have he : 0 < e := div_pos (sub_pos.mpr hβ) (sub_pos.mpr E.one_lt)
  have hsym (x y : X) : E.pointResistanceLength x y = E.pointResistanceLength y x := by
    unfold pointResistanceLength resistance
    rw [E.singleton_capacity_comm hvol hβ hPI hΓ hcap x y]
  have hzero (x y : X) (h : E.pointResistanceLength x y = 0) : x = y := by
    by_contra hxy
    have hr : 0 < dist x y := dist_pos.mpr hxy
    have hpos : 0 < c * dist x y ^ e := mul_pos hc (Real.rpow_pos_of_pos hr _)
    have hh := (hcompare x y).1
    rw [h] at hh
    exact hpos.not_ge hh
  have htopo (S : Set X) :
      IsOpen S ↔ ∀ x ∈ S, ∃ ε > 0, ∀ y, E.pointResistanceLength x y < ε → y ∈ S := by
    rw [Metric.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨r, hr, hball⟩ := h x hx
      refine ⟨c * r ^ e, by positivity, fun y hy ↦ hball ?_⟩
      have hrpow : dist x y ^ e < r ^ e :=
        (mul_lt_mul_iff_right₀ hc).mp ((hcompare x y).1.trans_lt hy)
      exact mem_ball.mpr (by rw [dist_comm y x]; exact
        (Real.rpow_lt_rpow_iff dist_nonneg hr.le he).mp hrpow)
    · intro h x hx
      obtain ⟨ε, hε, hball⟩ := h x hx
      let r := (ε / C) ^ e⁻¹
      have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hε hC) _
      have heq : C * r ^ e = ε := by
        dsimp only [r]
        rw [← Real.rpow_mul (div_nonneg hε.le hC.le), inv_mul_cancel₀ he.ne', Real.rpow_one,
          ← mul_div_assoc, mul_comm C ε, mul_div_cancel_right₀ _ hC.ne']
      refine ⟨r, hr, fun y hy ↦ hball y ?_⟩
      rw [← heq]
      apply (hcompare x y).2.trans_lt
      apply mul_lt_mul_of_pos_left _ hC
      exact Real.rpow_lt_rpow dist_nonneg (by rw [dist_comm x y]; exact mem_ball.mp hy) he
  exact ⟨MetricSpace.ofDistTopology E.pointResistanceLength E.pointResistanceLength_self hsym
    (E.pointResistanceLength_triangle hvol hβ hPI hΓ hcap) htopo hzero, rfl, rfl⟩

end WalkDimensions.PEnergy
