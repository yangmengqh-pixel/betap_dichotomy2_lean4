import WalkDimensions.SublevelEnergy
import WalkDimensions.StrongLocality

/-!
# Operations on the continuous compact core
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

noncomputable def neg (f : E.CompactCore) : E.CompactCore where
  domainElement := -f.domainElement
  toFun := -f.toFun
  ae_eq := by
    filter_upwards [Lp.coeFn_neg (f.domainElement : RealLp μ p), f.ae_eq] with x hx hy
    change (-(f.domainElement : RealLp μ p)) x = _
    rw [hx, Pi.neg_apply, hy]
    rfl
  continuous := f.continuous.neg
  compactSupport := f.compactSupport.neg

noncomputable def add (f g : E.CompactCore) : E.CompactCore where
  domainElement := f.domainElement + g.domainElement
  toFun := f.toFun + g.toFun
  ae_eq := by
    filter_upwards [Lp.coeFn_add (f.domainElement : RealLp μ p) (g.domainElement : RealLp μ p),
      f.ae_eq, g.ae_eq] with x hx hy hz
    change ((f.domainElement : RealLp μ p) + (g.domainElement : RealLp μ p)) x = _
    rw [hx, Pi.add_apply, Pi.add_apply, hy, hz]
  continuous := f.continuous.add g.continuous
  compactSupport := f.compactSupport.add g.compactSupport

noncomputable def smul (r : ℝ) (f : E.CompactCore) : E.CompactCore where
  domainElement := r • f.domainElement
  toFun x := r * f.toFun x
  ae_eq := by
    filter_upwards [Lp.coeFn_smul r (f.domainElement : RealLp μ p), f.ae_eq] with x hx hy
    change (r • (f.domainElement : RealLp μ p)) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hy]
  continuous := continuous_const.mul f.continuous
  compactSupport := f.compactSupport.comp_left (g := fun t ↦ r * t) (mul_zero _)

noncomputable def mapLipschitz (f : E.CompactCore) (φ : ℝ → ℝ)
    (hφ : LipschitzWith 1 φ) (hφ₀ : φ 0 = 0) : E.CompactCore where
  domainElement := (E.exists_lipschitz_one_comp f.domainElement f.ae_eq φ hφ hφ₀).choose
  toFun := φ ∘ f.toFun
  ae_eq := (E.exists_lipschitz_one_comp f.domainElement f.ae_eq φ hφ hφ₀).choose_spec.1
  continuous := hφ.continuous.comp f.continuous
  compactSupport := f.compactSupport.comp_left hφ₀

theorem root_mapLipschitz_le (f : E.CompactCore) (φ : ℝ → ℝ)
    (hφ : LipschitzWith 1 φ) (hφ₀ : φ 0 = 0) :
    E.rootSeminorm (f.mapLipschitz φ hφ hφ₀).domainElement ≤ E.rootSeminorm f.domainElement := by
  rw [E.rootSeminorm_apply, E.rootSeminorm_apply]
  exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr
    (E.exists_lipschitz_one_comp f.domainElement f.ae_eq φ hφ hφ₀).choose_spec.2)
    (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)

noncomputable def minAddConst (f g : E.CompactCore) {a : ℝ} (ha : 0 ≤ a) :
    E.CompactCore where
  domainElement := (E.exists_min_add_const f.domainElement g.domainElement f.ae_eq g.ae_eq ha).choose
  toFun x := min (f.toFun x) (g.toFun x + a)
  ae_eq := (E.exists_min_add_const f.domainElement g.domainElement f.ae_eq g.ae_eq ha).choose_spec.1
  continuous := f.continuous.min (g.continuous.add continuous_const)
  compactSupport := by
    apply (f.compactSupport.isCompact.union g.compactSupport.isCompact).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ (isClosed_closure.union isClosed_closure)
    intro x hx
    by_contra h
    have hf : f.toFun x = 0 := notMem_support.mp fun hx' ↦ h (Or.inl (subset_closure hx'))
    have hg : g.toFun x = 0 := notMem_support.mp fun hx' ↦ h (Or.inr (subset_closure hx'))
    apply hx
    change min (f.toFun x) (g.toFun x + a) = 0
    rw [hf, hg, zero_add, min_eq_left ha]

theorem root_minAddConst_le (f g : E.CompactCore) {a : ℝ} (ha : 0 ≤ a) :
    E.rootSeminorm (f.minAddConst g ha).domainElement ≤
      E.rootSeminorm f.domainElement + E.rootSeminorm g.domainElement :=
  (E.exists_min_add_const f.domainElement g.domainElement f.ae_eq g.ae_eq ha).choose_spec.2

noncomputable def sup (f g : E.CompactCore) : E.CompactCore :=
  (f.neg.minAddConst g.neg (a := 0) le_rfl).neg

theorem sup_apply (f g : E.CompactCore) (x : X) :
    (f.sup g).toFun x = max (f.toFun x) (g.toFun x) := by
  change -min (-f.toFun x) (-g.toFun x + 0) = _
  rw [add_zero, min_neg_neg, neg_neg]

theorem root_sup_le (f g : E.CompactCore) :
    E.rootSeminorm (f.sup g).domainElement ≤
      E.rootSeminorm f.domainElement + E.rootSeminorm g.domainElement := by
  change E.rootSeminorm (-(f.neg.minAddConst g.neg le_rfl).domainElement) ≤ _
  rw [map_neg_eq_map]
  simpa only [neg, map_neg_eq_map] using f.neg.root_minAddConst_le g.neg (a := 0) le_rfl

noncomputable def ramp (g : E.CompactCore) (r a : ℝ) : E.CompactCore :=
  g.mapLipschitz (offsetRamp r a) (lipschitzWith_offsetRamp r a) (offsetRamp_zero r a)

theorem domainElement_eq_of_toFun_eq (f g : E.CompactCore) (h : f.toFun = g.toFun) :
    f.domainElement = g.domainElement := by
  apply Subtype.ext
  apply Lp.ext
  have hf := f.ae_eq
  rw [h] at hf
  exact hf.trans g.ae_eq.symm

theorem tendsto_graph_ramp (g : E.CompactCore) (a : ℝ) :
    Tendsto (fun n ↦ E.graphSeminorm (g.ramp (oscillationWidth n) a).domainElement)
      atTop (𝓝 0) := by
  obtain ⟨r, hr, hlim⟩ := E.exists_ramp_graph_tendsto_zero g.domainElement g.ae_eq
    g.compactSupport a oscillationWidth (fun n ↦ (oscillationWidth_pos n).le)
    oscillationWidth_antitone tendsto_oscillationWidth
  have he (n : ℕ) : (g.ramp (oscillationWidth n) a).domainElement = r n := by
    apply Subtype.ext
    apply Lp.ext
    exact (g.ramp (oscillationWidth n) a).ae_eq.trans (hr n).symm
  simpa only [he] using hlim

theorem tendsto_root_ramp (g : E.CompactCore) (a : ℝ) :
    Tendsto (fun n ↦ E.rootSeminorm (g.ramp (oscillationWidth n) a).domainElement)
      atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ apply_nonneg _ _) (fun _ ↦ E.rootSeminorm_le_graphSeminorm _)
    (g.tendsto_graph_ramp a)

theorem energy_add_of_disjoint_support (f g : E.CompactCore)
    (h : Disjoint (support f.toFun) (support g.toFun)) :
    E.energy (f.add g).domainElement = E.energy f.domainElement + E.energy g.domainElement := by
  have hg : ∀ x ∈ support f.toFun, g.toFun x = 0 :=
    fun _ hx ↦ notMem_support.mp (Set.disjoint_left.mp h hx)
  exact E.stronglyLocal_of_const_on_support f.domainElement g.domainElement f.ae_eq g.ae_eq
    f.continuous f.compactSupport g.compactSupport hg

end WalkDimensions.PEnergy.CompactCore
