import WalkDimensions.DetourDeficit
import WalkDimensions.PathComponents
import WalkDimensions.SeriesContinuity
import WalkDimensions.SeriesTest
import WalkDimensions.SmallEnergyCutoff
import WalkDimensions.SmallZeroPlate

/-!
# A positive triangle deficit gives an annular detour

The absence of an annular path separates the two truncated point tests.
The series bound for the separated tests controls the deficit.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

theorem exists_detour_of_positive_deficit {d β : ℝ}
    (hvol : AhlforsRegular μ d) (hβ : d < β)
    {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hCC : ChainCondition X) {lower upper ξ : ℝ}
    (hLower : 0 < lower) (hUpper : 0 < upper) (hξ : 0 < ξ) :
    let γ := (β - d) / (p - 1)
    ∃ L a : ℝ, 0 < L ∧ 0 < a ∧ ∀ (x y z : X) (r : ℝ), 0 < r →
      BalancedWithin lower upper dist x y z r →
      ξ ≤ relativeDeficit E.pointResistanceLength γ x y z r →
      ∃ φ : ℝ → X, ContinuousOn φ (Icc 0 1) ∧ φ 0 = x ∧ φ 1 = z ∧
        ∀ t ∈ Icc (0 : ℝ) 1, dist (φ t) y ≤ L * r ∧ a * r ≤ dist (φ t) y := by
  let _ : LocallyPathConnectedSpace X := hCC.locallyPathConnectedSpace
  let γ := (β - d) / (p - 1)
  have hγ : 0 < γ := div_pos (sub_pos.mpr hβ) (sub_pos.mpr E.one_lt)
  let ρ := E.pointResistanceLength
  obtain ⟨c, C, hc, hC, hρ⟩ := E.pointResistanceLength_comparable hvol hβ hPI hΓ hcap
  let lo := c * lower ^ γ
  let hi := lo + C * upper ^ γ
  have hlo : 0 < lo := mul_pos hc (Real.rpow_pos_of_pos hLower _)
  have hlohi : lo ≤ hi := le_add_of_nonneg_right (by positivity)
  obtain ⟨ε, hε, hLoss⟩ := exists_series_resistance_loss E.one_lt hlo hlohi hξ
  obtain ⟨δ, hδ, hSmall⟩ :=
    E.exists_compact_test_zero_on_small_ball hvol hβ hPI hΓ hcap hLower hε
  obtain ⟨L, hL, hLarge⟩ :=
    E.exists_small_energy_large_cutoff hvol hβ hPI hΓ hcap hUpper hε
  let a := min δ lower / 2
  have ha : 0 < a := half_pos (lt_min hδ hLower)
  have had : a < δ :=
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans_lt (half_lt_self hδ)
  have hal : a < lower :=
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self hLower)
  refine ⟨L, a, hUpper.trans hL, ha, fun x y z r hr hbal hDef ↦ ?_⟩
  let R := r ^ (d - β)
  have hR : 0 < R := Real.rpow_pos_of_pos hr _
  have hrg : 0 < r ^ γ := Real.rpow_pos_of_pos hr γ
  let U := ball y (L * r) \ closedBall y (a * r)
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hxU : x ∈ U := ⟨mem_ball.mpr (hbal.1.2.trans_lt (mul_lt_mul_of_pos_right hL hr)),
    fun h ↦ (mul_lt_mul_of_pos_right hal hr).not_ge (hbal.1.1.trans (mem_closedBall.mp h))⟩
  have hzy : dist z y ∈ Icc (lower * r) (upper * r) := by rw [dist_comm]; exact hbal.2.1
  have hzU : z ∈ U := ⟨mem_ball.mpr (hzy.2.trans_lt (mul_lt_mul_of_pos_right hL hr)),
    fun h ↦ (mul_lt_mul_of_pos_right hal hr).not_ge (hzy.1.trans (mem_closedBall.mp h))⟩
  have hComp {u v : X} (h : dist u v ∈ Icc (lower * r) (upper * r)) :
      ρ u v / r ^ γ ∈ Icc lo hi := by
    obtain ⟨h₁, h₂⟩ := hρ u v
    refine ⟨(le_div_iff₀ hrg).mpr ?_, (div_le_iff₀ hrg).mpr ?_⟩
    · apply le_trans _ h₁
      dsimp [lo]
      rw [mul_assoc, ← Real.mul_rpow hLower.le hr.le]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h.1 hγ.le) hc.le
    · apply h₂.trans
      have hD := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg h.2 hγ.le) hC.le
      rw [Real.mul_rpow hUpper.le hr.le, ← mul_assoc] at hD
      exact hD.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hlo.le) hrg.le)
  have hCapNorm (u v : X) :
      (E.capacity {u} {v}).toReal / R = (ρ u v / r ^ γ) ^ (1 - p) := by
    rw [E.capacity_toReal_eq_pointResistanceLength_rpow,
      Real.div_rpow (E.pointResistanceLength_nonneg _ _) hrg.le, ← Real.rpow_mul hr.le]
    have hγe : γ * (1 - p) = d - β := by
      dsimp [γ]
      rw [show 1 - p = -(p - 1) by ring, mul_neg, div_mul_cancel₀ _ (sub_pos.mpr E.one_lt).ne']
      ring
    rw [hγe]
  have hRootNorm (u : E.CompactCore) :
      (E.energy u.domainElement : ℝ) ^ (-(p - 1)⁻¹) / r ^ γ =
        ((E.energy u.domainElement : ℝ) / R) ^ (-(p - 1)⁻¹) := by
    rw [Real.div_rpow (NNReal.coe_nonneg _) hR.le]
    dsimp [R]
    rw [← Real.rpow_mul hr.le]
    congr 2
    dsimp [γ]
    rw [div_eq_mul_inv]
    ring
  obtain ⟨g, hg, hg₁, hgU, hgE⟩ := hLarge y r hr
  have hTest (u : X) (hu : dist u y ∈ Icc (lower * r) (upper * r)) (huU : u ∈ U) :
      ∃ f : E.CompactCore, f.toFun u = 1 ∧ tsupport f.toFun ⊆ pathComponentIn U u ∧
        (E.energy f.domainElement : ℝ) ≤ (E.capacity {u} {y}).toReal + 2 * ε * R := by
    obtain ⟨q, hq, hq₁, hq₀, hqE⟩ := hSmall u y r hr hu.1
    let F := q.minAddConst g (a := 0) le_rfl
    have hF₁ : F.toFun u = 1 := by
      change min (q.toFun u) (g.toFun u + 0) = 1
      rw [add_zero, hq₁, hg₁ (mem_closedBall.mpr hu.2), min_self]
    have hfs : tsupport F.toFun ⊆ U := by
      let K := tsupport g.toFun ∩ (ball y (δ * r))ᶜ
      have hK : IsClosed K := isClosed_closure.inter isOpen_ball.isClosed_compl
      have hFK : support F.toFun ⊆ K := by
        intro x hx
        refine ⟨?_, ?_⟩
        · apply subset_closure
          by_contra h
          apply hx
          change min (q.toFun x) (g.toFun x + 0) = 0
          rw [notMem_support.mp h, add_zero, min_eq_right (hq x).1]
        · intro hxB
          apply hx
          change min (q.toFun x) (g.toFun x + 0) = 0
          rw [hq₀ (ball_subset_closedBall hxB), add_zero, min_eq_left (hg x).1]
      intro x hx
      have h := closure_minimal hFK hK hx
      refine ⟨hgU h.1, fun hx' ↦ h.2 (mem_ball.mpr ?_)⟩
      exact (mem_closedBall.mp hx').trans_lt (mul_lt_mul_of_pos_right had hr)
    obtain ⟨w, hw, hws, hwE⟩ := F.exists_core_restrict_pathComponentIn hU hfs u
    refine ⟨w, ?_, hws, ?_⟩
    · rw [hw, indicator_of_mem (mem_pathComponentIn_self huU), hF₁]
    · have hsum := congrArg NNReal.toReal (q.energy_sup_add_min g)
      simp only [NNReal.coe_add] at hsum
      have hlow : 0 ≤ (E.energy (q.sup g).domainElement : ℝ) := NNReal.coe_nonneg _
      have h := NNReal.coe_le_coe.mpr hwE
      linarith only [h, hsum, hlow, hqE, hgE]
  have hJoin : JoinedIn U x z := by
    by_contra hNo
    obtain ⟨f, hfx, hfs, hfE⟩ := hTest x hbal.1 hxU
    obtain ⟨g, hgz, hgs, hgE⟩ := hTest z hzy hzU
    have hDisj : Disjoint (support f.toFun) (support g.toFun) :=
      (disjoint_pathComponentIn_of_not_joinedIn hNo).mono
        (subset_closure.trans hfs) (subset_closure.trans hgs)
    have hSeries := E.pointResistanceLength_ge_series_of_disjoint_tests hvol hβ hPI hΓ hcap f g hfx hgz hDisj
    have hPosCap (u v : X) (h : 0 < dist u v) : 0 < (E.capacity {u} {v}).toReal := by
      rw [E.capacity_toReal_eq_pointResistanceLength_rpow]
      have hρ₀ := (mul_pos hc (Real.rpow_pos_of_pos h γ)).trans_le (hρ u v).1
      exact Real.rpow_pos_of_pos hρ₀ _
    have hfxz : f.toFun z = 0 :=
      notMem_support.mp (Set.disjoint_left.mp hDisj.symm (by rw [mem_support, hgz]; exact one_ne_zero))
    have hgx : g.toFun x = 0 :=
      notMem_support.mp (Set.disjoint_left.mp hDisj (by rw [mem_support, hfx]; exact one_ne_zero))
    have hPf : 0 < (E.energy f.domainElement : ℝ) := by
      have h := ENNReal.toReal_mono ENNReal.coe_ne_top
        (E.singleton_capacity_le_of_point_values f.ae_eq f.continuous hfx hfxz)
      rw [ENNReal.coe_toReal] at h
      exact (hPosCap x z ((mul_pos hLower hr).trans_le hbal.2.2.1)).trans_le h
    have hPg : 0 < (E.energy g.domainElement : ℝ) := by
      have h := ENNReal.toReal_mono ENNReal.coe_ne_top
        (E.singleton_capacity_le_of_point_values g.ae_eq g.continuous hgz hgx)
      rw [ENNReal.coe_toReal] at h
      exact (hPosCap z x (by rw [dist_comm]; exact (mul_pos hLower hr).trans_le hbal.2.2.1)).trans_le h
    let b := ρ x y / r ^ γ
    let s := ρ z y / r ^ γ
    have hb := hComp hbal.1
    have hs := hComp hzy
    have hEN (w : E.CompactCore) (u : X)
        (hw : (E.energy w.domainElement : ℝ) ≤ (E.capacity {u} {y}).toReal + 2 * ε * R) :
        (E.energy w.domainElement : ℝ) / R ≤ (ρ u y / r ^ γ) ^ (1 - p) + 2 * ε := by
      rw [← hCapNorm]
      exact (div_le_div_of_nonneg_right hw hR.le).trans_eq (by
        rw [add_div, mul_div_cancel_right₀ _ hR.ne'])
    have hF := (hLoss b hb)
    have hG := (hLoss s hs)
    have h₁ := Real.rpow_le_rpow_of_nonpos (div_pos hPf hR) (hEN f x hfE)
      (neg_nonpos.mpr (inv_nonneg.mpr (sub_pos.mpr E.one_lt).le))
    have h₂ := Real.rpow_le_rpow_of_nonpos (div_pos hPg hR) (hEN g z hgE)
      (neg_nonpos.mpr (inv_nonneg.mpr (sub_pos.mpr E.one_lt).le))
    rw [← hRootNorm] at h₁ h₂
    have hSeries' := div_le_div_of_nonneg_right hSeries hrg.le
    rw [add_div] at hSeries'
    have hsymm : ρ y z = ρ z y := by
      dsimp [ρ, pointResistanceLength, resistance]
      rw [E.singleton_capacity_comm hvol hβ hPI hΓ hcap y z]
    have hDef' : ξ ≤ b + s - ρ x z / r ^ γ := by
      simpa only [b, s, ← add_div, ← sub_div, ← hsymm, relativeDeficit, ρ] using hDef
    linarith only [hF, hG, h₁, h₂, hSeries', hDef']
  obtain ⟨θ, hθ⟩ := hJoin
  refine ⟨θ.extend, θ.continuous_extend.continuousOn, θ.extend_zero, θ.extend_one, ?_⟩
  intro t ht
  rw [θ.extend_apply ht]
  have h := hθ ⟨t, ht⟩
  exact ⟨(mem_ball.mp h.1).le, (lt_of_not_ge (fun h' ↦ h.2 (mem_closedBall.mpr h'))).le⟩

end WalkDimensions.PEnergy
