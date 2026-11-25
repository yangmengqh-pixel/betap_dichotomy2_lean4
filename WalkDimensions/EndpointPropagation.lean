import WalkDimensions.DeficitDetour
import WalkDimensions.ResistanceExponentBound

/-!
# Propagation of the upper endpoint in the positive Morrey range

The detour estimates transfer small balanced-triple deficits. Intrinsic
midpoint chains turn the transferred deficits into endpoint equality.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure]

theorem exists_balanced_deficit_transfer {d p q βp βq : ℝ}
    (hvol : AhlforsRegular μ d) (hCC : ChainCondition X)
    (Ep : PEnergy μ p) (Eq : PEnergy μ q) (hp : βp - d = p - 1) (hq : d < βq)
    {Γp : Ep.domain → Measure X} {Γq : Eq.domain → Measure X}
    (hPIp : Ep.Poincare Γp βp) (hPIq : Eq.Poincare Γq βq)
    (hΓp : ∀ f, Γp f univ = (Ep.energy f : ℝ≥0∞))
    (hΓq : ∀ f, Γq f univ = (Eq.energy f : ℝ≥0∞))
    (hcapP : Ep.CapacityUpperBound βp) (hcapQ : Eq.CapacityUpperBound βq)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) {lower upper : ℝ}
    (hLower : 0 < lower) (hUpper : 0 < upper) :
    ∀ ξ > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ (x y z : X) (r : ℝ), 0 < r →
      BalancedWithin lower upper dist x y z r →
      relativeDeficit Ep.pointResistanceLength 1 x y z r < κ →
      relativeDeficit Eq.pointResistanceLength ((βq - d) / (q - 1)) x y z r < ξ := by
  intro ξ hξ
  obtain ⟨L, a, hL, ha, hDetour⟩ :=
    Eq.exists_detour_of_positive_deficit hvol hq hPIq hΓq hcapQ hCC hLower hUpper hξ
  obtain ⟨κ, hκ, hLowerDeficit⟩ :=
    Ep.exists_positive_deficit_of_detour hvol hp hPIp hΓp hcapP hunbounded hL.le ha hLower hUpper
  refine ⟨κ, hκ, fun x y z r hr hbal hpDef ↦ ?_⟩
  by_contra! hqDef
  have h := hLowerDeficit x y z r hr hbal (hDetour x y z r hr hbal hqDef)
  exact hpDef.not_ge h

theorem upperEndpoint_eq_of_supercritical [Nonempty X] {d p q βp βq : ℝ}
    (hvol : AhlforsRegular μ d) (hCC : ChainCondition X)
    (Ep : PEnergy μ p) (Eq : PEnergy μ q) (hp : βp - d = p - 1) (hq : d < βq)
    {Γp : Ep.domain → Measure X} {Γq : Eq.domain → Measure X}
    (hPIp : Ep.Poincare Γp βp) (hPIq : Eq.Poincare Γq βq)
    (hΓp : ∀ f, Γp f univ = (Ep.energy f : ℝ≥0∞))
    (hΓq : ∀ f, Γq f univ = (Eq.energy f : ℝ≥0∞))
    (hcapP : Ep.CapacityUpperBound βp) (hcapQ : Eq.CapacityUpperBound βq)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    βq - d = q - 1 := by
  have hp' : d < βp := sub_pos.mp (hp ▸ sub_pos.mpr Ep.one_lt)
  let γ := (βq - d) / (q - 1)
  have hγ : 0 < γ := div_pos (sub_pos.mpr hq) (sub_pos.mpr Eq.one_lt)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ closedBall x 1 := by
    by_contra! h
    exact hunbounded ((isCompact_closedBall x 1).isBounded.subset fun y _ ↦ h y)
  have hxy : x ≠ y := by
    intro h
    exact hy (h ▸ mem_closedBall_self (by norm_num))
  have hqmax := Eq.walkExponent_le_volume_add_of_supercritical hvol hq hPIq hΓq hcapQ hCC hxy
  have hγ₁ : γ ≤ 1 := (div_le_iff₀ (sub_pos.mpr Eq.one_lt)).mpr (by linarith only [hqmax])
  obtain ⟨_, CP, _, hCP, hP⟩ := Ep.pointResistanceLength_comparable hvol hp' hPIp hΓp hcapP
  obtain ⟨cQ, CQ, hcQ, hCQ, hQ⟩ := Eq.pointResistanceLength_comparable hvol hq hPIq hΓq hcapQ
  obtain ⟨A, hA, hD⟩ := hCC.exists_intrinsicDistance_le
  let D := intrinsicDistance (X := X)
  let c := cQ / A ^ γ
  have hc : 0 < c := div_pos hcQ (Real.rpow_pos_of_pos hA _)
  have hP' (u v : X) : Ep.pointResistanceLength u v ≤ CP * D u v := by
    have h := (hP u v).2
    rw [hp, div_self (sub_pos.mpr Ep.one_lt).ne', Real.rpow_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (dist_le_intrinsicDistance hCC _ _) hCP.le)
  have hQUpper (u v : X) : Eq.pointResistanceLength u v ≤ CQ * D u v ^ γ :=
    (hQ u v).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (dist_le_intrinsicDistance hCC _ _) hγ.le) hCQ.le)
  have hQLower (u v : X) : c * D u v ^ γ ≤ Eq.pointResistanceLength u v := by
    have hlo : D u v / A ≤ dist u v := (div_le_iff₀ hA).mpr (by rw [mul_comm]; exact hD u v)
    apply le_trans _ (hQ u v).1
    calc
      _ = cQ * (D u v / A) ^ γ := by
        rw [Real.div_rpow (dist_nonneg.trans (dist_le_intrinsicDistance hCC _ _)) hA.le]
        dsimp [c]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (div_nonneg (dist_nonneg.trans (dist_le_intrinsicDistance hCC _ _)) hA.le) hlo hγ.le) hcQ.le
  let lower := 1 / (2 * A)
  have hLower : 0 < lower := by dsimp [lower]; positivity
  have hTransfer := exists_balanced_deficit_transfer hvol hCC Ep Eq hp hq hPIp hPIq hΓp hΓq
    hcapP hcapQ hunbounded hLower (show (0 : ℝ) < 2 by norm_num)
  have hTransferred : ∀ ξ > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ (u v w : X) (r : ℝ), 0 < r →
      BalancedAt D u v w r →
      relativeDeficit Ep.pointResistanceLength 1 u v w r < κ →
      relativeDeficit Eq.pointResistanceLength γ u v w r < ξ := by
    intro ξ hξ
    obtain ⟨κ, hκ, ht⟩ := hTransfer ξ hξ
    refine ⟨κ, hκ, fun u v w r hr hD3 hDef ↦ ht u v w r hr ?_ hDef⟩
    have hPair (a b : X) (h : D a b ∈ Icc (r / 2) (2 * r)) :
        dist a b ∈ Icc (lower * r) (2 * r) := by
      refine ⟨?_, (dist_le_intrinsicDistance hCC _ _).trans h.2⟩
      have he : lower * r = (r / 2) / A := by dsimp [lower]; rw [div_div]; ring
      rw [he, div_le_iff₀ hA, mul_comm]
      exact h.1.trans (hD a b)
    exact ⟨hPair _ _ hD3.1, hPair _ _ hD3.2.1, hPair _ _ hD3.2.2⟩
  have hγeq := gamma_eq_one_of_balanced_deficit_transfer hγ hγ₁ hCQ hc
    hP' hQLower hQUpper
    (Ep.pointResistanceLength_triangle hvol hp' hPIp hΓp hcapP)
    (Eq.pointResistanceLength_triangle hvol hq hPIq hΓq hcapQ)
    hTransferred (exists_intrinsicDistance_midpoint hCC) x y
    ((dist_pos.mpr hxy).trans_le (dist_le_intrinsicDistance hCC x y))
  exact (div_eq_iff (sub_pos.mpr Eq.one_lt).ne').mp hγeq |>.trans (one_mul _)

end WalkDimensions
