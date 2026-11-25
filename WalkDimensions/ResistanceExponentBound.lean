import WalkDimensions.DyadicMidpoints
import WalkDimensions.ResistanceMetric

/-!
# The resistance exponent is at most one

The resistance triangle inequality along the dyadic midpoint chain
rules out a superlinear resistance distance.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exponent_le_one_of_chain_distance_comparison
    {ρ : X → X → ℝ} {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C) (hCC : ChainCondition X)
    (htri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (hself : ∀ x, ρ x x = 0) (hbound : ∀ x y, ρ x y ≤ C * dist x y ^ γ)
    {x y : X} (hxy : 0 < ρ x y) : γ ≤ 1 := by
  by_contra! hγ₁
  obtain ⟨z, hz, _, hd⟩ := exists_intrinsic_dyadic_midpoint_chain hCC x y
  let s := intrinsicDistance x y
  have hs : 0 ≤ s := dist_nonneg.trans (dist_le_intrinsicDistance hCC x y)
  have hsum (n k : ℕ) : ρ (z n 0) (z n k) ≤ ∑ j ∈ Finset.range k, ρ (z n j) (z n (j + 1)) := by
    induction k with
    | zero => simp only [hself, Finset.range_zero, Finset.sum_empty, le_refl]
    | succ k ih =>
        rw [Finset.sum_range_succ]
        exact (htri _ _ _).trans (add_le_add_left ih _)
  have hPow (n : ℕ) :
      (2 : ℝ) ^ n * (s / (2 : ℝ) ^ n) ^ γ = s ^ γ * ((2 : ℝ) ^ (1 - γ)) ^ n := by
    have hbase : ((2 : ℝ) ^ n) ^ (-γ) = (2 : ℝ) ^ (-γ * (n : ℝ)) := by
      rw [mul_comm, Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.div_rpow hs (by positivity), div_eq_mul_inv, ← Real.rpow_neg (by positivity), hbase,
      mul_left_comm, ← Real.rpow_natCast (2 : ℝ) n,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  have hupper (n : ℕ) : ρ x y ≤ (C * s ^ γ) * ((2 : ℝ) ^ (1 - γ)) ^ n := by
    have hseq := hsum n (2 ^ n)
    rw [(hz n).1, (hz n).2] at hseq
    apply hseq.trans
    calc
      _ ≤ ∑ _ ∈ Finset.range (2 ^ n), C * (s / (2 : ℝ) ^ n) ^ γ := by
        apply Finset.sum_le_sum
        intro k hk
        have hb := dist_le_intrinsicDistance hCC (z n k) (z n (k + 1))
        rw [hd n k (Finset.mem_range.mp hk)] at hb
        exact (hbound _ _).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg hb hγ.le) hC.le)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
          mul_left_comm _ C, hPow, ← mul_assoc]
  have hbase : (2 : ℝ) ^ (1 - γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hγ₁)
  have hlimit := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hbase).const_mul (C * s ^ γ)
  have h := ge_of_tendsto hlimit (Eventually.of_forall hupper)
  exact hxy.not_ge (by simpa only [mul_zero] using h)

namespace PEnergy

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

theorem walkExponent_le_volume_add_of_supercritical {d β : ℝ} (hvol : AhlforsRegular μ d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hCC : ChainCondition X) {x y : X} (hxy : x ≠ y) : β ≤ d + p - 1 := by
  obtain ⟨c, C, hc, hC, hcomp⟩ := E.pointResistanceLength_comparable hvol hβ hPI hΓ hcap
  have hγ : 0 < (β - d) / (p - 1) := div_pos (sub_pos.mpr hβ) (sub_pos.mpr E.one_lt)
  have hpos : 0 < E.pointResistanceLength x y :=
    (mul_pos hc (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _)).trans_le (hcomp x y).1
  have h := exponent_le_one_of_chain_distance_comparison hγ hC hCC
    (E.pointResistanceLength_triangle hvol hβ hPI hΓ hcap) E.pointResistanceLength_self
    (fun u v ↦ (hcomp u v).2) hpos
  have h' := (div_le_iff₀ (sub_pos.mpr E.one_lt)).mp h
  linarith only [h']

end PEnergy
end WalkDimensions
