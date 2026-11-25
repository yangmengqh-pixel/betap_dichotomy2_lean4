import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# A dyadic growth obstruction

The final growth argument in Section 6 of arXiv:2611.02422v1.
A sequence with a geometric lower bound cannot have increments that are
little-o of the same geometric scale.
-/

open Filter
open scoped Topology BigOperators

namespace WalkDimensions

theorem growth_base_le_one_of_normalized_increment_tendsto_zero
    {a c : ℝ} (hc : 0 < c) {L M : ℕ → ℝ}
    (hlower : ∀ n, c * a ^ n ≤ L n)
    (hstep : ∀ n, L (n + 1) - L n = a ^ n * M n)
    (hM : Tendsto M atTop (𝓝 0)) : a ≤ 1 := by
  by_contra! ha
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have ha₁ : 0 < a - 1 := sub_pos.mpr ha
  have hε : 0 < (c / 2) * (a - 1) := mul_pos (half_pos hc) ha₁
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hM).2 _ hε)
  have hdiff (n : ℕ) (hn : N ≤ n) :
      L (n + 1) - L n ≤ (c / 2) * a ^ (n + 1) - (c / 2) * a ^ n := by
    rw [hstep, pow_succ]
    calc
      a ^ n * M n ≤ a ^ n * ((c / 2) * (a - 1)) :=
        mul_le_mul_of_nonneg_left (hN n hn).le (pow_nonneg ha₀.le _)
      _ = _ := by ring
  have hupper (k : ℕ) : L (N + k) ≤ L N + (c / 2) * a ^ (N + k) := by
    induction k with
    | zero =>
      simp only [Nat.add_zero]
      exact le_add_of_nonneg_right (mul_nonneg (half_pos hc).le (pow_nonneg ha₀.le _))
    | succ k ih =>
      have h := hdiff (N + k) (Nat.le_add_right _ _)
      change L (N + k + 1) ≤ L N + (c / 2) * a ^ (N + k + 1)
      linarith only [ih, h]
  have hbound : ∀ k : ℕ, (c / 2) * a ^ (N + k) ≤ L N := by
    intro k
    linarith only [hlower (N + k), hupper k]
  have hgrowth : Tendsto (fun k : ℕ ↦ (c / 2) * a ^ (N + k)) atTop atTop := by
    have hshift : Tendsto (fun k : ℕ ↦ N + k) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ Nat.le_add_left k N) tendsto_id
    exact Tendsto.const_mul_atTop (half_pos hc)
      ((tendsto_pow_atTop_atTop_of_one_lt ha).comp hshift)
  obtain ⟨k, hk⟩ := (hgrowth.eventually_gt_atTop (L N)).exists
  exact (not_lt_of_ge (hbound k)) hk

/-- The conclusion of the dyadic length argument once the transferred
average deficits tend to zero and the resistance lengths satisfy (6.1). -/
theorem gamma_eq_one_of_dyadic_growth {γ c : ℝ} (hγ : γ ≤ 1) (hc : 0 < c)
    {L M : ℕ → ℝ}
    (hlower : ∀ n, c * ((2 : ℝ) ^ (1 - γ)) ^ n ≤ L n)
    (hstep : ∀ n, L (n + 1) - L n = ((2 : ℝ) ^ (1 - γ)) ^ n * M n)
    (hM : Tendsto M atTop (𝓝 0)) : γ = 1 := by
  have hbase := growth_base_le_one_of_normalized_increment_tendsto_zero hc hlower hstep hM
  apply le_antisymm hγ
  by_contra! hlt
  exact (not_lt_of_ge hbase) (Real.one_lt_rpow (by norm_num) (sub_pos.mpr hlt))

/-- The average normalized deficit at the (n)-th dyadic level. -/
noncomputable def dyadicAverage (D : (n : ℕ) → Fin (2 ^ n) → ℝ) (n : ℕ) : ℝ :=
  (∑ k, D n k) / (2 : ℝ) ^ n

/-- The quantitative transfer of deficits gives convergence of the second
average once the first average converges. -/
theorem dyadicAverage_tendsto_zero_of_transfer
    {P Q : (n : ℕ) → Fin (2 ^ n) → ℝ} {C : ℝ} (hC : 0 < C)
    (hP : ∀ n k, 0 ≤ P n k) (hQ : ∀ n k, 0 ≤ Q n k)
    (hQbound : ∀ n k, Q n k ≤ C)
    (htransfer : ∀ ε > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ n k, P n k < κ → Q n k < ε)
    (hPzero : Tendsto (dyadicAverage P) atTop (𝓝 0)) :
    Tendsto (dyadicAverage Q) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b hb ↦ Eventually.of_forall (fun n ↦ ?_), fun b hb ↦ ?_⟩
  · exact hb.trans_le (div_nonneg (Finset.sum_nonneg fun i _ ↦ hQ n i) (by positivity))
  obtain ⟨κ, hκ, hκQ⟩ := htransfer (b / 2) (half_pos hb)
  have hpos : 0 < b / 2 / (C / κ) := div_pos (half_pos hb) (div_pos hC hκ)
  filter_upwards [(tendsto_order.1 hPzero).2 _ hpos] with n hn
  have hpoint (k : Fin (2 ^ n)) : Q n k ≤ b / 2 + (C / κ) * P n k := by
    by_cases hk : P n k < κ
    · exact (hκQ n k hk).le.trans (le_add_of_nonneg_right
        (mul_nonneg (div_pos hC hκ).le (hP n k)))
    · have h := mul_le_mul_of_nonneg_left (le_of_not_gt hk) (div_pos hC hκ).le
      rw [div_mul_cancel₀ _ hκ.ne'] at h
      exact (hQbound n k).trans (h.trans (le_add_of_nonneg_left (half_pos hb).le))
  have hsum : (∑ k, Q n k) ≤ b / 2 * (2 : ℝ) ^ n + (C / κ) * (∑ k, P n k) := by
    calc
      _ ≤ ∑ k : Fin (2 ^ n), (b / 2 + (C / κ) * P n k) :=
        Finset.sum_le_sum fun k _ ↦ hpoint k
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm ((2 : ℝ) ^ n)]
  have hdiv : dyadicAverage Q n ≤ b / 2 + (C / κ) * dyadicAverage P n := by
    unfold dyadicAverage
    apply (div_le_iff₀ (by positivity)).2
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ n ≠ 0)]
    exact hsum
  have htail := (lt_div_iff₀ (div_pos hC hκ)).1 hn
  linarith only [hdiv, htail]

/-- The scalar part of the endpoint propagation proof in Section 6. The
geometric resistance comparison and the deficit-transfer theorem supply
the bounds and the transfer modulus. -/
theorem gamma_eq_one_of_dyadic_deficit_transfer {γ c : ℝ} (hγ : γ ≤ 1) (hc : 0 < c)
    {L₁ L₂ : ℕ → ℝ} {P Q : (n : ℕ) → Fin (2 ^ n) → ℝ}
    (hmono : Monotone L₁) (hbounded : BddAbove (Set.range L₁))
    (hstep₁ : ∀ n, L₁ (n + 1) - L₁ n = dyadicAverage P n)
    (hlower : ∀ n, c * ((2 : ℝ) ^ (1 - γ)) ^ n ≤ L₂ n)
    (hstep₂ : ∀ n, L₂ (n + 1) - L₂ n = ((2 : ℝ) ^ (1 - γ)) ^ n * dyadicAverage Q n)
    {C : ℝ} (hC : 0 < C) (hP : ∀ n k, 0 ≤ P n k) (hQ : ∀ n k, 0 ≤ Q n k)
    (hQbound : ∀ n k, Q n k ≤ C)
    (htransfer : ∀ ε > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ n k, P n k < κ → Q n k < ε) :
    γ = 1 := by
  have hL := tendsto_atTop_ciSup hmono hbounded
  have hPzero : Tendsto (dyadicAverage P) atTop (𝓝 0) := by
    have hdiff : Tendsto (fun n ↦ L₁ (n + 1) - L₁ n) atTop (𝓝 0) := by
      simpa only [sub_self, Function.comp_apply] using
        (hL.comp (tendsto_add_atTop_nat 1)).sub hL
    convert hdiff using 1
    exact funext fun n ↦ (hstep₁ n).symm
  exact gamma_eq_one_of_dyadic_growth hγ hc hlower hstep₂
    (dyadicAverage_tendsto_zero_of_transfer hC hP hQ hQbound htransfer hPzero)

end WalkDimensions
