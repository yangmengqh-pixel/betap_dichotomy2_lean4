import WalkDimensions.DyadicMidpoints

/-!
# Geometric input for dyadic endpoint propagation

Balanced triples along exact midpoint chains give the normalized
increments in the resistance lengths.
-/

open Filter Set
open scoped Topology

namespace WalkDimensions

private theorem sum_pairs (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n), f k) =
      ∑ k ∈ Finset.range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

private theorem dyadic_scale_identity (s : ℝ) (hs : 0 < s) (γ : ℝ) (n : ℕ) :
    (s / (2 : ℝ) ^ n) ^ γ / s ^ γ * (2 : ℝ) ^ n = ((2 : ℝ) ^ (1 - γ)) ^ n := by
  have hpow : 0 < s ^ γ := Real.rpow_pos_of_pos hs _
  have hbase : ((2 : ℝ) ^ n) ^ (-γ) = (2 : ℝ) ^ (-γ * (n : ℝ)) := by
    rw [mul_comm, Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.div_rpow hs.le (by positivity)]
  calc
    _ = (2 : ℝ) ^ n * (((2 : ℝ) ^ n) ^ γ)⁻¹ := by
      field_simp
    _ = _ := by
      rw [← Real.rpow_neg (by positivity), hbase, ← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

variable {X : Type*}

def BalancedWithin (lower upper : ℝ) (D : X → X → ℝ) (x y z : X) (r : ℝ) : Prop :=
  D x y ∈ Icc (lower * r) (upper * r) ∧ D y z ∈ Icc (lower * r) (upper * r) ∧
    D x z ∈ Icc (lower * r) (upper * r)

def BalancedAt (D : X → X → ℝ) (x y z : X) (r : ℝ) : Prop :=
  D x y ∈ Icc (r / 2) (2 * r) ∧ D y z ∈ Icc (r / 2) (2 * r) ∧
    D x z ∈ Icc (r / 2) (2 * r)

noncomputable def relativeDeficit (ρ : X → X → ℝ) (γ : ℝ) (x y z : X) (r : ℝ) : ℝ :=
  (ρ x y + ρ y z - ρ x z) / r ^ γ

private noncomputable def dyadicLength (z : ℕ → ℕ → X) (ρ : X → X → ℝ)
    (s γ : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (2 ^ n), ρ (z n k) (z n (k + 1))) / s ^ γ

private noncomputable def dyadicRelativeDeficit (z : ℕ → ℕ → X) (ρ : X → X → ℝ)
    (s γ : ℝ) (n : ℕ) (k : Fin (2 ^ n)) : ℝ :=
  relativeDeficit ρ γ (z n k) (z (n + 1) (2 * (k : ℕ) + 1)) (z n ((k : ℕ) + 1))
    (s / (2 : ℝ) ^ n)

private theorem dyadicLength_step (z : ℕ → ℕ → X) (ρ : X → X → ℝ) {s : ℝ} (hs : 0 < s)
    (γ : ℝ) (hEven : ∀ n k, z (n + 1) (2 * k) = z n k) (n : ℕ) :
    dyadicLength z ρ s γ (n + 1) - dyadicLength z ρ s γ n =
      ((2 : ℝ) ^ (1 - γ)) ^ n * dyadicAverage (dyadicRelativeDeficit z ρ s γ) n := by
  let r := s / (2 : ℝ) ^ n
  have hr : 0 < r := by dsimp [r]; positivity
  have hsγ := (Real.rpow_pos_of_pos hs γ).ne'
  have hrγ := (Real.rpow_pos_of_pos hr γ).ne'
  let Δ (k : ℕ) := ρ (z n k) (z (n + 1) (2 * k + 1)) +
    ρ (z (n + 1) (2 * k + 1)) (z n (k + 1)) - ρ (z n k) (z n (k + 1))
  have hpair :
      (∑ k ∈ Finset.range (2 ^ (n + 1)), ρ (z (n + 1) k) (z (n + 1) (k + 1))) =
        ∑ k ∈ Finset.range (2 ^ n),
          (ρ (z n k) (z (n + 1) (2 * k + 1)) + ρ (z (n + 1) (2 * k + 1)) (z n (k + 1))) := by
    rw [show (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ, mul_comm], sum_pairs]
    apply Finset.sum_congr rfl
    intro k _
    rw [hEven, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, hEven]
  have hrel : dyadicAverage (dyadicRelativeDeficit z ρ s γ) n =
      ((∑ k ∈ Finset.range (2 ^ n), Δ k) / r ^ γ) / (2 : ℝ) ^ n := by
    unfold dyadicAverage dyadicRelativeDeficit relativeDeficit
    change (∑ k : Fin (2 ^ n), (fun j : ℕ ↦ Δ j / r ^ γ) k.val) / (2 : ℝ) ^ n = _
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ Δ j / r ^ γ)]
    simp only [Finset.sum_div]
  unfold dyadicLength
  rw [hpair, ← sub_div, ← Finset.sum_sub_distrib, hrel]
  change (∑ k ∈ Finset.range (2 ^ n), Δ k) / s ^ γ = _
  rw [← dyadic_scale_identity s hs γ n]
  change _ = (r ^ γ / s ^ γ * (2 : ℝ) ^ n) *
    ((∑ k ∈ Finset.range (2 ^ n), Δ k) / r ^ γ / (2 : ℝ) ^ n)
  field_simp

theorem gamma_eq_one_of_balanced_deficit_transfer
    {D ρ₁ ρ₂ : X → X → ℝ} {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1)
    {C₁ C₂ c : ℝ} (hC₂ : 0 < C₂) (hc : 0 < c)
    (hupper₁ : ∀ x y, ρ₁ x y ≤ C₁ * D x y)
    (hlower₂ : ∀ x y, c * D x y ^ γ ≤ ρ₂ x y)
    (hupper₂ : ∀ x y, ρ₂ x y ≤ C₂ * D x y ^ γ)
    (htriangle₁ : ∀ x y z, ρ₁ x z ≤ ρ₁ x y + ρ₁ y z)
    (htriangle₂ : ∀ x y z, ρ₂ x z ≤ ρ₂ x y + ρ₂ y z)
    (htransfer : ∀ ε > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ x y z r, 0 < r →
      BalancedAt D x y z r → relativeDeficit ρ₁ 1 x y z r < κ →
      relativeDeficit ρ₂ γ x y z r < ε)
    (hmid : ∀ x y : X, ∃ z : X, D x z = D x y / 2 ∧ D z y = D x y / 2)
    (x y : X) (hs : 0 < D x y) : γ = 1 := by
  obtain ⟨z, _, hEven, hdist⟩ := exists_dyadic_midpoint_chain hmid x y
  let s := D x y
  let r (n : ℕ) := s / (2 : ℝ) ^ n
  have hr (n : ℕ) : 0 < r n := div_pos hs (by positivity)
  let P := dyadicRelativeDeficit z ρ₁ s 1
  let Q := dyadicRelativeDeficit z ρ₂ s γ
  have hparents (n : ℕ) (k : Fin (2 ^ n)) :
      D (z n k) (z n ((k : ℕ) + 1)) = r n := hdist n k k.isLt
  have hchildren (n : ℕ) (k : Fin (2 ^ n)) :
      D (z n k) (z (n + 1) (2 * (k : ℕ) + 1)) = r n / 2 ∧
      D (z (n + 1) (2 * (k : ℕ) + 1)) (z n ((k : ℕ) + 1)) = r n / 2 := by
    have he : r (n + 1) = r n / 2 := by dsimp [r]; rw [pow_succ, div_div]
    have hnum : 2 * (k : ℕ) + 1 < (2 : ℕ) ^ (n + 1) := by
      rw [pow_succ]
      have hk := k.isLt
      omega
    constructor
    · rw [← hEven n (k : ℕ)]
      exact (hdist (n + 1) _ (by omega)).trans he
    · rw [← hEven n ((k : ℕ) + 1), ← show 2 * (k : ℕ) + 1 + 1 = 2 * ((k : ℕ) + 1) by omega]
      exact (hdist (n + 1) _ hnum).trans he
  have hP (n) (k) : 0 ≤ P n k := by
    unfold P dyadicRelativeDeficit relativeDeficit
    exact div_nonneg (sub_nonneg.mpr (htriangle₁ _ _ _)) (Real.rpow_nonneg (hr n).le _)
  have hQ (n) (k) : 0 ≤ Q n k := by
    unfold Q dyadicRelativeDeficit relativeDeficit
    exact div_nonneg (sub_nonneg.mpr (htriangle₂ _ _ _)) (Real.rpow_nonneg (hr n).le _)
  have hQbound (n) (k) : Q n k ≤ 2 * C₂ := by
    obtain ⟨h₁, h₂⟩ := hchildren n k
    have hupperL := (hupper₂ (z n k) (z (n + 1) (2 * (k : ℕ) + 1)))
    have hupperR := (hupper₂ (z (n + 1) (2 * (k : ℕ) + 1)) (z n ((k : ℕ) + 1)))
    rw [h₁] at hupperL
    rw [h₂] at hupperR
    have hcap := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (show r n / 2 ≤ r n by linarith only [hr n]) hγ.le) hC₂.le
    have hlo := hlower₂ (z n k) (z n ((k : ℕ) + 1))
    rw [hparents] at hlo
    have hzero : 0 ≤ ρ₂ (z n k) (z n ((k : ℕ) + 1)) := (by positivity : 0 ≤ c * r n ^ γ).trans hlo
    change _ / r n ^ γ ≤ _
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (hr n) _)).mpr
    linarith only [hupperL, hupperR, hcap, hzero]
  have htransfer' : ∀ ε > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ n k, P n k < κ → Q n k < ε := by
    intro ε hε
    obtain ⟨κ, hκ, ht⟩ := htransfer ε hε
    refine ⟨κ, hκ, fun n k hk ↦ ht _ _ _ (r n) (hr n) ?_ hk⟩
    obtain ⟨h₁, h₂⟩ := hchildren n k
    unfold BalancedAt
    rw [h₁, h₂, hparents]
    refine ⟨⟨le_rfl, ?_⟩, ⟨le_rfl, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith only [hr n]
  have hstep₁ (n) : dyadicLength z ρ₁ s 1 (n + 1) - dyadicLength z ρ₁ s 1 n = dyadicAverage P n := by
    simpa only [sub_self, Real.rpow_zero, one_pow, one_mul] using dyadicLength_step z ρ₁ hs 1 hEven n
  have hbound₁ (n) : dyadicLength z ρ₁ s 1 n ≤ C₁ := by
    unfold dyadicLength
    rw [Real.rpow_one]
    apply (div_le_iff₀ hs).mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range (2 ^ n), C₁ * r n := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hupper₁ _ _).trans_eq (by rw [hdist n k (Finset.mem_range.mp hk)])
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        dsimp [r]
        dsimp [s]
        field_simp
  have hlower (n) : c * ((2 : ℝ) ^ (1 - γ)) ^ n ≤ dyadicLength z ρ₂ s γ n := by
    unfold dyadicLength
    calc
      _ = (∑ _ ∈ Finset.range (2 ^ n), c * r n ^ γ) / s ^ γ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
          ← dyadic_scale_identity s hs γ n]
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
        apply Finset.sum_le_sum
        intro k hk
        have h := hlower₂ (z n k) (z n (k + 1))
        rwa [hdist n k (Finset.mem_range.mp hk)] at h
  have hmono : Monotone (dyadicLength z ρ₁ s 1) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [← sub_nonneg, hstep₁]
    exact div_nonneg (Finset.sum_nonneg fun k _ ↦ hP n k) (by positivity)
  exact gamma_eq_one_of_dyadic_deficit_transfer hγ₁ hc hmono
    ⟨C₁, forall_mem_range.mpr hbound₁⟩ hstep₁ hlower (dyadicLength_step z ρ₂ hs γ hEven)
    (mul_pos zero_lt_two hC₂) hP hQ hQbound htransfer'

end WalkDimensions
