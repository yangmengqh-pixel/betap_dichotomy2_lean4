import WalkDimensions.ConnectedChains
import WalkDimensions.PathTail
import WalkDimensions.PointPropagation
import WalkDimensions.PointResistance

/-!
# A positive value at the end of a detour

A near-minimizing point potential is positive near its unit plate.
Uniform propagation along a compact path tail gives a lower bound at
the other end of a detour avoiding the zero plate.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
  [μ.IsOpenPosMeasure] {p : ℝ} (E : PEnergy μ p)

theorem exists_point_potential_lower_bound_along_detour {d β : ℝ}
    (hvol : AhlforsRegular μ d) (hβ : d < β) {Γ : E.domain → Measure X}
    (hPI : E.Poincare Γ β) (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞))
    (hcap : E.CapacityUpperBound β) (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    {L a lower : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (hLower : 0 < lower) :
    ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
      ∀ (r : ℝ), 0 < r → ∀ (x y z : X), lower * r ≤ dist x y → lower * r ≤ dist z x →
      ∀ φ : ℝ → X, ContinuousOn φ (Icc 0 1) → φ 0 = x → φ 1 = z →
        (∀ t ∈ Icc (0 : ℝ) 1, dist (φ t) y ≤ L * r ∧ a * r ≤ dist (φ t) y) →
      ∀ f : E.CompactCore, (∀ t, f.toFun t ∈ Icc (0 : ℝ) 1) → f.toFun x = 1 → f.toFun y = 0 →
        (E.energy f.domainElement : ℝ) - (E.capacity {x} {y}).toReal ≤ κ * r ^ (d - β) →
        c ≤ f.toFun z := by
  obtain ⟨_, U, _, hU, hCaps⟩ := E.singleton_capacity_bounds hvol hβ hPI hΓ hcap
  obtain ⟨H, hH, hHolder⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  obtain ⟨A, b, hA, hb, hPropagation⟩ := E.exists_point_propagation hvol hβ hPI hΓ hcap hunbounded
  have hp := zero_lt_one.trans E.one_lt
  let e := (β - d) / p
  have he : 0 < e := div_pos (sub_pos.mpr hβ) hp
  let C := U * lower ^ (d - β) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let T := H * C ^ p⁻¹
  have hT : 0 < T := mul_pos hH (Real.rpow_pos_of_pos hC _)
  let σ := (1 / (2 * T)) ^ e⁻¹
  have hσ : 0 < σ := Real.rpow_pos_of_pos (by positivity) _
  have hTσ : T * σ ^ e = 1 / 2 := by
    dsimp [σ]
    rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ he.ne', Real.rpow_one]
    field_simp [hT.ne']
  let ell := min σ (lower / 2)
  have hell : 0 < ell := lt_min hσ (half_pos hLower)
  let ν := min ell a / (2 * A)
  have hA₀ : 0 < A := zero_lt_one.trans hA
  have hν : 0 < ν := div_pos (lt_min hell ha) (by positivity)
  have hAν : A * ν = min ell a / 2 := by dsimp [ν]; field_simp
  have hellA : A * ν < ell := by
    rw [hAν]
    exact (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans_lt (half_lt_self hell)
  have haA : A * ν < a := by
    rw [hAν]
    exact (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  obtain ⟨N, hChain⟩ := hvol.volumeDoubling.exists_short_chain_in_compact_connected_set hL (mul_pos hb hν)
  let ε := (1 / 2 : ℝ) ^ (N + 3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ, hδ, hprop⟩ := hPropagation ε hε
  let κ := min 1 (δ * ν ^ (d - β))
  have hκ : 0 < κ := lt_min zero_lt_one (mul_pos hδ (Real.rpow_pos_of_pos hν _))
  let c := (1 / 2 : ℝ) ^ (N + 2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨κ, c, hκ, hc, fun r hr x y z hxy hzx φ hφ hφx hφz hAvoid f hf hfx hfy hDef ↦ ?_⟩
  have hxy₀ : 0 < dist x y := (mul_pos hLower hr).trans_le hxy
  have hcapReal : (E.capacity {x} {y}).toReal ≤ U * lower ^ (d - β) * r ^ (d - β) := by
    have hupper := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hCaps x y (dist_pos.mp hxy₀)).2
    rw [ENNReal.toReal_ofReal (by positivity)] at hupper
    apply hupper.trans
    rw [mul_assoc, ← Real.mul_rpow hLower.le hr.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos hLower hr) hxy
      (sub_nonpos.mpr hβ.le)) hU.le
  have hE : (E.energy f.domainElement : ℝ) ≤ C * r ^ (d - β) := by
    have hκ₁ := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) (δ * ν ^ (d - β)))
      (Real.rpow_nonneg hr.le (d - β))
    dsimp [C]
    nlinarith only [hκ₁, hDef, hcapReal]
  have hroot : E.rootSeminorm f.domainElement ≤ C ^ p⁻¹ * r ^ (-e) := by
    rw [E.rootSeminorm_apply]
    have h := Real.rpow_le_rpow (NNReal.coe_nonneg _) hE (inv_nonneg.mpr hp.le)
    rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hr.le] at h
    have heq : (d - β) * p⁻¹ = -e := by dsimp [e]; rw [div_eq_mul_inv]; ring
    rwa [heq] at h
  obtain ⟨v, hv, hfv, hholder⟩ := hHolder f.domainElement
  have hfEq := Measure.eq_of_ae_eq (hfv.symm.trans f.ae_eq) hv f.continuous
  have hinit (w : X) (hw : dist w x ≤ ell * r) : (1 / 2 : ℝ) ≤ f.toFun w := by
    have hwi := hholder x w
    rw [hfEq, hfx, dist_comm x w] at hwi
    have hdist : dist w x ^ e ≤ (σ * r) ^ e :=
      Real.rpow_le_rpow dist_nonneg
        (hw.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)) he.le
    have hdiff : |1 - f.toFun w| ≤ 1 / 2 := hwi.trans (by
      calc
        _ ≤ H * (C ^ p⁻¹ * r ^ (-e)) * (σ * r) ^ e :=
          mul_le_mul (mul_le_mul_of_nonneg_left hroot hH.le) hdist (by positivity) (by positivity)
        _ = _ := by
          rw [Real.mul_rpow hσ.le hr.le]
          calc
            _ = (T * σ ^ e) * (r ^ (-e) * r ^ e) := by dsimp [T]; ring
            _ = _ := by rw [hTσ, ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, mul_one])
    linarith only [le_abs_self (1 - f.toFun w), hdiff]
  have hzfar : ell * r < dist z x := by
    have h := mul_le_mul_of_nonneg_right (min_le_right σ (lower / 2)) hr.le
    linarith only [h, hzx, mul_pos hLower hr]
  obtain ⟨K, hK, hKconn, hKsub, hzK, hKx, w, hwK, hwx⟩ :=
    exists_compact_connected_path_tail hφ hφx hφz (mul_pos hell hr) hzfar
  have hKy (v : X) (hv : v ∈ K) : dist v y ≤ L * r ∧ a * r ≤ dist v y := by
    obtain ⟨t, ht, rfl⟩ := hKsub hv
    exact hAvoid t ht
  obtain ⟨n, s, hn, hs₀, hsn, hsK, hsStep⟩ :=
    hChain y r hr hK hKconn (fun v hv ↦ mem_closedBall.mpr (hKy v hv).1) w hwK z hzK
  have hDef' : (E.energy f.domainElement : ℝ) - (E.capacity {x} {y}).toReal ≤
      δ * (ν * r) ^ (d - β) := by
    apply hDef.trans
    rw [Real.mul_rpow hν.le hr.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hr.le (d - β))
  have hValues (k : ℕ) (hk : k ≤ n) :
      (1 / 2 : ℝ) ^ (k + 1) - 2 * ε ≤ f.toFun (s k) := by
    induction k with
    | zero =>
        rw [hs₀, pow_one]
        exact (sub_le_self _ (by positivity)).trans (hinit w hwx.le)
    | succ k ih =>
        have hk' : k < n := hk
        have hstepX : A * (ν * r) < dist x (s k) := by
          rw [← mul_assoc, dist_comm x]
          exact (mul_lt_mul_of_pos_right hellA hr).trans_le (hKx _ (hsK k hk'.le))
        have hstepY : A * (ν * r) < dist y (s k) := by
          rw [← mul_assoc, dist_comm y]
          exact (mul_lt_mul_of_pos_right haA hr).trans_le (hKy _ (hsK k hk'.le)).2
        have hstep : dist (s (k + 1)) (s k) ≤ b * (ν * r) := by
          rw [dist_comm, ← mul_assoc]
          exact hsStep k hk'
        have he := hprop f x y (s k) (s (k + 1)) (ν * r) (mul_pos hν hr)
          hf hfx hfy hstepX hstepY hstep hDef'
        have hPrev := ih hk'.le
        rw [pow_succ]
        linarith only [he, hPrev]
  have hnPow : (1 / 2 : ℝ) ^ (N + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_succ hn)
  have hResult := hValues n le_rfl
  rw [hsn] at hResult
  have heq : (1 / 2 : ℝ) ^ (N + 1) - 2 * ε = c := by
    dsimp [ε, c]
    rw [show N + 3 = (N + 2) + 1 by omega, show N + 2 = (N + 1) + 1 by omega, pow_succ, pow_succ]
    ring
  linarith only [hResult, hnPow, heq]

end WalkDimensions.PEnergy
