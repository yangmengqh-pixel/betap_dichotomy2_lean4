import WalkDimensions.CutoffDensityBounds
import WalkDimensions.FiniteCutoffCover

/-!
# Finite cutoff partitions subordinate to minimizing cutoffs
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

omit [SecondCountableTopology X] in
theorem exists_finite_potential_cutoff_partition {c d β A C H : ℝ}
    (hA : 1 < A) (hC : 0 < C) (hH : 0 < H) (hScale : β - d = (p - 1) * c)
    (hvol : VolumeDoubling m) (hcut : ∀ (x : X) (r : ℝ), 0 < r →
      ∃ f : E.CompactCore, E.UnitPlate (ball x r) (closedBall x (A * r)) f.domainElement f.toFun ∧
        (E.energy f.domainElement : ℝ) ≤ C * r ^ (d - β) ∧
        E.energyMeasure f.domainElement ≤ ENNReal.ofReal (C * H * r ^ (-p * c)) • μH[c])
    (u : E.CompactCore) {W : Set X} {K : ℝ≥0∞} (hKT : K ≠ ∞)
    (hDensity : ∀ S ⊆ W, μH[c] S ≤ K * E.energyMeasure u.domainElement S) :
    ∃ (L : ℝ) (M : ℕ), 0 < L ∧ 0 < M ∧ ∀ τ > (0 : ℝ), ∃ N : ℕ, 0 < N ∧
      ∀ (x : X) (r : ℝ), 0 < r → ∃ (n : ℕ) (z : Fin n → X) (φ : Fin n → E.CompactCore),
        n ≤ N ∧ (∀ i, z i ∈ closedBall x (A * r)) ∧
        (∀ i y, (φ i).toFun y ∈ Icc (0 : ℝ) 1) ∧
        (∀ i, tsupport (φ i).toFun ⊆ closedBall (z i) (A * (τ * r))) ∧
        (∀ y ∈ closedBall x (A * r), ∑ i, (φ i).toFun y = 1) ∧
        (∀ S : Set X, MeasurableSet S →
          (∑ i, E.energyMeasure u.domainElement (S ∩ closedBall (z i) (A * (τ * r)))) ≤
            (M : ℝ≥0∞) * E.energyMeasure u.domainElement S) ∧
        (∀ i, E.rootSeminorm (φ i).domainElement ≤ L * (τ * r) ^ (-((p - 1) / p) * c)) ∧
        (∀ i (S : Set X) (hS : MeasurableSet S), S ⊆ W →
          E.energyMeasureRoot S hS (φ i).domainElement ≤
            L * (τ * r) ^ (-c) * E.energyMeasureRoot S hS u.domainElement) := by
  classical
  obtain ⟨M, hM, hOverlap⟩ := exists_uniform_cutoff_cover_overlap hvol (A := A) (by linarith)
  let L := 2 * (M : ℝ) * (C ^ p⁻¹ + (C * H * K.toReal) ^ p⁻¹ + 1)
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hC' : 0 ≤ C ^ p⁻¹ := Real.rpow_nonneg hC.le _
  have hH' : 0 ≤ (C * H * K.toReal) ^ p⁻¹ := Real.rpow_nonneg (by positivity) _
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨L, M, hL, hM, fun τ hτ ↦ ?_⟩
  obtain ⟨N, hN, hNets⟩ := exists_indexed_separated_ball_cover hvol (A := A) (by linarith) hτ
  refine ⟨N, hN, fun x r hr ↦ ?_⟩
  let s := τ * r
  have hs : 0 < s := mul_pos hτ hr
  obtain ⟨n, z, hn, hzNear, hzSep, hzCover⟩ := hNets x hr
  obtain ⟨hCounts, hCoverMass⟩ := hOverlap z hs hzSep
  let B (i : Fin n) := closedBall (z i) (A * s)
  choose ψ hψPlate hψE hψH using fun i : Fin n ↦ hcut (z i) s hs
  have hψSupp (i : Fin n) : support (ψ i).toFun ⊆ B i := by
    intro y hy
    by_contra he
    exact hy ((hψPlate i).2.2.2.2 he)
  let Nbr (i : Fin n) := Finset.univ.filter (fun j ↦ dist (z j) (z i) ≤ 2 * A * s)
  have hNbr (i j : Fin n) (h : (B i ∩ B j).Nonempty) : j ∈ Nbr i := by
    obtain ⟨y, hy⟩ := h
    simp only [Nbr, Finset.mem_filter, Finset.mem_univ, true_and]
    have hT := dist_triangle_right (z j) (z i) y
    rw [dist_comm (z j) y, dist_comm (z i) y] at hT
    have hi := mem_closedBall.mp hy.1
    have hj := mem_closedBall.mp hy.2
    linarith only [hT, hi, hj]
  obtain ⟨φ, hφ0, hφsupp, hSum, hRoot⟩ := CompactCore.exists_clipped_cutoff_partition ψ B
    (fun _ ↦ isClosed_closedBall) hψSupp (fun i ↦ (hψPlate i).2.2.1) Nbr hNbr
  have hRange (i : Fin n) (y : X) : (φ i).toFun y ∈ Icc (0 : ℝ) 1 :=
    ⟨(hφ0 i y).1, (hφ0 i y).2.trans ((hψPlate i).2.2.1 y).2⟩
  have hSumOne (y : X) (hy : y ∈ closedBall x (A * r)) : ∑ i, (φ i).toFun y = 1 := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hzCover hy)
    rw [hSum, min_eq_right]
    exact ((hψPlate i).2.2.2.1 hi).ge.trans (Finset.single_le_sum
      (fun j _ ↦ ((hψPlate j).2.2.1 y).1) (Finset.mem_univ i))
  refine ⟨n, z, φ, hn, hzNear, hRange, hφsupp, hSumOne,
    fun S hS ↦ hCoverMass _ hS, ?_, ?_⟩
  · intro i
    have hN : (Nbr i).card ≤ M := hCounts i
    have hSub : ∀ j, E.rootSeminorm (ψ j).domainElement ≤ C ^ p⁻¹ * s ^ (-((p - 1) / p) * c) := by
      intro j
      apply E.rootSeminorm_le_of_energy_le_rpow _ hC.le hs
      have h := hψE j
      rw [show d - β = -(p - 1) * c by linarith only [hScale]] at h
      exact h
    have h := hRoot i univ MeasurableSet.univ
    simp only [E.energyMeasureRoot_univ] at h
    calc
      _ ≤ 2 * ∑ j ∈ Nbr i, E.rootSeminorm (ψ j).domainElement := h
      _ ≤ 2 * ∑ j ∈ Nbr i, (C ^ p⁻¹ * s ^ (-((p - 1) / p) * c)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hSub j)) (by norm_num)
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hh : ((Nbr i).card : ℝ) ≤ M := by exact_mod_cast hN
        have hCcoef : 2 * ((Nbr i).card : ℝ) * C ^ p⁻¹ ≤ L := by
          dsimp only [L]
          nlinarith only [mul_le_mul_of_nonneg_right hh hC', mul_nonneg hM'.le hH', hM']
        calc
          _ = 2 * ((Nbr i).card : ℝ) * C ^ p⁻¹ * s ^ (-((p - 1) / p) * c) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hCcoef (Real.rpow_nonneg hs.le _)
  · intro i S hS hSW
    have hN : (Nbr i).card ≤ M := hCounts i
    have hh : ((Nbr i).card : ℝ) ≤ M := by exact_mod_cast hN
    have hSub (j : Fin n) := E.energyMeasureRoot_le_of_hausdorff_bound
      u.domainElement (ψ j).domainElement hKT (mul_nonneg hC.le hH.le) hs hS hSW hDensity (hψH j)
    calc
      _ ≤ 2 * ∑ j ∈ Nbr i, E.energyMeasureRoot S hS (ψ j).domainElement := hRoot i S hS
      _ ≤ 2 * ∑ _ ∈ Nbr i, ((C * H * K.toReal) ^ p⁻¹ * s ^ (-c) *
          E.energyMeasureRoot S hS u.domainElement) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ hSub j)) (by norm_num)
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hCcoef : 2 * ((Nbr i).card : ℝ) * (C * H * K.toReal) ^ p⁻¹ ≤ L := by
          dsimp only [L]
          nlinarith only [mul_le_mul_of_nonneg_right hh hH', mul_nonneg hM'.le hC', hM']
        calc
          _ = (2 * ((Nbr i).card : ℝ) * (C * H * K.toReal) ^ p⁻¹) * s ^ (-c) *
              E.energyMeasureRoot S hS u.domainElement := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCcoef (Real.rpow_nonneg hs.le _)) (apply_nonneg _ _)

end WalkDimensions.PEnergy
