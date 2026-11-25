import WalkDimensions.PotentialOscillationDensity
import WalkDimensions.PotentialCutoffPartition
import WalkDimensions.PotentialHarmonic
import WalkDimensions.HarmonicCutoffFlow
import WalkDimensions.TransportScales
import WalkDimensions.TransportVariationScaling

/-!
# A shared positive normalized exponent below one is impossible

The minimizing potential produces a finite coupling of nearby cutoff
centres. A Lipschitz approximation of its normalized values forces the
coupling payoff to vanish as the link scale goes to zero.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [SFinite m] [m.IsOpenPosMeasure]

theorem false_of_shared_normalized_exponent {p q d β β' c : ℝ}
    (E : PEnergy m p) (G : PEnergy m q) (hpq : p < q)
    (hvol : AhlforsRegular m d) (hβ' : 0 < β')
    (hEq : β - d = (p - 1) * c) (hEq' : β' - β = (q - p) * c)
    (hc : 0 < c) (hc₁ : c < 1)
    (hPI : E.Poincare E.energyMeasure β) (hPI' : G.Poincare G.energyMeasure β')
    (hcap : E.CapacityUpperBound β) (hcap' : G.CapacityUpperBound β')
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) : False := by
  classical
  have hp := zero_lt_one.trans E.one_lt
  have hβ : d < β := sub_pos.mp (hEq ▸ mul_pos (sub_pos.mpr E.one_lt) hc)
  have hce : (β - d) / (p - 1) = c := by
    rw [hEq, mul_comm, mul_div_cancel_right₀ _ (sub_pos.mpr E.one_lt).ne']
  have hPow : d - β = -(p - 1) * c := by linarith only [hEq]
  let α := (p - 1) / p
  have hα : 0 < α := div_pos (sub_pos.mpr E.one_lt) hp
  obtain ⟨C, H, A, hC, hH, hA, hCut⟩ :=
    E.exists_ball_unitPlate_minimizer_with_measure_bound hvol hβ hPI hcap hunbounded
  simp only [hce] at hCut
  have hA₀ := zero_lt_one.trans hA
  let x₀ := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨u, hu, huMin, _, huH, huDom⟩ := hCut x₀ 1 zero_lt_one
  let ν := E.energyMeasure u.domainElement
  have huHolder : ∀ y z, |u.toFun y - u.toFun z| ≤ H * dist y z ^ c := by
    simpa only [Real.one_rpow, mul_one] using huH
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : X, y₀ ∉ closedBall x₀ (A * 1) := by
    by_contra! h
    exact hunbounded ((isCompact_closedBall _ _).isBounded.subset fun y _ ↦ h y)
  have hnc : ¬ ∃ a : ℝ, u.toFun =ᵐ[m] fun _ ↦ a := by
    rintro ⟨a, ha⟩
    have he := Measure.eq_of_ae_eq ha u.continuous continuous_const
    have h := (congrFun he x₀).trans (congrFun he y₀).symm
    rw [hu.2.2.2.1 (mem_ball_self zero_lt_one), hu.2.2.2.2 hy₀] at h
    exact one_ne_zero h
  obtain ⟨W, x, J, b₀, hW, hWΩ, hx, hJT, hb₀, hHaus, hTail, hLower⟩ :=
    E.exists_density_point_of_shared_holder_exponent G hpq hvol hβ hβ'
      hEq hEq' hc hPI hPI' hcap' u hnc hu.2.2.1 hH huHolder huDom
  have hmap : ν.map u.toFun = (E.energy u.domainElement : ℝ≥0∞) •
      volume.restrict (Icc (0 : ℝ) 1) := by
    dsimp only [ν]
    rw [E.energyMeasure_core u]
    exact u.map_coreEnergyMeasure_of_unitPlate_minimizer (isCompact_closedBall _ _) hu huMin
  obtain ⟨V, hV, hVmass⟩ := exists_closedBall_mass_bound_of_holder hc.le hH hA₀.le
    u.continuous huHolder ENNReal.coe_ne_top hmap
  obtain ⟨L, M, hL, _, hParts⟩ := E.exists_finite_potential_cutoff_partition hA hC hH hEq
    hvol.volumeDoubling (fun z r hr ↦ by
      obtain ⟨f, hf, _, hE, _, hG⟩ := hCut z r hr
      exact ⟨f, hf, hE, hG⟩) u hJT hHaus
  let C₀ := C ^ p⁻¹
  let C₁ := (C * H * J.toReal) ^ p⁻¹
  have hC₀ : 0 ≤ C₀ := Real.rpow_nonneg hC.le _
  have hC₁ : 0 ≤ C₁ := Real.rpow_nonneg (by positivity) _
  let Q₀ := 2 * C₁ * V + 2 * C₀
  have hQ₀ : 0 ≤ Q₀ := by dsimp only [Q₀]; positivity
  let D₀ := Q₀ + 1
  let K₀ := 4 * L * (M : ℝ) * V * (2 * A) ^ c
  let A₀ := H * A ^ c
  have hA₀' : 0 < A₀ := mul_pos hH (Real.rpow_pos_of_pos hA₀ _)
  let b := (min b₀ 1).toReal
  have hb : 0 < b := ENNReal.toReal_pos (lt_min hb₀ zero_lt_one).ne'
    ((min_le_right b₀ 1).trans_lt ENNReal.one_lt_top).ne
  obtain ⟨ε, δ, hε, hδ, hSmall⟩ := exists_transport_scales (H := H) (D := D₀) (K := K₀)
    hc hc₁ (half_pos hb)
  obtain ⟨τ, hτ, hτQ⟩ := exists_pos_mul_rpow_lt (K := A₀ * Q₀) hc
    (show 0 < b / 4 by positivity) (div_pos hδ (by positivity : 0 < 2 * A))
  have hτδ : 2 * A * τ ≤ δ := by
    have h := (lt_div_iff₀ (show 0 < 2 * A by positivity)).mp hτ.2
    simpa only [mul_comm τ] using h.le
  obtain ⟨N, _, hPart⟩ := hParts τ hτ.1
  let P := 2 * L * (N : ℝ) * τ ^ (-α * c)
  let t := min 1 (b / (4 * A₀))
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  obtain ⟨η, hη, hηtail⟩ := exists_pos_mul_rpow_lt (K := P) hα ht zero_lt_one
  have hηone : η ^ α ≤ 1 := (Real.rpow_le_rpow hη.1.le hη.2.le hα.le).trans_eq (Real.one_rpow _)
  have hTail' := eventually_closedBall_compl_mass_le (ν := ν) hA₀.le hη.1 hTail
  let Ω : Set X := {z | u.toFun z ∈ Ioo (0 : ℝ) 1}
  have hΩ : IsOpen Ω := isOpen_Ioo.preimage u.continuous
  obtain ⟨r₀, hr₀, hΩ₀⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds (hWΩ hx))
  obtain ⟨r₁, hr₁, hrTail⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hTail'
  obtain ⟨r, hr, hrLower⟩ := hLower (min (r₀ / A) r₁) (lt_min (div_pos hr₀ hA₀) hr₁)
  have hrpos : 0 < r := hr.1
  have hR : 0 < r ^ c := Real.rpow_pos_of_pos hrpos _
  let B := closedBall x (A * r)
  let S := B ∩ W
  let Z := B \ S
  have hB : MeasurableSet B := measurableSet_closedBall
  have hS : MeasurableSet S := hB.inter hW
  have hZ : MeasurableSet Z := hB.diff hS
  have hBΩ : B ⊆ Ω := by
    apply (closedBall_subset_ball (x := x) ?_).trans hΩ₀
    have hh := (lt_div_iff₀ hA₀).mp (hr.2.trans_le (min_le_left _ _))
    linarith only [hh]
  have hZeq : Z = B \ W := by ext z; simp only [Z, S, Set.mem_sdiff, mem_inter_iff]; tauto
  have hZmass : (ν Z).toReal ≤ η * r ^ c := by
    rw [hZeq]
    exact hrTail ⟨hrpos, hr.2.trans_le (min_le_right _ _)⟩
  obtain ⟨χ, hχ, _, hχE, _, hχDom⟩ := hCut x r hrpos
  have hχsupp : support χ.toFun ⊆ B := by
    intro y hy
    by_contra hn
    exact hy (hχ.2.2.2.2 hn)
  have hχRoot := E.rootSeminorm_le_of_energy_le_rpow χ.domainElement hC.le hrpos (hPow ▸ hχE)
  have hχLocal := E.energyMeasureRoot_le_of_hausdorff_bound u.domainElement χ.domainElement
    hJT (mul_nonneg hC.le hH.le) hrpos hS inter_subset_right hHaus hχDom
  obtain ⟨n, z, φ, hn, hzB, hφ, hφSupp, hSum, hOverlap, hRoot, hLocal⟩ := hPart x r hrpos
  let Bφ (i : Fin n) := closedBall (z i) (A * (τ * r))
  let a (i : Fin n) := u.toFun (z i) - u.toFun x
  have ha (i : Fin n) : |a i| ≤ A₀ * r ^ c := by
    calc
      _ ≤ H * dist (z i) x ^ c := huHolder _ _
      _ ≤ H * (A * r) ^ c := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (mem_closedBall.mp (hzB i)) hc.le) hH.le
      _ = _ := by rw [Real.mul_rpow hA₀.le hrpos.le]; ring
  have hApprox (y : X) (hy : y ∈ B) :
      |u.toFun y - u.toFun x - ∑ i, a i * (φ i).toFun y| ≤ (A₀ * τ ^ c) * r ^ c := by
    have he : u.toFun y - u.toFun x - ∑ i, a i * (φ i).toFun y =
        ∑ i, (u.toFun y - u.toFun (z i)) * (φ i).toFun y := by
      have hTerm (i : Fin n) : u.toFun y - u.toFun (z i) = u.toFun y - u.toFun x - a i := by
        dsimp only [a]
        ring
      simp_rw [hTerm, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hSum y hy, mul_one]
    rw [he]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hpwise (i : Fin n) : |(u.toFun y - u.toFun (z i)) * (φ i).toFun y| ≤
        ((A₀ * τ ^ c) * r ^ c) * (φ i).toFun y := by
      by_cases hf : (φ i).toFun y = 0
      · simp [hf]
      have hyB := mem_closedBall.mp (hφSupp i (subset_closure (show y ∈ support (φ i).toFun from hf)))
      rw [abs_mul, abs_of_nonneg (hφ i y).1]
      apply mul_le_mul_of_nonneg_right _ (hφ i y).1
      apply (huHolder y (z i)).trans
      have he' : H * (A * (τ * r)) ^ c = (A₀ * τ ^ c) * r ^ c := by
        rw [Real.mul_rpow hA₀.le (mul_nonneg hτ.1.le hrpos.le), Real.mul_rpow hτ.1.le hrpos.le]
        dsimp only [A₀]
        ring
      rw [← he']
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hyB hc.le) hH.le
    exact (Finset.sum_le_sum fun i _ ↦ hpwise i).trans_eq (by rw [← Finset.mul_sum, hSum y hy, mul_one])
  have hHarmonic (v : E.CompactCore) (hv : support v.toFun ⊆ B) :
      E.energyDerivativeMeasure u.domainElement v.domainElement univ = 0 :=
    u.energyDerivativeMeasure_univ_eq_zero_of_plate_minimum_of_tsupport v hu huMin
      ((closure_minimal hv isClosed_closedBall).trans hBΩ)
  obtain ⟨F, hF, hLinks, hFlow, hBoundary, hPayoff⟩ := u.exists_harmonic_cutoff_flow χ φ
    hB hS inter_subset_left Bφ (fun _ ↦ measurableSet_closedBall) hχ.2.2.1
    (fun i y ↦ (hφ i y).1) hχsupp (fun i ↦ subset_closure.trans (hφSupp i)) hSum
    hHarmonic a ha hApprox
  let D (v : E.CompactCore) := E.energyDerivativeMeasure u.domainElement v.domainElement
  let T := ∑ j, ((D (φ j)).totalVariation Z).toReal
  let Q := ((D χ).totalVariation B).toReal
  have hT : T ≤ P * η ^ α := by
    have hEach (i : Fin n) := u.energyDerivativeMeasure_variation_le_of_scaled_compl (φ i)
      hZ hrpos hτ.1 hη.1.le hL.le hZmass (hRoot i)
    have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
    calc
      _ ≤ ∑ _ : Fin n, 2 * L * η ^ α * τ ^ (-α * c) := Finset.sum_le_sum fun i _ ↦ hEach i
      _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply (mul_le_mul_of_nonneg_right hn' (show 0 ≤ 2 * L * η ^ α * τ ^ (-α * c) from
          mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hη.1.le _))
            (Real.rpow_nonneg hτ.1.le _))).trans_eq
        dsimp only [P]
        ring
  have hQχ : ((D χ).totalVariation S).toReal ≤ 2 * C₁ * V := by
    have h := u.energyDerivativeMeasure_variation_real_le_of_local_root χ hS
      (show 0 ≤ C₁ * r ^ (-c) by positivity) hχLocal
    change _ ≤ 2 * (C₁ * r ^ (-c)) * (ν S).toReal at h
    have hVS : (ν S).toReal ≤ V * r ^ c :=
      (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_left)).trans (hVmass x r hrpos)
    apply h.trans ((mul_le_mul_of_nonneg_left hVS (by positivity)).trans_eq ?_)
    have he : r ^ (-c) * r ^ c = 1 := by rw [← Real.rpow_add hrpos, neg_add_cancel, Real.rpow_zero]
    calc
      _ = (2 * C₁ * V) * (r ^ (-c) * r ^ c) := by ring
      _ = _ := by rw [he, mul_one]
  have hQtail : ((D χ).totalVariation Z).toReal ≤ 2 * C₀ := by
    have h := u.energyDerivativeMeasure_variation_le_of_scaled_compl (τ := 1) χ hZ hrpos
      zero_lt_one hη.1.le hC₀ hZmass (by simpa only [one_mul] using hχRoot)
    simp only [Real.one_rpow, mul_one] at h
    exact h.trans (mul_le_of_le_one_right (mul_nonneg (by norm_num) hC₀) hηone)
  have hQ : Q ≤ Q₀ := by
    dsimp only [Q, Q₀]
    rw [← measure_inter_add_sdiff B hS, inter_eq_right.mpr (show S ⊆ B from inter_subset_left),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact add_le_add hQχ hQtail
  have hTD : T ≤ 1 := hT.trans (hηtail.le.trans (min_le_left _ _))
  have hTC : A₀ * T ≤ b / 4 := by
    have h := hT.trans (hηtail.le.trans (min_le_right _ _))
    apply (mul_le_mul_of_nonneg_left h hA₀'.le).trans_eq
    field_simp [hA₀'.ne']
  have hRlower : b * r ^ c ≤ weightSignedMeasure (D u) χ.toFun B := by
    have hL := ENNReal.toReal_mono (measure_ne_top _ _)
      ((mul_le_mul_of_nonneg_right (min_le_left b₀ 1) bot_le).trans hrLower)
    rw [ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_pos hrpos,
      ENNReal.toReal_ofReal hR.le] at hL
    have hSub : ball x r ∩ W ⊆ B := inter_subset_left.trans
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by nlinarith only [hA, hrpos])))
    exact hL.trans (u.le_weighted_self_of_cutoff χ hB (measurableSet_ball.inter hW)
      hSub (fun y ↦ (hχ.2.2.1 y).1) (fun y hy ↦ hχ.2.2.2.1 hy.1))
  have hPay : (b / 2) * r ^ c ≤ ∑ j, (∑ i, (F i j - F j i)) * a j := by
    apply le_trans _ hPayoff
    have hτErr : ((A₀ * τ ^ c) * r ^ c) * Q ≤ (b / 4) * r ^ c := by
      have hh := mul_le_mul_of_nonneg_left hQ (mul_nonneg (mul_nonneg hA₀'.le (Real.rpow_nonneg hτ.1.le c)) hR.le)
      exact hh.trans (by
        rw [mul_right_comm]
        refine mul_le_mul_of_nonneg_right ?_ hR.le
        calc
          _ = (A₀ * Q₀) * τ ^ c := by ring
          _ ≤ _ := hτQ.le)
    have hTErr : (A₀ * r ^ c) * T ≤ (b / 4) * r ^ c := by
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right hTC hR.le
    change _ ≤ weightSignedMeasure (D u) χ.toFun B - ((A₀ * τ ^ c) * r ^ c) * Q -
      (A₀ * r ^ c) * T
    linarith only [hRlower, hτErr, hTErr]
  let d₀ (i j : Fin n) := dist (z i) (z j) / r
  have hd₀ (i j : Fin n) : 0 ≤ d₀ i j := div_nonneg dist_nonneg hrpos.le
  have hMesh' (i j : Fin n) (h : 0 < F i j) : d₀ i j ≤ 2 * A * τ := by
    obtain ⟨y, hy⟩ := hLinks i j h
    apply (div_le_iff₀ hrpos).mpr
    have hi := mem_closedBall.mp hy.1
    have hj := mem_closedBall.mp hy.2
    have hh := dist_triangle_right (z i) (z j) y
    rw [dist_comm (z i) y, dist_comm (z j) y] at hh
    exact hh.trans ((add_le_add hi hj).trans_eq (by ring))
  have hCost : (∑ i, ∑ j, F i j * d₀ i j ^ c) ≤ K₀ := by
    have hMassV : (∑ j, ((D (φ j)).totalVariation (S ∩ Bφ j)).toReal) ≤
        (2 * L * (M : ℝ) * V) * τ ^ (-c) := by
      have hvRoot (j : Fin n) := hLocal j (S ∩ Bφ j) (hS.inter measurableSet_closedBall)
        (inter_subset_left.trans (inter_subset_right : S ⊆ W))
      have hVar (j : Fin n) := u.energyDerivativeMeasure_variation_real_le_of_local_root (φ j)
        (hS.inter measurableSet_closedBall) (mul_nonneg hL.le (Real.rpow_nonneg (mul_nonneg hτ.1.le hrpos.le) _)) (hvRoot j)
      have hsumMass : (∑ j, (ν (S ∩ Bφ j)).toReal) ≤ (M : ℝ) * (V * r ^ c) := by
        have hh := ENNReal.toReal_mono
          (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)) (hOverlap S hS)
        rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _), ENNReal.toReal_mul, ENNReal.toReal_natCast] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left
          ((ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono inter_subset_left)).trans
            (hVmass x r hrpos)) (Nat.cast_nonneg _))
      calc
        _ ≤ ∑ j, (2 * (L * (τ * r) ^ (-c))) * (ν (S ∩ Bφ j)).toReal :=
          Finset.sum_le_sum fun j _ ↦ hVar j
        _ ≤ _ := by
          rw [← Finset.mul_sum]
          apply (mul_le_mul_of_nonneg_left hsumMass (mul_nonneg (by norm_num) (mul_nonneg hL.le
            (Real.rpow_nonneg (mul_nonneg hτ.1.le hrpos.le) _)))).trans_eq
          rw [Real.mul_rpow hτ.1.le hrpos.le]
          have he : r ^ (-c) * r ^ c = 1 :=
            by rw [← Real.rpow_add hrpos, neg_add_cancel, Real.rpow_zero]
          calc
            _ = ((2 * L * (M : ℝ) * V) * τ ^ (-c)) * (r ^ (-c) * r ^ c) := by ring
            _ = _ := by rw [he, mul_one]
    have hCostPair (i j : Fin n) : F i j * d₀ i j ^ c ≤ (2 * A * τ) ^ c * F i j := by
      rcases (hF i j).eq_or_lt with h | h
      · simp [← h]
      · rw [mul_comm ((2 * A * τ) ^ c)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hd₀ i j) (hMesh' i j h) hc.le) h.le
    calc
      _ ≤ ∑ i, ∑ j, (2 * A * τ) ^ c * F i j :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hCostPair i j
      _ ≤ _ := by
        simp_rw [← Finset.mul_sum]
        apply (mul_le_mul_of_nonneg_left (hFlow.trans
          (mul_le_mul_of_nonneg_left hMassV (by norm_num)))
          (Real.rpow_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * A) hτ.1.le) _)).trans_eq
        rw [Real.mul_rpow (by positivity : 0 ≤ 2 * A) hτ.1.le]
        dsimp only [K₀]
        have he : τ ^ c * τ ^ (-c) = 1 :=
          by rw [← Real.rpow_add hτ.1, add_neg_cancel, Real.rpow_zero]
        calc
          _ = 4 * L * (M : ℝ) * V * (2 * A) ^ c * (τ ^ c * τ ^ (-c)) := by ring
          _ = _ := by rw [he, mul_one]
  have hBnd : (∑ j, |∑ i, (F i j - F j i)|) ≤ D₀ :=
    hBoundary.trans ((add_le_add hTD hQ).trans_eq (add_comm _ _))
  let h₀ (i : Fin n) := a i / r ^ c
  have hh₀ (i j : Fin n) : |h₀ i - h₀ j| ≤ H * d₀ i j ^ c := by
    dsimp only [h₀, a, d₀]
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hR,
      Real.div_rpow dist_nonneg hrpos.le]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (huHolder _ _) hR.le
  have hPayNorm : b / 2 ≤ ∑ j, (∑ i, (F i j - F j i)) * h₀ j := by
    simp only [h₀, ← mul_div_assoc, ← Finset.sum_div]
    exact (le_div_iff₀ hR).mpr hPay
  have hne : Nonempty (Fin n) := by
    by_contra hh
    have : IsEmpty (Fin n) := not_nonempty_iff.mp hh
    simp only [Finset.univ_eq_empty, Finset.sum_empty, not_le.mpr (half_pos hb)] at hPayNorm
  have hTpt := transport_pairing_le_of_small_links hd₀
    (fun i ↦ by simp [d₀]) (fun i j ↦ by dsimp only [d₀]; rw [dist_comm])
    (fun i j k ↦ by
      dsimp only [d₀]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (dist_triangle _ _ _) hrpos.le)
    hc hc₁ hH.le h₀ hh₀ F hF hδ (fun i j hij ↦ (hMesh' i j hij).trans hτδ) hε
  exact hSmall.not_ge (hPayNorm.trans (hTpt.trans (add_le_add
    (mul_le_mul_of_nonneg_left hBnd (by positivity))
    (mul_le_mul_of_nonneg_left hCost (by positivity)))))

end WalkDimensions.PEnergy
