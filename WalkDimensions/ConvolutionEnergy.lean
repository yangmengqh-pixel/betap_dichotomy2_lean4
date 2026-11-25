import WalkDimensions.DiscreteOscillation
import WalkDimensions.EnergyLocality
import WalkDimensions.EnergyGluing
import Mathlib.Analysis.MeanInequalities

/-!
# Energy of a discrete convolution

On each covering ball the constant reference average drops out by
locality. The remaining weights meet only a uniformly bounded number of
neighbours, and their oscillations are controlled by the Besov moment.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X} [SFinite m]
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

omit [ProperSpace X] [SecondCountableTopology X] [SFinite m] [m.IsOpenPosMeasure] in
private theorem energy_finset_smul_sum_le {ι : Type*} (t : Finset ι)
    (f : ι → E.domain) (a : ι → ℝ) :
    (E.energy (∑ i ∈ t, a i • f i) : ℝ) ≤
      (t.card : ℝ) ^ (p - 1) * ∑ i ∈ t, |a i| ^ p * (E.energy (f i) : ℝ) := by
  classical
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  let S := E.rootSeminorm
  have hsum : S (∑ i ∈ t, a i • f i) ≤ ∑ i ∈ t, |a i| * S (f i) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
      simp only [Finset.sum_insert hj]
      refine (S.add_le' _ _).trans ?_
      change S (a j • f j) + S (∑ i ∈ t, a i • f i) ≤ _
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      exact add_le_add_right ih _
  rw [E.energy_eq_root_rpow]
  calc
    _ ≤ (∑ i ∈ t, |a i| * S (f i)) ^ p :=
      Real.rpow_le_rpow (apply_nonneg _ _) hsum hp.le
    _ ≤ (t.card : ℝ) ^ (p - 1) * ∑ i ∈ t, (|a i| * S (f i)) ^ p :=
      Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg t E.one_lt.le (fun i _ ↦ by positivity)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.mul_rpow (abs_nonneg _) (apply_nonneg _ _), ← E.energy_eq_root_rpow]

theorem exists_discrete_convolution_energy_le (hvol : VolumeDoubling m) {β A C : ℝ}
    (hA : 1 < A) (hC : 0 < C) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ (t : Finset X) (r : ℝ), 0 < r →
      (↑t : Set X).Pairwise (fun x y ↦ r ≤ dist x y) →
      ∀ (g : X → E.domain) (w : X → X → ℝ),
      (∀ z, (g z : RealLp m p) =ᵐ[m] w z) →
      (∀ z, tsupport (w z) ⊆ closedBall z (A * r)) →
      (∀ z, E.rootSeminorm (g z) ≤ C * (r ^ (-β) * m.real (ball z r)) ^ p⁻¹) →
      ∀ (U : Set X), IsOpen U → EqOn (fun x ↦ ∑ z ∈ t, w z x) (fun _ ↦ 1) U →
      ∀ (u : X → ℝ), Measurable u → MemLp u (ENNReal.ofReal p) m →
      let a (z : X) := ⨍ y in ball z r, u y ∂m
      tsupport (fun x ↦ ∑ z ∈ t, a z * w z x) ⊆ U →
      (E.energy (∑ z ∈ t, a z • g z) : ℝ≥0∞) ≤
        K * ENNReal.ofReal (r ^ (-β)) *
          (∫⁻ x, ballMoment m p u ((2 * A + 3) * r) x ∂m) := by
  classical
  let B := 2 * A + 1
  have hB : 0 ≤ B := by dsimp [B]; linarith
  obtain ⟨M, _, hpack⟩ := exists_card_le_of_separated_centres hvol (R := 2 * B) (by positivity)
  obtain ⟨J, hJ, hosc⟩ := exists_sum_ball_average_oscillation_le hvol hB
  obtain ⟨D, hD', hD⟩ := hvol
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B + 1) (show (1 : ℝ) < 2 by norm_num)
  let L := (M : ℝ) ^ (p - 1) * C ^ p * D ^ n
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hA' : 0 < A := zero_lt_one.trans hA
  refine ⟨ENNReal.ofReal L * J, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ,
    fun t r hr hsep g w hgw hw henergy U hU hUnity u hu huLp ↦ ?_⟩
  let a (z : X) := ⨍ y in ball z r, u y ∂m
  let f := ∑ z ∈ t, a z • g z
  let v (x : X) := ∑ z ∈ t, a z * w z x
  change tsupport v ⊆ U → (E.energy f : ℝ≥0∞) ≤ _
  intro hvU
  let N (z : X) := t.filter fun y ↦ dist y z ≤ B * r
  let W (z : X) := U ∩ ball z ((A + 1) * r)
  have hW (z : X) : IsOpen (W z) := hU.inter isOpen_ball
  have hN (z : X) : N z ⊆ t := Finset.filter_subset _ _
  have hNear (z y : X) (hy : y ∈ N z) : dist y z ≤ B * r := (Finset.mem_filter.mp hy).2
  have hCard (z : X) : (N z).card ≤ M := by
    apply hpack z (r / 2) (by positivity)
    · intro y hy
      rw [show 2 * B * (r / 2) = B * r by ring]
      exact hNear z y hy
    · intro x hx y hy hxy
      rw [show 2 * (r / 2) = r by ring]
      exact hsep (hN z hx) (hN z hy) hxy
  have hFsum (s : Finset X) (c : X → ℝ) :
      ((∑ z ∈ s, c z • g z : E.domain) : RealLp m p) =ᵐ[m]
        fun x ↦ ∑ z ∈ s, c z * w z x := by
    apply E.coeFn_finsetSum
    intro z _
    filter_upwards [Lp.coeFn_smul (c z) (g z : RealLp m p), hgw z] with x hx hzx
    change (c z • (g z : RealLp m p)) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hzx]
  have hSupports (s : Finset X) (c : X → ℝ) :
      tsupport (fun x ↦ ∑ z ∈ s, c z * w z x) ⊆ ⋃ z ∈ s, tsupport (w z) := by
    apply closure_minimal _ (isClosed_biUnion_finset (fun _ _ ↦ isClosed_closure))
    intro x hx
    by_contra h₀
    apply hx
    apply Finset.sum_eq_zero
    intro z hz
    have hzero : w z x = 0 := notMem_support.mp fun h ↦ h₀ (mem_iUnion₂.mpr ⟨z, hz, subset_closure h⟩)
    rw [hzero, mul_zero]
  have hcover : tsupport v ⊆ ⋃ z ∈ t, W z := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hSupports t a hx)
    apply mem_iUnion₂.mpr
    refine ⟨z, hz, hvU hx, mem_ball.mpr ?_⟩
    have hh := mem_closedBall.mp (hw z hxz)
    linarith only [hh, hr]
  have hJac (z y : X) (hy : y ∈ N z) :
      m.real (ball y r) ≤ D ^ n * m.real (ball z r) := by
    have hRadius : dist y z + r ≤ (2 : ℝ) ^ n * r := by
      calc
        _ ≤ (B + 1) * r := by linarith only [hNear z y hy]
        _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hr.le
    have h := measure_ball_le_of_dist_le hD hr n hRadius
    have hfin : (ENNReal.ofReal D) ^ n * m (ball z r) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) measure_ball_ne_top
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hD'.le]
      using ENNReal.toReal_mono hfin h
  let G (z : X) := ∑ y ∈ N z, m.real (ball z r) * |a z - a y| ^ p
  let c (z y : X) := a y - a z
  let k (z : X) := ∑ y ∈ N z, c z y • g y
  let q (z x : X) := ∑ y ∈ N z, c z y * w y x
  have hEq (z x : X) (hx : x ∈ W z) : v x - q z x = a z := by
    have hweighted : (∑ y ∈ N z, c z y * w y x) = ∑ y ∈ t, c z y * w y x := by
      apply Finset.sum_subset (hN z)
      intro y hy hny
      have hz₀ : w y x = 0 := by
        apply notMem_support.mp
        intro h
        have hh := mem_closedBall.mp (hw y (subset_closure h))
        have h' := mem_ball.mp hx.2
        have htri := dist_triangle y x z
        rw [dist_comm y x] at htri
        exact hny (Finset.mem_filter.mpr ⟨hy, by dsimp [B]; linarith only [hh, h', htri]⟩)
      rw [hz₀, mul_zero]
    dsimp only [v, q]
    rw [hweighted]
    simp only [c, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hOne : (∑ j ∈ t, w j x) = 1 := hUnity hx.1
    rw [hOne, mul_one, sub_sub_cancel]
  have hmass : (E.energy f : ℝ) ≤ ∑ z ∈ t, (E.energy (k z) : ℝ) := by
    let s : Finset (Option X) := insert none (t.image some)
    let V : Option X → Set X := Option.elim' (tsupport v)ᶜ W
    let K : Option X → E.domain := Option.elim' 0 k
    let A : Option X → ℝ := Option.elim' 0 a
    have hOpen : ∀ i ∈ s, IsOpen (V i) := by
      intro i _
      cases i with
      | none => exact isClosed_closure.isOpen_compl
      | some z => exact hW z
    have hC : univ ⊆ ⋃ i ∈ s, V i := by
      intro x _
      by_cases hx : x ∈ tsupport v
      · obtain ⟨z, hz, hzx⟩ := mem_iUnion₂.mp (hcover hx)
        exact mem_iUnion₂.mpr ⟨some z, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz), hzx⟩
      · exact mem_iUnion₂.mpr ⟨none, Finset.mem_insert_self _ _, hx⟩
    have hLocal : ∀ i ∈ s, ∀ᵐ x ∂m, x ∈ V i →
        (f : RealLp m p) x - (K i : RealLp m p) x = A i := by
      intro i _
      cases i with
      | none =>
        filter_upwards [hFsum t a, Lp.coeFn_zero ℝ (ENNReal.ofReal p) m] with x hx hz
        intro hxu
        change (f : RealLp m p) x - (0 : RealLp m p) x = 0
        rw [hx, hz, Pi.zero_apply, sub_zero]
        exact notMem_support.mp fun h ↦ hxu (subset_closure h)
      | some z =>
        filter_upwards [hFsum t a, hFsum (N z) (c z)] with x hx hy
        intro hxu
        change (f : RealLp m p) x - (k z : RealLp m p) x = a z
        rw [hx, hy]
        exact hEq z x hxu
    have hBound := E.energy_le_sum_of_local_extensions f s V K A hOpen hC hLocal
    dsimp [s] at hBound
    rw [Finset.sum_insert (by simp), Finset.sum_image (fun _ _ _ _ h ↦ Option.some.inj h)] at hBound
    change (E.energy f : ℝ) ≤ (E.energy (0 : E.domain) : ℝ) + ∑ z ∈ t, (E.energy (k z) : ℝ) at hBound
    simpa only [E.energy_eq_root_rpow 0, map_zero, Real.zero_rpow hp.ne', zero_add] using hBound
  have hlocal (z : X) : (E.energy (k z) : ℝ) ≤ (L * r ^ (-β)) * G z := by
    have hbound := E.energy_finset_smul_sum_le (N z) g (c z)
    have hroot (y : X) : (E.energy (g y) : ℝ) ≤ C ^ p * (r ^ (-β) * m.real (ball y r)) := by
      rw [E.energy_eq_root_rpow]
      have h := Real.rpow_le_rpow (apply_nonneg _ _) (henergy y) hp.le
      rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul (by positivity),
        inv_mul_cancel₀ hp.ne', Real.rpow_one] at h
      exact h
    have hcardPow : ((N z).card : ℝ) ^ (p - 1) ≤ (M : ℝ) ^ (p - 1) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hCard z) (sub_nonneg.mpr E.one_lt.le)
    have hsum : (∑ y ∈ N z, |c z y| ^ p * (E.energy (g y) : ℝ)) ≤
        (C ^ p * D ^ n * r ^ (-β)) * G z := by
      dsimp only [G]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      have h := mul_le_mul_of_nonneg_left ((hroot y).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hJac z y hy) (by positivity)) (by positivity))) (by positivity : 0 ≤ |c z y| ^ p)
      refine h.trans_eq ?_
      simp only [c, abs_sub_comm (a y) (a z)]
      ring
    calc
      _ ≤ _ := hbound
      _ ≤ (M : ℝ) ^ (p - 1) * ((C ^ p * D ^ n * r ^ (-β)) * G z) :=
        mul_le_mul hcardPow hsum (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hTotal : (E.energy f : ℝ) ≤ (L * r ^ (-β)) * ∑ z ∈ t, G z := by
    rw [Finset.mul_sum]
    exact hmass.trans (Finset.sum_le_sum fun z _ ↦ hlocal z)
  have hCast (z : X) : ENNReal.ofReal (G z) =
      ∑ y ∈ N z, m (ball z r) * ENNReal.ofReal |a z - a y| ^ p := by
    dsimp only [G]
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [ENNReal.ofReal_mul (by positivity), measureReal_def,
      ENNReal.ofReal_toReal (measure_ball_ne_top (μ := m)),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  have hOsc := hosc E.one_lt.le t r hr hsep N hN hNear u hu huLp
  change _ ≤ J * (∫⁻ x, ballMoment m p u ((B + 2) * r) x ∂m) at hOsc
  have heq : B + 2 = 2 * A + 3 := by dsimp [B]; ring
  rw [heq] at hOsc
  have hGnonneg (z : X) : 0 ≤ G z := Finset.sum_nonneg fun y _ ↦ by positivity
  have hBound := ENNReal.ofReal_le_ofReal hTotal
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_mul (by positivity : 0 ≤ L * r ^ (-β)),
    ENNReal.ofReal_mul hL, ENNReal.ofReal_sum_of_nonneg (fun z _ ↦ hGnonneg z)] at hBound
  simp only [hCast] at hBound
  exact hBound.trans ((mul_le_mul_of_nonneg_left hOsc bot_le).trans_eq (by ac_rfl))

end WalkDimensions.PEnergy
