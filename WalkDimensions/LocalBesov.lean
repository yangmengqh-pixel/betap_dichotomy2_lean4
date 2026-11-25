import WalkDimensions.BallIntegration
import WalkDimensions.LargeScale
import WalkDimensions.PEnergy

/-!
# Local Besov bound from the ball Poincaré inequality

Lemma 3.3 of arXiv:2611.02422v1. Integration over nearby centres replaces
the sum over a covering.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
private theorem lintegral_lintegral_increment_le {m : Measure X} {u : X → ℝ}
    (hu : Measurable u) {p : ℝ} (hp : 0 ≤ p) (c : ℝ) (B : Set X) :
    (∫⁻ x in B, ∫⁻ y in B, ENNReal.ofReal |u x - u y| ^ p ∂m ∂m) ≤
      ((2 : ℝ≥0∞) ^ p * 2) * m B * (∫⁻ x in B, ENNReal.ofReal |u x - c| ^ p ∂m) := by
  let f : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal |u x - c| ^ p
  let C := (2 : ℝ≥0∞) ^ p
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp (by norm_num)
  have hf : Measurable f :=
    ((continuous_abs.measurable.comp (hu.sub measurable_const)).ennreal_ofReal).pow_const _
  have hbound (x y : X) : ENNReal.ofReal |u x - u y| ^ p ≤ C * (f x + f y) := by
    simpa only [sub_sub_sub_cancel_right] using
      ennreal_abs_sub_rpow_le (u x - c) (u y - c) hp
  calc
    _ ≤ ∫⁻ x in B, ∫⁻ y in B, C * (f x + f y) ∂m ∂m :=
      lintegral_mono fun x ↦ lintegral_mono (hbound x)
    _ = C * (∫⁻ x in B, f x * m B + (∫⁻ y in B, f y ∂m) ∂m) := by
      simp only [lintegral_const_mul' _ _ hC, lintegral_add_left measurable_const, setLIntegral_const]
    _ = _ := by
      rw [lintegral_add_left (hf.mul_const _), lintegral_mul_const _ hf, setLIntegral_const]
      change C * (_ + _) = (C * 2) * m B * (∫⁻ x in B, f x ∂m)
      rw [← two_mul]
      ac_rfl

variable {m : Measure X} [SecondCountableTopology X] [SFinite m]
  [ProperSpace X] [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure]

private theorem lintegral_ballMoment_le_lintegral_pairs {D : ℝ≥0∞} (hDfin : D ≠ ∞)
    (hD : ∀ (x : X) (r : ℝ), 0 < r → m (ball x (2 * r)) ≤ D * m (ball x r))
    {p s : ℝ} (hs : 0 < s) {u : X → ℝ} (hu : Measurable u)
    {U : Set X} :
    (∫⁻ x in U, ballMoment m p u (2 * s) x ∂m) ≤
      D ^ 2 * ∫⁻ z in thickening s U, (m (ball z s))⁻¹ ^ (2 : ℕ) *
        (∫⁻ x in ball z (3 * s), ∫⁻ y in ball z (3 * s),
          ENNReal.ofReal |u x - u y| ^ p ∂m ∂m) ∂m := by
  let a := fun x : X ↦ (m (ball x s))⁻¹
  let F := fun x y : X ↦ ENNReal.ofReal |u x - u y| ^ p
  let H := fun z x : X ↦ ∫⁻ y in ball z (3 * s), F x y ∂m
  have hH : Measurable (fun q : X × X ↦ H q.2 q.1) := by
    let S : Set ((X × X) × X) := {q | dist q.2 q.1.2 < 3 * s}
    have hS : MeasurableSet S :=
      measurableSet_lt (continuous_snd.dist continuous_fst.snd).measurable measurable_const
    have hF : Measurable (fun q : (X × X) × X ↦ F q.1.1 q.2) :=
      (continuous_abs.measurable.comp
        ((hu.comp measurable_fst.fst).sub (hu.comp measurable_snd))).ennreal_ofReal.pow_const _
    have h := Measurable.lintegral_prod_right
      (f := fun q y ↦ S.indicator (fun t ↦ F t.1.1 t.2) (q, y)) (ν := m) (hF.indicator hS)
    convert h using 1
    ext q
    dsimp only [H]
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro y
    rfl
  have ha : Measurable a := (measurable_measure_ball m s).inv
  have ha' (z : X) : a z ≠ ∞ := ENNReal.inv_ne_top.mpr (measure_ball_pos m z hs).ne'
  have hD₂ : D ^ (2 : ℕ) ≠ ∞ := ENNReal.pow_ne_top hDfin
  have hfjoint : Measurable (fun q : X × X ↦ (a q.2) ^ (2 : ℕ) * H q.2 q.1) :=
    ((ha.comp measurable_snd).pow_const _).mul hH
  have hxbound (x : X) : ballMoment m p u (2 * s) x ≤
      D ^ 2 * (∫⁻ z in ball x s, (a z) ^ (2 : ℕ) * H z x ∂m) := by
    let P := ∫⁻ y in ball x (2 * s), F x y ∂m
    calc
      _ ≤ a x * P := by
        unfold ballMoment normalizedBall
        rw [lintegral_smul_measure, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (ENNReal.inv_le_inv.mpr (measure_mono (ball_subset_ball (by linarith)))) bot_le
      _ = ∫⁻ z in ball x s, (a x) ^ (2 : ℕ) * P ∂m := by
        rw [setLIntegral_const, pow_two]
        symm
        calc
          _ = a x * ((a x * m (ball x s)) * P) := by ac_rfl
          _ = _ := by
            rw [show a x * m (ball x s) = 1 from ENNReal.inv_mul_cancel
              (measure_ball_pos m x hs).ne' measure_ball_ne_top, one_mul]
      _ ≤ ∫⁻ z in ball x s, D ^ 2 * ((a z) ^ (2 : ℕ) * H z x) ∂m := by
        apply setLIntegral_mono' measurableSet_ball
        intro z hz
        have hba : m (ball z s) ≤ D * m (ball x s) := by
          simpa only [pow_one] using measure_ball_le_of_dist_le hD hs 1
            (by have h := mem_ball.mp hz; norm_num; linarith)
        have ha_le : a x ≤ D * a z := inv_measure_le_mul_inv_of_le
          (measure_ball_pos m x hs).ne' (measure_ball_pos m z hs).ne'
          measure_ball_ne_top measure_ball_ne_top hba
        have hP : P ≤ H z x := by
          apply lintegral_mono_set
          intro y hy
          apply mem_ball.mpr
          have hzy : dist x z < s := by rw [dist_comm]; exact mem_ball.mp hz
          exact (dist_triangle y x z).trans_lt (by
            have hy' := mem_ball.mp hy
            linarith)
        calc
          _ ≤ ((D * a z) ^ (2 : ℕ)) * H z x := by
            rw [pow_two, pow_two]
            exact mul_le_mul (mul_le_mul ha_le ha_le bot_le bot_le) hP bot_le bot_le
          _ = _ := by rw [mul_pow, mul_assoc]
      _ = _ := lintegral_const_mul' _ _ hD₂
  calc
    _ ≤ ∫⁻ x in U, D ^ 2 * (∫⁻ z in ball x s, (a z) ^ (2 : ℕ) * H z x ∂m) ∂m :=
      lintegral_mono hxbound
    _ = D ^ 2 * (∫⁻ z in thickening s U,
        ∫⁻ x in U ∩ ball z s, (a z) ^ (2 : ℕ) * H z x ∂m ∂m) := by
      rw [lintegral_const_mul' _ _ hD₂, lintegral_lintegral_ball_restrict_swap s hfjoint]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      apply lintegral_mono
      intro z
      change (∫⁻ x in U ∩ ball z s, (a z) ^ (2 : ℕ) * H z x ∂m) ≤
        (a z) ^ (2 : ℕ) * (∫⁻ x in ball z (3 * s), H z x ∂m)
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ha' z))]
      exact mul_le_mul_of_nonneg_left (lintegral_mono_set
        (inter_subset_right.trans (ball_subset_ball (by linarith)))) bot_le

/-- Lemma 3.3 applied to a measurable representative. The same Poincaré
dilation `A` appears in the enlargement by `2 * A * r`. -/
theorem local_besov_bound_of_poincare {p β A C : ℝ} (hp : 0 ≤ p)
    (hA : 1 ≤ A) (hC : 0 < C) (hVD : VolumeDoubling m) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K ≠ ∞ ∧
      ∀ (ν : Measure X) [SFinite ν] (u : X → ℝ), Measurable u →
      (∀ (z : X) (t : ℝ), 0 < t →
        (∫⁻ x in ball z t, ENNReal.ofReal |u x - ⨍ y in ball z t, u y ∂m| ^ p ∂m) ≤
          ENNReal.ofReal (C * t ^ β) * ν (ball z (A * t))) →
      ∀ (U : Set X), ∀ r > (0 : ℝ),
        besovEnergy m p β U u r ≤ K * ν (thickening (2 * A * r) U) := by
  obtain ⟨d, hd, hD⟩ := hVD
  let D := ENNReal.ofReal d
  have hDfin : D ≠ ∞ := ENNReal.ofReal_ne_top
  have hDpos : 0 < D := ENNReal.ofReal_pos.mpr hd
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (6 * A) (show (1 : ℝ) < 2 by norm_num)
  let B := ((2 : ℝ≥0∞) ^ p * 2)
  let P := ENNReal.ofReal (C * (3 / 2 : ℝ) ^ β)
  let K₀ := D ^ 2 * B * P
  have hPfin : P ≠ ∞ := ENNReal.ofReal_ne_top
  have hPpos : 0 < P := ENNReal.ofReal_pos.mpr (mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _))
  have hBfin : B ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp (by norm_num)) (by norm_num)
  have hBne : B ≠ 0 := mul_ne_zero
    (ENNReal.rpow_pos (by norm_num : (0 : ℝ≥0∞) < 2) (by norm_num)).ne' (by norm_num)
  have hK₀fin : K₀ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hDfin) hBfin) hPfin
  have hK₀ne : K₀ ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hDpos.ne') hBne) hPpos.ne'
  let K := D ^ 2 * K₀ * D ^ n
  refine ⟨K, pos_iff_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ hDpos.ne') hK₀ne) (pow_ne_zero _ hDpos.ne')),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hDfin) hK₀fin)
      (ENNReal.pow_ne_top hDfin), ?_⟩
  intro ν _ u hu hPI U r hr
  let s := r / 2
  let t := A * (3 * s)
  let V := thickening s U
  let R := (ENNReal.ofReal r) ^ β
  let a := fun x : X ↦ (m (ball x s))⁻¹
  have hs : 0 < s := half_pos hr
  have ht : 0 < t := mul_pos (zero_lt_one.trans_le hA) (by positivity)
  have hRpos : 0 < R := ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top
  have hRfin : R ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top
  have hscale : 2 * t ≤ (2 : ℝ) ^ n * s := by
    change 2 * (A * (3 * s)) ≤ (2 : ℝ) ^ n * s
    calc
      _ = (6 * A) * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hn.le hs.le
  have hPscale : ENNReal.ofReal (C * (3 * s) ^ β) = P * R := by
    have hr' : 3 * s = (3 / 2 : ℝ) * r := by dsimp [s]; ring
    have hpos (x : ℝ) : 0 ≤ C * (3 / 2 : ℝ) ^ x :=
      mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _)
    rw [hr', Real.mul_rpow (by norm_num) hr.le, ← mul_assoc, ENNReal.ofReal_mul (hpos β)]
    change _ = P * R
    congr 1
    exact (ENNReal.ofReal_rpow_of_pos hr).symm
  have hpoint (z : X) :
      a z ^ (2 : ℕ) * (∫⁻ x in ball z (3 * s), ∫⁻ y in ball z (3 * s),
        ENNReal.ofReal |u x - u y| ^ p ∂m ∂m) ≤
          (K₀ * R) * (a z * ν (ball z t)) := by
    have hvol : m (ball z (3 * s)) ≤ D ^ 2 * m (ball z s) := by
      apply (measure_mono (ball_subset_ball (show 3 * s ≤ (2 : ℝ) ^ 2 * s by norm_num; linarith))).trans
      exact measure_ball_two_pow_le hD z hs 2
    let c := ⨍ y in ball z (3 * s), u y ∂m
    let x := m (ball z s)
    have hc := lintegral_lintegral_increment_le (m := m) hu hp c (ball z (3 * s))
    have hi := hPI z (3 * s) (by positivity)
    change (∫⁻ y in ball z (3 * s), ENNReal.ofReal |u y - c| ^ p ∂m) ≤
      ENNReal.ofReal (C * (3 * s) ^ β) * ν (ball z t) at hi
    rw [hPscale] at hi
    have hax : a z * x = 1 :=
      ENNReal.inv_mul_cancel (measure_ball_pos m z hs).ne' measure_ball_ne_top
    calc
      _ ≤ a z ^ (2 : ℕ) * (B * (D ^ 2 * x) * ((P * R) * ν (ball z t))) := by
        exact mul_le_mul_of_nonneg_left
          (hc.trans (mul_le_mul (mul_le_mul_of_nonneg_left hvol bot_le) hi bot_le bot_le)) bot_le
      _ = (a z * x) * ((K₀ * R) * (a z * ν (ball z t))) := by
        dsimp only [K₀]
        rw [pow_two]
        ac_rfl
      _ = _ := by rw [hax, one_mul]
  have hraw : (∫⁻ x in U, ballMoment m p u r x ∂m) ≤
      (R * K) * ν (thickening (2 * A * r) U) := by
    calc
      _ ≤ D ^ 2 * (∫⁻ z in V, a z ^ (2 : ℕ) *
          (∫⁻ x in ball z (3 * s), ∫⁻ y in ball z (3 * s),
            ENNReal.ofReal |u x - u y| ^ p ∂m ∂m) ∂m) := by
        have h := lintegral_ballMoment_le_lintegral_pairs (p := p) hDfin hD hs hu (U := U)
        rw [show 2 * s = r by dsimp [s]; ring] at h
        exact h
      _ ≤ D ^ 2 * (∫⁻ z in V, (K₀ * R) * (a z * ν (ball z t)) ∂m) :=
        mul_le_mul_of_nonneg_left (lintegral_mono hpoint) bot_le
      _ ≤ D ^ 2 * ((K₀ * R) * (D ^ n * ν (thickening t V))) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hK₀fin hRfin)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (lintegral_inv_ball_mul_measure_ball_le hD hs ht hscale isOpen_thickening.measurableSet)
          bot_le) bot_le
      _ = (R * K) * ν (thickening t V) := by dsimp only [K]; ac_rfl
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (measure_mono ?_) bot_le
        exact (thickening_thickening_subset t s U).trans (thickening_mono (by
          dsimp [t, s]
          nlinarith [mul_nonneg (sub_nonneg.mpr hA) hr.le]) U)
  unfold besovEnergy
  rw [ENNReal.rpow_neg]
  calc
    _ ≤ R⁻¹ * ((R * K) * ν (thickening (2 * A * r) U)) := mul_le_mul_of_nonneg_left hraw bot_le
    _ = _ := by rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hRpos.ne' hRfin, one_mul]

namespace PEnergy

/-- Lemma 3.3 on the p-energy domain. The total-mass identity is property
(a) of the paper's energy measure. -/
theorem local_besov_bound {p β : ℝ} (E : PEnergy m p) {Γ : E.domain → Measure X}
    (hVD : VolumeDoubling m) (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ C A K, 0 < C ∧ 1 ≤ A ∧ 0 < K ∧ K ≠ ∞ ∧
      (∀ (z : X) (t : ℝ), 0 < t → ∀ f : E.domain,
        (∫⁻ x in ball z t, ENNReal.ofReal
          |(f : RealLp m p) x - ⨍ y in ball z t, (f : RealLp m p) y ∂m| ^ p ∂m) ≤
          ENNReal.ofReal (C * t ^ β) * Γ f (ball z (A * t))) ∧
      ∀ (U : Set X) (f : E.domain), ∀ r > (0 : ℝ),
        besovEnergy m p β U (f : RealLp m p) r ≤ K * Γ f (thickening (2 * A * r) U) := by
  obtain ⟨C, A, hC, hA, hPI⟩ := hPI
  obtain ⟨K, hK, hKfin, hlocal⟩ :=
    local_besov_bound_of_poincare (m := m) (β := β) (zero_lt_one.trans E.one_lt).le hA hC hVD
  refine ⟨C, A, K, hC, hA, hK, hKfin, hPI, ?_⟩
  intro U f r hr
  have : IsFiniteMeasure (Γ f) := ⟨by rw [hΓ]; exact ENNReal.coe_lt_top⟩
  have hf : AEMeasurable (f : RealLp m p) m := (Lp.aestronglyMeasurable _).aemeasurable
  let u := hf.mk (f : RealLp m p)
  have hu : (f : RealLp m p) =ᵐ[m] u := hf.ae_eq_mk
  rw [besovEnergy_congr_ae hu]
  refine hlocal (Γ f) u hf.measurable_mk (fun z t ht ↦ ?_) U r hr
  have hres := ae_restrict_of_ae (s := ball z t) hu
  have havg := average_congr hres
  have he :
      (∫⁻ x in ball z t, ENNReal.ofReal |u x - ⨍ y in ball z t, u y ∂m| ^ p ∂m) =
      ∫⁻ x in ball z t, ENNReal.ofReal
        |(f : RealLp m p) x - ⨍ y in ball z t, (f : RealLp m p) y ∂m| ^ p ∂m := by
    apply lintegral_congr_ae
    filter_upwards [hres] with x hx
    rw [hx, havg]
  exact he.le.trans (hPI z t ht f)

/-- The upper energy bound in Lemma 3.4 follows from Lemma 3.3 with
the integration region equal to the whole space. -/
theorem global_besov_bound {p β : ℝ} (E : PEnergy m p) {Γ : E.domain → Measure X}
    (hVD : VolumeDoubling m) (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K ≠ ∞ ∧ ∀ f : E.domain,
      (⨆ r : Ioi (0 : ℝ), besovEnergy m p β univ (f : RealLp m p) r) ≤
        K * (E.energy f : ℝ≥0∞) := by
  obtain ⟨_, A, K, _, _, hK, hKfin, _, hlocal⟩ := E.local_besov_bound hVD hPI hΓ
  refine ⟨K, hK, hKfin, fun f ↦ iSup_le fun r ↦ ?_⟩
  calc
    _ ≤ K * Γ f (thickening (2 * A * r) univ) := hlocal univ f r r.property
    _ ≤ K * Γ f univ := mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) bot_le
    _ = _ := by rw [hΓ]

end PEnergy

end WalkDimensions
