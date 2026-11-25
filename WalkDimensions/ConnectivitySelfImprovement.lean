import WalkDimensions.ObstaclePaths
import WalkDimensions.UnitWeightConnectivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Openness of bounded-weight connectivity below its exponent
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [m.IsOpenPosMeasure] [SFinite m]

/-- A doubling chain space with bounded-weight connectivity at an exponent
strictly greater than one has bounded-weight connectivity at smaller
exponents in a left-hand neighbourhood. -/
theorem LowerSemicontinuousConnectivity.exists_lower_exponents {p C₀ A₀ : ℝ}
    (hp : 1 < p) (hC₀ : 0 < C₀) (hA₀ : 1 ≤ A₀) (hvol : VolumeDoubling m)
    (hCC : ChainCondition X) (hConn : LowerSemicontinuousConnectivity m p C₀ A₀) :
    ∃ ε > (0 : ℝ), ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ q ∈ Ioo (max 1 (p - ε)) p, LowerSemicontinuousConnectivity m q C A := by
  obtain ⟨D, hD, hVD⟩ := hvol
  obtain ⟨L, hL, hLBound⟩ := hCC.exists_intrinsicDistance_le
  let M := max 2 (D ^ 2)
  have hM₂ : 2 ≤ M := le_max_left _ _
  have hM₁ : 1 < M := (by norm_num : (1 : ℝ) < 2).trans_le hM₂
  have hM : 0 < M := zero_lt_one.trans hM₁
  let A := 3 * A₀
  have hA : 1 ≤ A := by dsimp only [A]; linarith
  let δ : ℝ := 1 / 8
  have hδ : 0 < δ := by norm_num [δ]
  let η := δ / C₀
  have hη : 0 < η := div_pos hδ hC₀
  let F (s : ℝ) := (2 : ℝ) ^ p * D ^ 4 * s ^ (1 - p)
  have hLim : Tendsto F atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hp)).const_mul ((2 : ℝ) ^ p * D ^ 4)
    simpa only [F, neg_sub, mul_zero] using h
  have hLimNat := hLim.comp tendsto_natCast_atTop_atTop
  obtain ⟨k, hk, hkSmall⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (hLimNat.eventually_lt_const (show 0 < η ^ p / 2 by positivity))).exists
  have hk₀ : 0 < k := zero_lt_one.trans_le hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk₀
  let G (q : ℝ) := M ^ ((k : ℝ) * (p - q))
  have hG : Continuous G :=
    Real.continuous_const_rpow hM.ne' |>.comp
      (continuous_const.mul (continuous_const.sub continuous_id))
  obtain ⟨ε, hε, hNear⟩ := Metric.continuousAt_iff.mp (hG.continuousAt (x := p)) 1 zero_lt_one
  let C := max L (2 * (C₀ * M ^ k + C₀ + 1))
  have hC : 0 < C := hL.trans_le (le_max_left L _)
  refine ⟨ε, hε, C, A, hC, hA, fun q hq ↦ ?_⟩
  have hq₁ : 1 < q := (le_max_left _ _).trans_lt hq.1
  have hq₀ := zero_lt_one.trans hq₁
  have hqp : q < p := hq.2
  have hqε : dist q p < ε := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hqp)]
    have h := (le_max_right 1 (p - ε)).trans_lt hq.1
    linarith
  have hGval : G q ≤ 2 := by
    have h := hNear hqε
    have hGp : G p = 1 := by simp [G]
    rw [Real.dist_eq, hGp] at h
    linarith only [(abs_lt.mp h).2]
  apply UnitWeightConnectivity.lowerSemicontinuousConnectivity hq₀.le
  intro vx vy g hg hg₁ τ hτ hX hY
  have hRec (n : ℕ) : ∀ (x y : X) (τ : ℝ), 0 < τ → 1 ≤ M ^ n * τ →
      localMaximalAverage m (fun z ↦ g z ^ q) (A * dist x y) x ≤ ENNReal.ofReal (τ ^ q) →
      localMaximalAverage m (fun z ↦ g z ^ q) (A * dist x y) y ≤ ENNReal.ofReal (τ ^ q) →
      ∃ γ : TimedPath x y, γ.duration ≤ C * dist x y ∧
        γ.cost g ≤ ENNReal.ofReal (C * τ * dist x y) := by
    induction n with
    | zero =>
      intro x y u hu h₁ _ _
      obtain ⟨γ, hγ⟩ := hCC.exists_timedPath x y
      have hTime : γ.duration ≤ C * dist x y := hγ ▸ (hLBound x y).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
      refine ⟨γ, hTime, (γ.cost_le_const fun z _ ↦ hg₁ _).trans ?_⟩
      rw [one_mul]
      apply ENNReal.ofReal_le_ofReal
      simp only [pow_zero, one_mul] at h₁
      apply hTime.trans
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hC.le h₁) dist_nonneg
    | succ n ih =>
      intro x y u hu he hx hy
      by_cases hxy : x = y
      · subst y
        exact ⟨TimedPath.refl x, by simp, by simp [TimedPath.cost]⟩
      let r := dist x y
      have hr : 0 < r := dist_pos.mpr hxy
      let T := δ * (A * r)
      have hT : 0 < T := by dsimp only [T]; positivity
      have hTL : 4 * T ≤ A * r := by
        dsimp only [T, δ]
        nlinarith only [mul_pos (zero_lt_one.trans_le hA) hr]
      change F (k : ℝ) < η ^ p / 2 at hkSmall
      have hPow : F (k : ℝ) * G q ≤ η ^ p :=
        (mul_le_mul_of_nonneg_left hGval (by dsimp only [F]; positivity)).trans
          (by linarith only [hkSmall])
      let H := obstacleWeight m g q T M u k
      have hMax (z : X) (hz : localMaximalAverage m (fun v ↦ g v ^ q) (A * r) z ≤ ENNReal.ofReal (u ^ q)) :
          localMaximalAverage m (fun v ↦ H v ^ p) (A₀ * r) z ≤ ENNReal.ofReal (η ^ p) := by
        apply (localMaximalAverage_obstacleWeight_le hD hVD g hg.measurable z hq₁.le hqp.le
          hM₂ (le_max_right _ _) hu (by dsimp only [A]; ring_nf; exact le_rfl) hTL hz hk₀).trans
        exact ENNReal.ofReal_le_ofReal hPow
      obtain ⟨γ, hγT, hγH⟩ := hConn x y H (lowerSemicontinuous_obstacleWeight g q T M u hk₀)
        (obstacleWeight_bounded g q T M u hk₀) η hη (hMax x hx) (hMax y hy)
      have hηC : C₀ * η * r = δ * r := by dsimp only [η]; field_simp
      rw [hηC] at hγH
      obtain ⟨i, hi, hObs⟩ := γ.exists_short_obstacle_level g hM
        (show 0 ≤ δ * r by positivity) hk₀ hγH
      let V := M ^ (i + 1)
      have hV : 0 < V := pow_pos hM _
      have hV₁ : 1 ≤ V := one_le_pow₀ hM₁.le
      have hVM : V ≤ M ^ k := pow_le_pow_right₀ hM₁.le (Nat.succ_le_of_lt hi)
      have hVs : M ≤ V := by
        dsimp only [V]
        rw [pow_succ]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hM₁.le) hM.le
      let E := obstacleSet m g q T M u i
      have hE : IsOpen E := isOpen_obstacleSet g q T M u i
      have hΘ : ENNReal.ofReal (u ^ q) ≤ ENNReal.ofReal ((V * u) ^ q) := by
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow hu.le (le_mul_of_one_le_left hu.le hV₁) hq₀.le
      have hEnd (z : X) (hz : localMaximalAverage m (fun v ↦ g v ^ q) (A * r) z ≤ ENNReal.ofReal (u ^ q)) :
          z ∉ E := by
        intro hz'
        have hh : ENNReal.ofReal ((V * u) ^ q) <
            localMaximalAverage m (fun v ↦ g v ^ q) T z := hz'
        exact hh.not_ge ((localMaximalAverage_mono (le_refl _) (by
          dsimp only [T, δ]; nlinarith only [mul_pos (zero_lt_one.trans_le hA) hr]) z).trans (hz.trans hΘ))
      have hOut : ∀ z ∉ E, g z ≤ ENNReal.ofReal (V * u) := by
        intro z hz
        have hgq := (ENNReal.continuous_rpow_const (y := q)).comp_lowerSemicontinuous hg
          (fun a b hab ↦ ENNReal.rpow_le_rpow hab hq₀.le)
        have hpt := le_localMaximalAverage_of_lowerSemicontinuous (m := m) hgq hT z
        have hz' : localMaximalAverage m (fun v ↦ g v ^ q) T z ≤ ENNReal.ofReal ((V * u) ^ q) :=
          le_of_not_gt hz
        rw [← ENNReal.ofReal_rpow_of_pos (mul_pos hV hu)] at hz'
        exact (ENNReal.rpow_le_rpow_iff hq₀).mp (hpt.trans hz')
      let W := Ioc 0 γ.duration ∩ γ.toFun ⁻¹' E
      have hW : (volume W).toReal ≤ δ * r / V := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hObs
        rwa [ENNReal.toReal_ofReal (by positivity)] at h
      have hReplace (a b : ℝ) (_ : 0 ≤ a) (hab : a < b) (_ : b ≤ γ.duration)
          (ha : γ.toFun a ∉ E) (hb : γ.toFun b ∉ E) (hba : b - a ≤ (volume W).toReal) :
          ∃ w : TimedPath (γ.toFun a) (γ.toFun b), w.duration ≤ C * (b - a) ∧
            w.cost g ≤ ENNReal.ofReal (C * (V * u)) * ENNReal.ofReal (b - a) := by
        let d := dist (γ.toFun a) (γ.toFun b)
        have hd : d ≤ b - a := by
          simpa only [d, NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm a,
            abs_of_nonneg (sub_nonneg.mpr hab.le)] using γ.lipschitz.dist_le_mul a b
        have hdT : A * d ≤ T := by
          have hδr : δ * r / V ≤ δ * r := div_le_self (by positivity) hV₁
          have h := mul_le_mul_of_nonneg_left (hd.trans (hba.trans (hW.trans hδr)))
            (zero_le_one.trans hA)
          dsimp only [T]
          exact h.trans_eq (by ring)
        have hLocal (z : X) (hz : z ∉ E) :
            localMaximalAverage m (fun v ↦ g v ^ q) (A * d) z ≤ ENNReal.ofReal ((V * u) ^ q) :=
          (localMaximalAverage_mono (le_refl _) hdT z).trans (le_of_not_gt hz)
        have hPow₀ : 1 ≤ M ^ n * (V * u) := by
          rw [pow_succ] at he
          rw [mul_assoc] at he
          exact he.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hVs hu.le) (pow_nonneg hM.le n))
        obtain ⟨w, hw, hwCost⟩ := ih (γ.toFun a) (γ.toFun b) (V * u) (mul_pos hV hu)
          hPow₀ (hLocal _ ha) (hLocal _ hb)
        refine ⟨w, hw.trans (mul_le_mul_of_nonneg_left hd hC.le), hwCost.trans ?_⟩
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd (by positivity))
      obtain ⟨w, hwT, hwCost⟩ := γ.exists_splice_of_open_obstacle g hg₁ hE (hEnd x hx) (hEnd y hy)
        hOut hC.le hReplace (ENNReal.ofReal_pos.mpr (mul_pos hu hr))
      have hTime : w.duration ≤ C * r := by
        have h₀ := hW.trans (div_le_self (by positivity) hV₁)
        have h := hwT.trans (add_le_add hγT (mul_le_mul_of_nonneg_left h₀ hC.le))
        have hC' : 2 * C₀ ≤ C :=
          (show 2 * C₀ ≤ 2 * (C₀ * M ^ k + C₀ + 1) by
            nlinarith only [mul_nonneg hC₀.le (pow_nonneg hM.le k)]).trans (le_max_right _ _)
        dsimp only [δ] at h
        change w.duration ≤ C₀ * r + C * (1 / 8 * r) at h
        nlinarith only [h, mul_le_mul_of_nonneg_right hC' hr.le, mul_nonneg hC.le hr.le]
      refine ⟨w, hTime, hwCost.trans ?_⟩
      change ENNReal.ofReal (V * u) * ENNReal.ofReal γ.duration + ENNReal.ofReal (u * r) +
        ENNReal.ofReal (C * (V * u)) * volume W ≤ _
      have hVol : volume W ≤ ENNReal.ofReal (δ * r / V) := hObs
      refine (add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal hγT) bot_le) _) (mul_le_mul_of_nonneg_left hVol bot_le)).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hmul : C * (V * u) * (δ * r / V) = C * δ * (u * r) := by field_simp
      rw [hmul]
      have hC' : 2 * (C₀ * M ^ k + 1) ≤ C := by
        apply (show 2 * (C₀ * M ^ k + 1) ≤ 2 * (C₀ * M ^ k + C₀ + 1) by linarith).trans
        exact le_max_right _ _
      have hN := mul_le_mul_of_nonneg_right hVM (show 0 ≤ C₀ * (u * r) by positivity)
      dsimp only [δ]
      nlinarith only [hN, mul_le_mul_of_nonneg_right hC' (mul_pos hu hr).le,
        mul_nonneg hC.le (mul_pos hu hr).le]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / τ) hM₁
  exact hRec n vx vy τ hτ (by
    have h := (div_lt_iff₀ hτ).mp hn
    exact h.le) hX hY

end WalkDimensions
