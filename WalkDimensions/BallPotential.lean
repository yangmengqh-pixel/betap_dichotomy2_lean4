import WalkDimensions.BesovMembership
import WalkDimensions.CapacityCutoffs
import WalkDimensions.LocalBesov
import WalkDimensions.PotentialTruncation

/-!
# Compactly supported Hölder tests

Ball capacity provides a feasible function for the plate minimization.
This gives the compactly supported test used in the positive-exponent
comparison of Section 5.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [IsFiniteMeasureOnCompacts m] [m.IsOpenPosMeasure] {p : ℝ} (E : PEnergy m p)

/-- In the positive Morrey range, the measurable ball cutoffs from
capacity have continuous representatives. -/
theorem exists_continuous_ball_cutoff {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β) :
    ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ (x : X) (r : ℝ), 0 < r →
      ∃ f u, E.UnitPlate (ball x r) (closedBall x (A * r)) f u ∧
        (E.energy f : ℝ≥0∞) ≤ ENNReal.ofReal (C * r ^ (-β)) * m (ball x r) := by
  obtain ⟨C, A, hC, hA, hcut⟩ := E.exists_measurable_ball_cutoff hcap
  obtain ⟨_, _, hrep⟩ := E.exists_holder_representative hvol hβ hPI hΓ
  refine ⟨C, A, hC, hA, fun x r hr ↦ ?_⟩
  let B := ball x r
  let S := closedBall x (A * r)
  have hS : IsCompact S := isCompact_closedBall x _
  obtain ⟨g, w, hg, _, _, hrange, h1, h0, hEg⟩ := hcut x r hr
  obtain ⟨v, hv, hgv, _⟩ := hrep g
  have hvw := hgv.symm.trans hg
  have hVeq (T : Set X) (hT : IsOpen T) (c : ℝ) (h : EqOn w (fun _ ↦ c) T) :
      EqOn v (fun _ ↦ c) T := by
    apply Measure.eqOn_open_of_ae_eq (μ := m) _ hT hv.continuousOn continuousOn_const
    filter_upwards [ae_restrict_of_ae (s := T) hvw, ae_restrict_mem hT.measurableSet] with z hz hzT
    exact hz.trans (h hzT)
  have hvRange (z : X) : v z ∈ Icc (0 : ℝ) 1 := by
    have hclosed : IsClosed {z | v z ∈ Icc (0 : ℝ) 1} := isClosed_Icc.preimage hv
    have hae : {z | v z ∈ Icc (0 : ℝ) 1} =ᵐ[m] (univ : Set X) := by
      filter_upwards [hvw] with y hy
      simpa only [mem_ofPred_eq, mem_univ, iff_true, hy] using hrange y
    have he := hclosed.ae_eq_univ_iff_eq.1 hae
    exact (show z ∈ {y | v y ∈ Icc (0 : ℝ) 1} from he ▸ mem_univ z)
  have hgv' : E.UnitPlate B S g v :=
    ⟨hv, hgv, hvRange, hVeq B isOpen_ball 1 h1,
      hVeq Sᶜ hS.isClosed.isOpen_compl 0 (h0.mono (compl_subset_compl.mpr ball_subset_closedBall))⟩
  exact ⟨g, v, hgv', hEg⟩

/-- Capacity and Poincaré give a continuous compactly supported minimizing
ball potential. -/
theorem exists_ball_unitPlate_minimizer {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    ∃ C A : ℝ, 0 < C ∧ 1 < A ∧ ∀ (x : X) (r : ℝ), 0 < r →
      ∃ f u, E.UnitPlate (ball x r) (closedBall x (A * r)) f u ∧
        (∀ g w, E.UnitPlate (ball x r) (closedBall x (A * r)) g w → E.energy f ≤ E.energy g) ∧
        (E.energy f : ℝ≥0∞) ≤ ENNReal.ofReal (C * r ^ (-β)) * m (ball x r) := by
  obtain ⟨C, A, hC, hA, hcut⟩ := E.exists_continuous_ball_cutoff hvol hβ hPI hΓ hcap
  refine ⟨C, A, hC, hA, fun x r hr ↦ ?_⟩
  let S := closedBall x (A * r)
  have hS : IsCompact S := isCompact_closedBall x _
  have hSproper : Sᶜ.Nonempty := by
    by_contra! h
    exact hunbounded ((compl_empty_iff.mp h) ▸ hS.isBounded)
  obtain ⟨g, v, hgv', hEg⟩ := hcut x r hr
  obtain ⟨f, u, hu, hmin⟩ :=
    E.exists_unitPlate_minimizer hvol hβ hPI hΓ hS hSproper ⟨g, v, hgv'⟩
  exact ⟨f, u, hu, hmin, (ENNReal.coe_le_coe.mpr (hmin g v hgv')).trans hEg⟩

variable [Nonempty X] [SFinite m]

/-- In the range (eta>d), the source assumptions provide the
nonconstant compactly supported test with the sharp Hölder exponent
used in Lemma 5.2. -/
theorem exists_holder_besov_test {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    ∃ (u : X → ℝ) (M : ℝ≥0∞) (K : ℝ), Continuous u ∧ HasCompactSupport u ∧
      (¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c) ∧ M ≠ ∞ ∧ 0 ≤ K ∧
      (∀ r > (0 : ℝ), besovEnergy m p β univ u r ≤ M) ∧
      (∀ x y, |u x - u y| ≤ K * dist x y ^ ((β - d) / (p - 1))) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, A, _, _, htest⟩ := E.exists_ball_unitPlate_minimizer hvol hβ hPI hΓ hcap hunbounded
  obtain ⟨f, u, hfu, hmin, _⟩ := htest x 1 zero_lt_one
  let S := closedBall x (A * 1)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hc : HasCompactSupport u := HasCompactSupport.intro hS hfu.2.2.2.2
  obtain ⟨K, hK, hholder⟩ := E.exists_minimizer_holder_bound hvol hβ hPI hΓ
  obtain ⟨M, _, hM, hbound⟩ := E.global_besov_bound hvol.volumeDoubling hPI hΓ
  refine ⟨u, M * (E.energy f : ℝ≥0∞), K * (E.energy f : ℝ) ^ (p - 1)⁻¹,
    hfu.1, hc, ?_, ENNReal.mul_ne_top hM ENNReal.coe_ne_top, by positivity, ?_,
    hholder hS hfu hmin⟩
  · rintro ⟨c, h⟩
    have he := Measure.eq_of_ae_eq h hfu.1 continuous_const
    obtain ⟨y, hy⟩ : Sᶜ.Nonempty := by
      by_contra! h
      exact hunbounded ((compl_empty_iff.mp h) ▸ hS.isBounded)
    have hx := hfu.2.2.2.1 (mem_ball_self (x := x) zero_lt_one)
    have hy' := hfu.2.2.2.2 hy
    exact one_ne_zero (hx.symm.trans ((congrFun he x).trans ((congrFun he y).symm.trans hy')))
  · intro r hr
    rw [← besovEnergy_congr_ae hfu.2.1]
    exact (le_iSup (fun s : Ioi (0 : ℝ) ↦ besovEnergy m p β univ (f : RealLp m p) s) ⟨r, hr⟩).trans
      (hbound f)


/-- The Besov membership asserted in Lemma 5.2, for a nonconstant
compactly supported ball potential. -/
theorem exists_besov_interpolation_test {d β : ℝ} (hvol : AhlforsRegular m d)
    (hβ : d < β) {Γ : E.domain → Measure X} (hPI : E.Poincare Γ β)
    (hΓ : ∀ f, Γ f univ = (E.energy f : ℝ≥0∞)) (hcap : E.CapacityUpperBound β)
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X)) :
    ∃ u : X → ℝ, Continuous u ∧ HasCompactSupport u ∧
      (¬ ∃ c : ℝ, u =ᵐ[m] fun _ ↦ c) ∧
      ∀ q > p, ∀ b > (0 : ℝ), b ≤ (q - 1) * ((β - d) / (p - 1)) + d →
        InBesov m q (b / q) u := by
  obtain ⟨u, M, K, hu, hc, hnc, hM, hK, hb, hholder⟩ :=
    E.exists_holder_besov_test hvol hβ hPI hΓ hcap hunbounded
  refine ⟨u, hu, hc, hnc, fun q hpq b hb₀ hb₁ ↦ ?_⟩
  have hp : 0 < p := zero_lt_one.trans E.one_lt
  have hq : 0 < q := hp.trans hpq
  have hγ : 0 ≤ (β - d) / (p - 1) := div_nonneg (sub_nonneg.mpr hβ.le) (sub_nonneg.mpr E.one_lt.le)
  have hγp : (p - 1) * ((β - d) / (p - 1)) = β - d := by
    rw [mul_comm, div_mul_cancel₀ _ (sub_pos.mpr E.one_lt).ne']
  have hscale : q * (b / q) ≤ β + (q - p) * ((β - d) / (p - 1)) := by
    rw [mul_comm, div_mul_cancel₀ _ hq.ne']
    exact hb₁.trans_eq (by linarith only [hγp])
  exact inBesov_of_holder hvol hp hpq.le (div_pos hb₀ hq) hγ hK hscale hu.measurable
    (hu.memLp_of_hasCompactSupport hc) hM (fun r hr ↦ hb r hr.1) hholder

end WalkDimensions.PEnergy
