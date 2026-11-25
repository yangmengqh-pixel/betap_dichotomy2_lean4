import WalkDimensions.CoreMeasureContinuity

/-!
# The triangle inequality for the localized core energy root
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions

private theorem Icc_subset_of_isClosed_midpoint {S : Set ℝ} (hS : IsClosed S)
    (hmid : ∀ x ∈ S, ∀ y ∈ S, (x + y) / 2 ∈ S) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    Icc a b ⊆ S := by
  intro t ht
  by_contra h
  let L := S ∩ Iic t
  let U := S ∩ Ici t
  have hL : L.Nonempty := ⟨a, ha, ht.1⟩
  have hU : U.Nonempty := ⟨b, hb, ht.2⟩
  have hLb : BddAbove L := ⟨t, fun _ hx ↦ hx.2⟩
  have hUb : BddBelow U := ⟨t, fun _ hx ↦ hx.2⟩
  have hSL := (hS.inter isClosed_Iic).csSup_mem hL hLb
  have hIU := (hS.inter isClosed_Ici).csInf_mem hU hUb
  have hlo : sSup L < t := lt_of_le_of_ne hSL.2 (fun he ↦ h (he ▸ hSL.1))
  have hhi : t < sInf U := lt_of_le_of_ne hIU.2 (fun he ↦ h (he.symm ▸ hIU.1))
  let r := (sSup L + sInf U) / 2
  have hrS : r ∈ S := hmid _ hSL.1 _ hIU.1
  rcases le_total r t with hrt | htr
  · have hh := le_csSup hLb (show r ∈ L from ⟨hrS, hrt⟩)
    dsimp only [r] at hh
    linarith only [hh, hlo, hhi]
  · have hh := csInf_le hUb (show r ∈ U from ⟨hrS, htr⟩)
    dsimp only [r] at hh
    linarith only [hh, hlo, hhi]

namespace PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

theorem localEnergyRoot_eq_of_toFun_eq (f g : E.CompactCore) (h : f.toFun = g.toFun)
    {A : Set X} (hA : MeasurableSet A) : f.localEnergyRoot A = g.localEnergyRoot A := by
  unfold localEnergyRoot
  rw [f.coreEnergyMeasure_eq_on_subset_of_eqOn g hA isOpen_univ (subset_univ _)
    (fun x _ ↦ congrFun h x)]

theorem localEnergyRoot_le_rootSeminorm (f : E.CompactCore) (A : Set X) :
    f.localEnergyRoot A ≤ E.rootSeminorm f.domainElement := by
  unfold localEnergyRoot
  rw [E.rootSeminorm_apply]
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (μ := f.coreEnergyMeasure)
    (subset_univ A))
  rw [f.coreEnergyMeasure_univ, ENNReal.coe_toReal] at h
  exact Real.rpow_le_rpow ENNReal.toReal_nonneg h (inv_nonneg.mpr (zero_lt_one.trans E.one_lt).le)

private noncomputable def segmentCore (f g : E.CompactCore) (t : ℝ) : E.CompactCore :=
  (f.smul (1 - t)).add (g.smul t)

private theorem continuous_localEnergyRoot_segment (f g : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) :
    Continuous (fun t : ℝ ↦ (segmentCore f g t).localEnergyRoot A) := by
  apply continuous_iff_seqContinuous.mpr
  intro t z ht
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr E.one_lt.le⟩
  let w : E.domain := g.domainElement - f.domainElement
  have hchange (a b : ℝ) : (segmentCore f g a).domainElement - (segmentCore f g b).domainElement =
      (a - b) • w := by
    change ((1 - a) • f.domainElement + a • g.domainElement) -
      ((1 - b) • f.domainElement + b • g.domainElement) =
        (a - b) • (g.domainElement - f.domainElement)
    module
  have hlim : Tendsto (fun n ↦ |t n - z|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (ht.sub_const z).abs
  apply tendsto_localEnergyRoot (f := segmentCore f g z) (g := fun n ↦ segmentCore f g (t n)) _ _ hA
  · have h (n : ℕ) :
      ((segmentCore f g (t n)).domainElement : RealLp μ p) -
        ((segmentCore f g z).domainElement : RealLp μ p) =
        (t n - z) • (w : RealLp μ p) :=
      congrArg (fun u : E.domain ↦ (u : RealLp μ p)) (hchange (t n) z)
    simp_rw [h, norm_smul, Real.norm_eq_abs]
    simpa only [zero_mul] using hlim.mul_const ‖(w : RealLp μ p)‖
  · simp_rw [hchange, map_smul_eq_mul, Real.norm_eq_abs]
    simpa only [zero_mul] using hlim.mul_const (E.rootSeminorm w)

set_option maxHeartbeats 400000 in
private theorem localEnergyRoot_segment_le_one (f g : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A)
    (hf : f.localEnergyRoot A ≤ 1) (hg : g.localEnergyRoot A ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (segmentCore f g t).localEnergyRoot A ≤ 1 := by
  let S : Set ℝ := {t | (segmentCore f g t).localEnergyRoot A ≤ 1}
  have hS : IsClosed S := isClosed_le (continuous_localEnergyRoot_segment f g hA) continuous_const
  have hmid (x : ℝ) (hx : x ∈ S) (y : ℝ) (hy : y ∈ S) : (x + y) / 2 ∈ S := by
    let u := ((segmentCore f g x).add (segmentCore f g y)).smul (1 / 2)
    have he : (segmentCore f g ((x + y) / 2)).toFun = u.toFun := by
      funext z
      change (1 - (x + y) / 2) * f.toFun z + ((x + y) / 2) * g.toFun z =
        (1 / 2) * (((1 - x) * f.toFun z + x * g.toFun z) +
          ((1 - y) * f.toFun z + y * g.toFun z))
      ring
    change (segmentCore f g ((x + y) / 2)).localEnergyRoot A ≤ 1
    rw [localEnergyRoot_eq_of_toFun_eq _ u he hA]
    exact (localEnergyRoot_midpoint_le (segmentCore f g x) (segmentCore f g y) hA).trans
      (max_le (show (segmentCore f g x).localEnergyRoot A ≤ 1 from hx)
        (show (segmentCore f g y).localEnergyRoot A ≤ 1 from hy))
  have h0 : (0 : ℝ) ∈ S := by
    have he : (segmentCore f g 0).toFun = f.toFun := by
      funext z
      change (1 - 0) * f.toFun z + 0 * g.toFun z = _
      rw [sub_zero, one_mul, zero_mul, add_zero]
    change (segmentCore f g 0).localEnergyRoot A ≤ 1
    exact (localEnergyRoot_eq_of_toFun_eq (segmentCore f g 0) f he hA).le.trans hf
  have h1 : (1 : ℝ) ∈ S := by
    have he : (segmentCore f g 1).toFun = g.toFun := by
      funext z
      change (1 - 1) * f.toFun z + 1 * g.toFun z = _
      rw [sub_self, zero_mul, one_mul, zero_add]
    change (segmentCore f g 1).localEnergyRoot A ≤ 1
    exact (localEnergyRoot_eq_of_toFun_eq (segmentCore f g 1) g he hA).le.trans hg
  exact Icc_subset_of_isClosed_midpoint hS hmid h0 h1 ht

set_option maxHeartbeats 400000 in
theorem localEnergyRoot_add_le (f g : E.CompactCore)
    {A : Set X} (hA : MeasurableSet A) :
    (f.add g).localEnergyRoot A ≤ f.localEnergyRoot A + g.localEnergyRoot A := by
  have h (ε : ℝ) (hε : 0 < ε) :
      (f.add g).localEnergyRoot A ≤ f.localEnergyRoot A + g.localEnergyRoot A + 2 * ε := by
    let a := f.localEnergyRoot A + ε
    let b := g.localEnergyRoot A + ε
    have ha : 0 < a := add_pos_of_nonneg_of_pos (f.localEnergyRoot_nonneg A) hε
    have hb : 0 < b := add_pos_of_nonneg_of_pos (g.localEnergyRoot_nonneg A) hε
    let u := f.smul a⁻¹
    let v := g.smul b⁻¹
    have hu : u.localEnergyRoot A ≤ 1 := by
      rw [localEnergyRoot_smul, abs_of_nonneg (inv_nonneg.mpr ha.le), ← div_eq_inv_mul,
        div_le_one₀ ha]
      exact le_add_of_nonneg_right hε.le
    have hv : v.localEnergyRoot A ≤ 1 := by
      rw [localEnergyRoot_smul, abs_of_nonneg (inv_nonneg.mpr hb.le), ← div_eq_inv_mul,
        div_le_one₀ hb]
      exact le_add_of_nonneg_right hε.le
    let t := b / (a + b)
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hb.le (by positivity), (div_le_one₀ (by positivity)).mpr
        (le_add_of_nonneg_left ha.le)⟩
    have ht' := localEnergyRoot_segment_le_one u v hA hu hv ht
    have he : (segmentCore u v t).toFun = ((f.add g).smul (a + b)⁻¹).toFun := by
      funext z
      change (1 - b / (a + b)) * (a⁻¹ * f.toFun z) +
        (b / (a + b)) * (b⁻¹ * g.toFun z) = (a + b)⁻¹ * (f.toFun z + g.toFun z)
      field_simp
      <;> ring
    have ht'' := (localEnergyRoot_eq_of_toFun_eq (segmentCore u v t)
      ((f.add g).smul (a + b)⁻¹) he hA).symm.le.trans ht'
    rw [localEnergyRoot_smul,
      abs_of_nonneg (inv_nonneg.mpr (add_nonneg ha.le hb.le)), ← div_eq_inv_mul,
      div_le_one₀ (add_pos ha hb)] at ht''
    calc
      _ ≤ a + b := ht''
      _ = _ := by dsimp only [a, b]; ring
  by_contra! h'
  let ε := ((f.add g).localEnergyRoot A - (f.localEnergyRoot A + g.localEnergyRoot A)) / 3
  have hε : 0 < ε := div_pos (sub_pos.mpr h') (by norm_num)
  have he := h ε hε
  dsimp only [ε] at he
  linarith only [he, h']

end PEnergy.CompactCore

end WalkDimensions
