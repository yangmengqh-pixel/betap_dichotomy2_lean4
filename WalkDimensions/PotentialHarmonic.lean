import WalkDimensions.EnergyDerivativeLaws
import WalkDimensions.PlateMinimizer
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The variational equation of a plate minimizer
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] {p : ℝ} {E : PEnergy m p}

theorem energyDerivativeMeasure_univ_eq_zero_of_plate_minimum (f h : E.CompactCore) {K S : Set X}
    (hf : E.UnitPlate K S f.domainElement f.toFun)
    (hmin : ∀ g w, E.UnitPlate K S g w → E.energy f.domainElement ≤ E.energy g)
    (hK : EqOn h.toFun (fun _ ↦ 0) K) (hS : EqOn h.toFun (fun _ ↦ 0) Sᶜ) :
    E.energyDerivativeMeasure f.domainElement h.domainElement univ = 0 := by
  let φ := fun t : ℝ ↦ min (max t 0) 1
  have hφ : LipschitzWith 1 φ := (LipschitzWith.id.max_const 0).min_const 1
  have hφ₀ : φ 0 = 0 := by norm_num [φ]
  have hφ₁ : φ 1 = 1 := by norm_num [φ]
  have hcompare (t : ℝ) :
      (E.energy f.domainElement : ℝ) ≤ (E.energy (f.domainElement + t • h.domainElement) : ℝ) := by
    let u := f.add (h.smul t)
    let v := u.mapLipschitz φ hφ hφ₀
    have hv : E.UnitPlate K S v.domainElement v.toFun := by
      refine ⟨v.continuous, v.ae_eq, fun x ↦ ?_, ?_, ?_⟩
      · change min (max (u.toFun x) 0) 1 ∈ Icc 0 1
        exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
      · intro x hx
        change φ (f.toFun x + t * h.toFun x) = 1
        rw [hf.2.2.2.1 hx, hK hx, mul_zero, add_zero, hφ₁]
      · intro x hx
        change φ (f.toFun x + t * h.toFun x) = 0
        rw [hf.2.2.2.2 hx, hS hx, mul_zero, add_zero, hφ₀]
    apply (NNReal.coe_le_coe.mpr (hmin v.domainElement v.toFun hv)).trans
    change (E.energy v.domainElement : ℝ) ≤ (E.energy u.domainElement : ℝ)
    rw [E.energy_eq_root_rpow v.domainElement, E.energy_eq_root_rpow u.domainElement]
    exact Real.rpow_le_rpow (apply_nonneg _ _) (u.root_mapLipschitz_le φ hφ hφ₀)
      (zero_lt_one.trans E.one_lt).le
  have hLoc : IsLocalMin (fun t : ℝ ↦ (E.energy (f.domainElement + t • h.domainElement) : ℝ)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [zero_smul, add_zero] using hcompare t
  have hzero := hLoc.hasDerivAt_eq_zero (E.hasDerivAt_energy_of_energyDerivativeMeasure
    f.domainElement h.domainElement)
  exact (mul_eq_zero.mp hzero).resolve_left (zero_lt_one.trans E.one_lt).ne'

theorem energyDerivativeMeasure_univ_eq_zero_of_plate_minimum_of_tsupport (f h : E.CompactCore)
    {K S : Set X} (hf : E.UnitPlate K S f.domainElement f.toFun)
    (hmin : ∀ g w, E.UnitPlate K S g w → E.energy f.domainElement ≤ E.energy g)
    (hsupp : tsupport h.toFun ⊆ {x | f.toFun x ∈ Ioo (0 : ℝ) 1}) :
    E.energyDerivativeMeasure f.domainElement h.domainElement univ = 0 := by
  apply f.energyDerivativeMeasure_univ_eq_zero_of_plate_minimum h hf hmin
  · intro x hx
    apply notMem_support.mp
    intro hne
    have hh := hsupp (subset_closure hne)
    have he := hf.2.2.2.1 hx
    exact (show f.toFun x < 1 from hh.2).ne he
  · intro x hx
    apply notMem_support.mp
    intro hne
    have hh := hsupp (subset_closure hne)
    have he := hf.2.2.2.2 hx
    exact (show 0 < f.toFun x from hh.1).ne' he

end WalkDimensions.PEnergy.CompactCore
