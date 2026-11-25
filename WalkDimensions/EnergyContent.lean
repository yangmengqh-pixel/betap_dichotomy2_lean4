import WalkDimensions.CompactLevelTest
import WalkDimensions.SublevelComparison
import Mathlib.MeasureTheory.Measure.Content

/-!
# The compact content of the energy measure

An exact level test gives a value for each compact set. Inclusion and the
two-set comparison make the value independent of the choice of test.
-/

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy.CompactCore

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {p : ℝ} {E : PEnergy μ p}

private theorem exists_levelTest (K : Compacts X) :
    ∃ g : E.CompactCore, {x | g.toFun x ≤ -1} = (K : Set X) := by
  obtain ⟨g, hg, _⟩ := E.exists_compactCore_sublevel_eq K.isCompact' isOpen_univ (subset_univ _)
  exact ⟨g, hg⟩

noncomputable def compactEnergy (f : E.CompactCore) (K : Compacts X) : ℝ :=
  f.sublevelDistribution (exists_levelTest (E := E) K).choose (-1)

theorem compactEnergy_of_level (f g : E.CompactCore) (K : Compacts X) (a : ℝ)
    (hK : {x | g.toFun x ≤ a} = (K : Set X)) :
    f.compactEnergy K = f.sublevelDistribution g a := by
  let w := (exists_levelTest (E := E) K).choose
  have hw : {x | w.toFun x ≤ -1} = (K : Set X) := (exists_levelTest (E := E) K).choose_spec
  change f.sublevelDistribution w (-1) = _
  have h (x : X) : w.toFun x ≤ -1 ↔ g.toFun x ≤ a := by
    change x ∈ {y | w.toFun y ≤ -1} ↔ x ∈ {y | g.toFun y ≤ a}
    rw [hw, hK]
  exact le_antisymm (f.sublevelDistribution_le_of_sublevel_subset w g (fun x _ ↦ (h x).mp))
    (f.sublevelDistribution_le_of_sublevel_subset g w (fun x _ ↦ (h x).mpr))

theorem compactEnergy_nonneg (f : E.CompactCore) (K : Compacts X) : 0 ≤ f.compactEnergy K :=
  Real.rpow_nonneg (f.sublevelEnergyRoot_nonneg _ _) _

theorem compactEnergy_mono (f : E.CompactCore) (K L : Compacts X) (hKL : (K : Set X) ⊆ L) :
    f.compactEnergy K ≤ f.compactEnergy L := by
  obtain ⟨g, hg⟩ := exists_levelTest (E := E) K
  obtain ⟨h, hh⟩ := exists_levelTest (E := E) L
  rw [f.compactEnergy_of_level g K (-1) hg, f.compactEnergy_of_level h L (-1) hh]
  apply f.sublevelDistribution_le_of_sublevel_subset
  intro x _ hx
  change x ∈ {y | h.toFun y ≤ -1}
  rw [hh]
  apply hKL
  rwa [← hg]

theorem compactEnergy_sup_le (f : E.CompactCore) (K L : Compacts X) :
    f.compactEnergy (K ⊔ L) ≤ f.compactEnergy K + f.compactEnergy L := by
  obtain ⟨g, hg⟩ := exists_levelTest (E := E) K
  obtain ⟨h, hh⟩ := exists_levelTest (E := E) L
  obtain ⟨w, hw⟩ := exists_levelTest (E := E) (K ⊔ L)
  rw [f.compactEnergy_of_level g K (-1) hg, f.compactEnergy_of_level h L (-1) hh,
    f.compactEnergy_of_level w (K ⊔ L) (-1) hw]
  apply f.sublevelDistribution_le_add_of_sublevel_subset
  intro x _ hx
  change x ∈ {y | g.toFun y ≤ -1} ∪ {y | h.toFun y ≤ -1}
  rw [hg, hh]
  change x ∈ (↑(K ⊔ L) : Set X)
  rw [← hw]
  exact hx

theorem compactEnergy_sup_disjoint (f : E.CompactCore) (K L : Compacts X)
    (hKL : Disjoint (K : Set X) L) :
    f.compactEnergy (K ⊔ L) = f.compactEnergy K + f.compactEnergy L := by
  obtain ⟨U, V, hU, hV, hKU, hLV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact K.isCompact' L.isCompact' hKL
  obtain ⟨g, hg, hgU⟩ := E.exists_compactCore_sublevel_eq K.isCompact' hU hKU
  obtain ⟨h, hh, hhV⟩ := E.exists_compactCore_sublevel_eq L.isCompact' hV hLV
  let w := g.minAddConst h (a := 0) le_rfl
  have hw : {x | w.toFun x ≤ -1} = (↑(K ⊔ L) : Set X) := by
    ext x
    change min (g.toFun x) (h.toFun x + 0) ≤ -1 ↔ x ∈ (K : Set X) ∪ L
    rw [add_zero, min_le_iff]
    change x ∈ {y | g.toFun y ≤ -1} ∪ {y | h.toFun y ≤ -1} ↔ _
    rw [hg, hh]
    rfl
  rw [f.compactEnergy_of_level g K (-1) hg, f.compactEnergy_of_level h L (-1) hh,
    f.compactEnergy_of_level w (K ⊔ L) (-1) hw]
  apply tendsto_nhds_unique_of_eventuallyEq (f.tendsto_oscillation_energy w (-1))
    ((f.tendsto_oscillation_energy g (-1)).add (f.tendsto_oscillation_energy h (-1)))
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)]
    with n hn
  let r := oscillationWidth n
  let A := f.oscillationCore g (-1) n
  let B := f.oscillationCore h (-1) n
  let C := f.oscillationCore w (-1) n
  have houtA (x : X) (hx : x ∉ U) : sublevelRamp r (-1) (g.toFun x) = 0 := by
    have he : g.toFun x = 0 := notMem_support.mp fun hy ↦ hx (hgU (subset_closure hy))
    rw [he]
    exact sublevelRamp_eq_zero (by linarith only [hn])
  have houtB (x : X) (hx : x ∉ V) : sublevelRamp r (-1) (h.toFun x) = 0 := by
    have he : h.toFun x = 0 := notMem_support.mp fun hy ↦ hx (hhV (subset_closure hy))
    rw [he]
    exact sublevelRamp_eq_zero (by linarith only [hn])
  have hdisj : Disjoint (support A.toFun) (support B.toFun) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hAU : x ∈ U := by
      by_contra hu
      apply hx
      change min _ (sublevelRamp r (-1) (g.toFun x)) = 0
      rw [houtA x hu, min_eq_right (sawtooth_nonneg _ _)]
    have hBV : x ∈ V := by
      by_contra hv
      apply hy
      change min _ (sublevelRamp r (-1) (h.toFun x)) = 0
      rw [houtB x hv, min_eq_right (sawtooth_nonneg _ _)]
    exact Set.disjoint_left.mp hUV hAU hBV
  have hsum : C.domainElement = (A.add B).domainElement := by
    apply domainElement_eq_of_toFun_eq
    funext x
    let T := sawtooth r (f.toFun x)
    change min T (sublevelRamp r (-1) (min (g.toFun x) (h.toFun x + 0))) =
      min T (sublevelRamp r (-1) (g.toFun x)) + min T (sublevelRamp r (-1) (h.toFun x))
    have he : sublevelRamp r (-1) (min (g.toFun x) (h.toFun x)) =
        max (sublevelRamp r (-1) (g.toFun x)) (sublevelRamp r (-1) (h.toFun x)) := by
      have hanti : Antitone (sublevelRamp r (-1)) := fun s t hst ↦
        max_le_max (min_le_min (sub_le_sub_left hst _) le_rfl) le_rfl
      exact hanti.map_min
    rw [add_zero, he]
    by_cases hx : x ∈ U
    · have hv := houtB x (Set.disjoint_left.mp hUV hx)
      rw [hv, max_eq_left (sublevelRamp_nonneg _ _ _), min_eq_right (sawtooth_nonneg _ _), add_zero]
    · have hu := houtA x hx
      rw [hu, max_eq_right (sublevelRamp_nonneg _ _ _), min_eq_right (sawtooth_nonneg _ _), zero_add]
  change (E.energy C.domainElement : ℝ) = (E.energy A.domainElement : ℝ) + (E.energy B.domainElement : ℝ)
  rw [hsum, A.energy_add_of_disjoint_support B hdisj, NNReal.coe_add]

noncomputable def energyContent (f : E.CompactCore) : Content X where
  toFun K := Real.toNNReal (f.compactEnergy K)
  mono' K L h := Real.toNNReal_le_toNNReal (f.compactEnergy_mono K L h)
  sup_disjoint' K L h _ _ := by
    rw [f.compactEnergy_sup_disjoint K L h, Real.toNNReal_add (f.compactEnergy_nonneg _) (f.compactEnergy_nonneg _)]
  sup_le' K L := by
    rw [← Real.toNNReal_add (f.compactEnergy_nonneg _) (f.compactEnergy_nonneg _)]
    exact Real.toNNReal_le_toNNReal (f.compactEnergy_sup_le K L)

theorem energyContent_apply (f : E.CompactCore) (K : Compacts X) :
    f.energyContent K = ENNReal.ofReal (f.compactEnergy K) := rfl

theorem energyContent_regular (f : E.CompactCore) : f.energyContent.ContentRegular := by
  intro K
  apply le_antisymm
  · exact le_iInf fun L ↦ le_iInf fun h ↦ f.energyContent.mono _ _ (h.trans interior_subset)
  obtain ⟨g, hg⟩ := exists_levelTest (E := E) K
  rw [f.energyContent_apply K, f.compactEnergy_of_level g K (-1) hg]
  have hlim := ENNReal.tendsto_ofReal (f.tendsto_sublevelDistribution_add_width g (-1) 1 zero_le_one)
  apply ge_of_tendsto hlim
  filter_upwards [tendsto_oscillationWidth.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)]
    with n hn
  let b := -1 + 1 * oscillationWidth n
  have hb : b < 0 := by dsimp [b]; linarith only [hn]
  have hcompact : IsCompact {x | g.toFun x ≤ b} := by
    have hclosed : IsClosed {x | g.toFun x ≤ b} := isClosed_le g.continuous continuous_const
    apply g.compactSupport.isCompact.of_isClosed_subset hclosed
    intro x hx
    exact subset_closure (fun hx' ↦ hb.not_ge (show (0 : ℝ) ≤ b by
      change g.toFun x ≤ b at hx
      rw [hx'] at hx
      exact hx))
  let L : Compacts X := ⟨{x | g.toFun x ≤ b}, hcompact⟩
  have hi : (K : Set X) ⊆ interior (L : Set X) := by
    have ho : IsOpen {x | g.toFun x < b} := isOpen_lt g.continuous continuous_const
    have hsub : {x | g.toFun x < b} ⊆ (L : Set X) := fun _ hx ↦
      show g.toFun _ ≤ b from le_of_lt hx
    apply Subset.trans _ (interior_maximal hsub ho)
    intro x hx
    change g.toFun x < b
    have hx' : g.toFun x ≤ -1 := by
      rw [← hg] at hx
      exact hx
    apply hx'.trans_lt
    dsimp [b]
    linarith only [oscillationWidth_pos n]
  exact (iInf₂_le L hi).trans_eq (by
    rw [f.energyContent_apply, f.compactEnergy_of_level g L b rfl])

/-- Energy measure on the continuous compact core. -/
noncomputable def coreEnergyMeasure (f : E.CompactCore) : Measure X := f.energyContent.measure

instance (f : E.CompactCore) : f.coreEnergyMeasure.Regular :=
  inferInstanceAs f.energyContent.measure.Regular

theorem coreEnergyMeasure_compact (f g : E.CompactCore) (K : Compacts X) (a : ℝ)
    (hK : {x | g.toFun x ≤ a} = (K : Set X)) :
    f.coreEnergyMeasure K = ENNReal.ofReal (f.sublevelDistribution g a) := by
  rw [coreEnergyMeasure, f.energyContent.measure_eq_content_of_regular f.energyContent_regular,
    energyContent_apply, compactEnergy_of_level f g K a hK]

end WalkDimensions.PEnergy.CompactCore
