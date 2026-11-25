import WalkDimensions.FineOscillationMeasure
import WalkDimensions.PotentialHausdorffCutoffs
import WalkDimensions.WalkExponent
import WalkDimensions.CoreEnergyLevels

/-!
# Fine densities for a minimizing potential at a shared exponent
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal Topology

namespace WalkDimensions.PEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [ProperSpace X] [SecondCountableTopology X] {m : Measure X}
  [m.Regular] [SFinite m] [m.IsOpenPosMeasure]

theorem exists_density_point_of_shared_holder_exponent {p q d β β' c : ℝ}
    (E : PEnergy m p) (F : PEnergy m q) (hpq : p < q)
    (hvol : AhlforsRegular m d) (hβ : d < β) (hβ' : 0 < β')
    (hEq : β - d = (p - 1) * c) (hEq' : β' - β = (q - p) * c) (hc : 0 < c)
    (hPI : E.Poincare E.energyMeasure β) (hPI' : F.Poincare F.energyMeasure β')
    (hcap' : F.CapacityUpperBound β') (u : E.CompactCore)
    (hnc : ¬ ∃ a : ℝ, u.toFun =ᵐ[m] fun _ ↦ a)
    (hRange : ∀ x, u.toFun x ∈ Icc (0 : ℝ) 1)
    {H : ℝ} (hH : 0 < H) (hHolder : ∀ x y, |u.toFun x - u.toFun y| ≤ H * dist x y ^ c)
    {J : ℝ≥0∞} (hDominated : E.energyMeasure u.domainElement ≤ J • μH[c]) :
    let ν := E.energyMeasure u.domainElement
    let Ω := {x | u.toFun x ∈ Ioo (0 : ℝ) 1}
    ∃ (W : Set X) (x : X) (K b : ℝ≥0∞), MeasurableSet W ∧ W ⊆ Ω ∧ x ∈ W ∧
      K ≠ ∞ ∧ 0 < b ∧ (∀ S ⊆ W, μH[c] S ≤ K * ν S) ∧
      Tendsto (fun r : ℝ ↦ ν (ball x r \ W) / (ENNReal.ofReal r) ^ c) (𝓝[>] 0) (𝓝 0) ∧
      ∀ ε > (0 : ℝ), ∃ s ∈ Ioo (0 : ℝ) ε, b * (ENNReal.ofReal s) ^ c ≤ ν (ball x s ∩ W) := by
  let ν := E.energyMeasure u.domainElement
  let Ω := {x | u.toFun x ∈ Ioo (0 : ℝ) 1}
  have hΩ : IsOpen Ω := isOpen_Ioo.preimage u.continuous
  have hΩfull : ν Ωᶜ = 0 := by
    have hsub : Ωᶜ ⊆ {x | u.toFun x = 0} ∪ {x | u.toFun x = 1} := by
      intro x hx
      have h := hRange x
      by_cases h₀ : u.toFun x = 0
      · exact Or.inl h₀
      · by_cases h₁ : u.toFun x = 1
        · exact Or.inr h₁
        · exact (hx ⟨lt_of_le_of_ne h.1 (Ne.symm h₀), lt_of_le_of_ne h.2 h₁⟩).elim
    have hlevel (a : ℝ) : ν {x | u.toFun x = a} = 0 := by
      dsimp only [ν]
      rw [E.energyMeasure_core u]
      exact u.coreEnergyMeasure_level a
    apply measure_mono_null hsub
    have h := measure_union_le (μ := ν) {x | u.toFun x = 0} {x | u.toFun x = 1}
    rw [hlevel, hlevel, add_zero] at h
    exact le_antisymm h bot_le
  have hVD := hvol.volumeDoubling
  obtain ⟨_, A, K, _, hA, hK, hKT, _, hlocal⟩ := E.local_besov_bound hVD hPI E.energyMeasure_univ
  obtain ⟨B, _, hBT, hglobal⟩ := E.global_besov_bound hVD hPI E.energyMeasure_univ
  let M := B * ↑(E.energy u.domainElement)
  have hM : M ≠ ∞ := ENNReal.mul_ne_top hBT ENNReal.coe_ne_top
  have hB (r : ℝ) (hr : 0 < r) : besovEnergy m p β univ u.toFun r ≤ M := by
    rw [← besovEnergy_congr_ae u.ae_eq]
    exact (le_iSup (fun r : Ioi (0 : ℝ) ↦ besovEnergy m p β univ
      (u.domainElement : RealLp m p) r) ⟨r, hr⟩).trans (hglobal _)
  have hp := zero_lt_one.trans E.one_lt
  have hQ (r : ℝ) (hr : 0 < r) :
      besovEnergy m q β' univ u.toFun r ≤ (ENNReal.ofReal H) ^ (q - p) * M := by
    have h := besovEnergy_le_of_holder (m := m) (β := β) hp.le hpq.le hc.le hH.le hr univ hHolder
    rw [show β + (q - p) * c = β' by linarith only [hEq']] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hB r hr) bot_le)
  let L := liminf (besovEnergy m q β' univ u.toFun) (𝓝[>] (0 : ℝ))
  have hLT : L < ∞ := (liminf_le_of_frequently_le
    (eventually_mem_nhdsWithin.mono (fun r hr ↦ hQ r hr)).frequently
    (by isBoundedDefault)).trans_lt
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hpq.le)
      ENNReal.ofReal_ne_top) hM).lt_top
  obtain ⟨D, _, hRecover⟩ := F.exists_energy_of_besov_liminf hβ' hVD hcap'
  obtain ⟨v, hv, hvE⟩ := hRecover (u.continuous.memLp_of_hasCompactSupport u.compactSupport) hLT
  have hL : 0 < L := by
    by_contra! hz
    have hz' : L = 0 := le_antisymm hz bot_le
    change (F.energy v : ℝ≥0∞) ≤ D * L at hvE
    rw [hz', mul_zero, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at hvE
    obtain ⟨a, ha⟩ := F.ae_constant_of_energy_eq_zero hPI' F.energyMeasure_univ hvE
    exact hnc ⟨a, hv.symm.trans ha⟩
  obtain ⟨θ, hθ, W₀, hW₀, hWpos, hFine⟩ := exists_positive_measure_fine_oscillation
    (m := m) (ν := ν) (A := 2 * A) (β := β) (β' := β') hp.le hpq hc.le (by rw [hEq', mul_comm]) u.continuous hH hHolder
    hK hKT hM (fun U r hr ↦ by
      rw [← besovEnergy_congr_ae u.ae_eq]
      exact hlocal U u.domainElement r hr) hB hL
  obtain ⟨C, P, hC, hP, hMorrey⟩ := E.exists_local_morrey_bound hvol hβ hPI E.energyMeasure_univ
  obtain ⟨a, ha, haT, hDensity⟩ := exists_fine_lower_ball_mass_of_oscillation E.one_lt
    (show 0 < 2 * A by linarith only [hA]) hP hC hθ (u := u.toFun)
    (fun x r hr y hy z hz ↦ by
      have h := hMorrey u.domainElement u.continuous u.compactSupport u.ae_eq x hr y hy z hz
      rw [hEq] at h
      exact h) hFine
  exact exists_point_with_fine_mass_in_set hc hDominated hΩ.measurableSet hΩfull
    hW₀ hWpos ha haT hDensity

end WalkDimensions.PEnergy
