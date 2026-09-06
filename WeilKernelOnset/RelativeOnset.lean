import WeilKernelOnset.Onset

/-!
# Relative first variation

The revised main theorem distinguishes the onset scale from the sharper limit
`response / firstOrder → 1`.  This module proves the quantitative relative-error
bound and extracts the limit from compact-localization smallness.  No boundary
or operator facts are hidden in these scalar implications.
-/

namespace WeilKernelOnset

open Filter Set
open scoped Topology

/-- A remainder controlled on the strip-mass scale is small relative to a
positive first variation that dominates that mass. -/
theorem relative_response_error_bound
    {F D γ mass η c₀ : ℝ}
    (hF : 0 < F) (hc₀ : 0 < c₀) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hfirst : c₀ * γ * mass ≤ F)
    (herror : |D - F| ≤ γ * (η / (1 - η)) * mass) :
    |D / F - 1| ≤ η / (c₀ * (1 - η)) := by
  have hden : 0 < 1 - η := sub_pos.mpr hη1
  have hq : 0 ≤ η / (c₀ * (1 - η)) :=
    div_nonneg hη0 (mul_pos hc₀ hden).le
  have hbound : |D - F| ≤ (η / (c₀ * (1 - η))) * F := by
    calc
      |D - F| ≤ γ * (η / (1 - η)) * mass := herror
      _ = (η / (c₀ * (1 - η))) * (c₀ * γ * mass) := by
        field_simp
      _ ≤ (η / (c₀ * (1 - η))) * F :=
        mul_le_mul_of_nonneg_left hfirst hq
  have heq : D / F - 1 = (D - F) / F := by
    field_simp
  rw [heq, abs_div, abs_of_pos hF]
  exact (div_le_iff₀ hF).2 hbound

/-- Family-level relative linearization, with all width-dependent input stated
only eventually on the positive side of zero. -/
theorem relative_first_variation_of_eta_tendsto
    (F D mass η : ℝ → ℝ) {γ c₀ : ℝ} (hc₀ : 0 < c₀)
    (hη : Tendsto η (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdata : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < F ε ∧ 0 ≤ η ε ∧
      c₀ * γ * mass ε ≤ F ε ∧
      |D ε - F ε| ≤ γ * (η ε / (1 - η ε)) * mass ε) :
    Tendsto (fun ε ↦ D ε / F ε) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hmajorant : Tendsto (fun ε ↦ η ε / (c₀ * (1 - η ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hg : ContinuousAt (fun x : ℝ ↦ x / (c₀ * (1 - x))) 0 := by
      fun_prop (disch := positivity)
    simpa using hg.tendsto.comp hη
  have hηlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), η ε < 1 :=
    hη.eventually (Iio_mem_nhds (by norm_num))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _ hmajorant
  filter_upwards [hdata, hηlt] with ε hd hlt
  simpa only [Real.norm_eq_abs] using
    relative_response_error_bound hd.1 hc₀ hd.2.1 hlt hd.2.2.1 hd.2.2.2

/-- Two-sided scale information is more than is needed for relative accuracy:
a positive lower bound for the first variation and an upper bound for strip
mass already provide the required domination. -/
theorem relative_first_variation_of_scale
    (datum : ℝ → OnsetDatum) {γ cF Cm : ℝ}
    (hγ : 0 < γ) (hcF : 0 < cF) (hCm : 0 < Cm)
    (hη : Tendsto (fun ε ↦ (datum ε).eta) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdata : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε < 1 ∧
      cF * γ * onsetScale ε ≤ (datum ε).firstOrder ∧
      (datum ε).stripMass ≤ Cm * onsetScale ε ∧
      0 ≤ (datum ε).eta ∧
      (datum ε).response = (datum ε).firstOrder + (datum ε).remainder ∧
      |(datum ε).remainder| ≤
        γ * ((datum ε).eta / (1 - (datum ε).eta)) * (datum ε).stripMass) :
    Tendsto (fun ε ↦ (datum ε).response / (datum ε).firstOrder)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  apply relative_first_variation_of_eta_tendsto
    (fun ε ↦ (datum ε).firstOrder) (fun ε ↦ (datum ε).response)
    (fun ε ↦ (datum ε).stripMass) (fun ε ↦ (datum ε).eta)
    (γ := γ) (c₀ := cF / Cm) (div_pos hcF hCm) hη
  filter_upwards [hdata] with ε hd
  rcases hd with ⟨hε, hε1, hfirst, hmass, hη0, hresponse, hrem⟩
  refine ⟨(mul_pos (mul_pos hcF hγ) (onsetScale_pos hε hε1)).trans_le hfirst,
    hη0, ?_, ?_⟩
  · calc
      cF / Cm * γ * (datum ε).stripMass ≤
          cF / Cm * γ * (Cm * onsetScale ε) := by gcongr
      _ = cF * γ * onsetScale ε := by field_simp
      _ ≤ (datum ε).firstOrder := hfirst
  · simpa only [hresponse, add_sub_cancel_left] using hrem

end WeilKernelOnset
