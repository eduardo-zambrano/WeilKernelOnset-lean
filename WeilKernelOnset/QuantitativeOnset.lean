import WeilKernelOnset.RelativeAssembly

/-!
# Logarithmic relative-error rate

The manuscript's Fourier-cutoff estimate gives a quantitative bound for the
localization parameter: `eta ε ≤ Cη / log (1 / ε)`.  That analytic estimate
remains an explicit hypothesis here.  This module checks its scalar transfer
to the relative response and assembles it with the existing operator theorem.
-/

open Set MeasureTheory Filter
open scoped InnerProduct Interval Topology

namespace WeilKernelOnset

/-- A logarithmic localization bound gives an explicit one-width relative-error
bound once the localization parameter is at most one half. -/
theorem logarithmic_relative_error_bound
    {F D γ mass η c₀ Cη ε : ℝ}
    (hF : 0 < F) (hc₀ : 0 < c₀) (hη0 : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hfirst : c₀ * γ * mass ≤ F)
    (herror : |D - F| ≤ γ * (η / (1 - η)) * mass)
    (hbelow : F ≤ D) (hrate : η ≤ Cη / Real.log (1 / ε)) :
    0 ≤ D / F - 1 ∧
      D / F - 1 ≤ (2 * Cη / c₀) / Real.log (1 / ε) := by
  have hη1 : η < 1 := by linarith
  have hden : 0 < 1 - η := by linarith
  have hlog : 0 < Real.log (1 / ε) :=
    Real.log_pos ((lt_div_iff₀ hε).2 (by simpa using hε1))
  constructor
  · have : 1 ≤ D / F := (le_div_iff₀ hF).2 (by simpa using hbelow)
    linarith
  · calc
      D / F - 1 ≤ |D / F - 1| := le_abs_self _
      _ ≤ η / (c₀ * (1 - η)) :=
        relative_response_error_bound hF hc₀ hη0 hη1 hfirst herror
      _ ≤ η / (c₀ / 2) := by
        apply div_le_div_of_nonneg_left hη0 (by positivity)
        nlinarith
      _ = (2 / c₀) * η := by field_simp
      _ ≤ (2 / c₀) * (Cη / Real.log (1 / ε)) :=
        mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = (2 * Cη / c₀) / Real.log (1 / ε) := by ring

/-- The scalar logarithmic majorant vanishes on the positive side of zero. -/
theorem tendsto_logarithmic_rate_zero (C : ℝ) :
    Tendsto (fun ε : ℝ ↦ C / Real.log (1 / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlog : Tendsto (fun ε : ℝ ↦ Real.log (1 / ε))
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div] using Real.tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero : Tendsto (fun ε : ℝ ↦ ε⁻¹) (𝓝[>] 0) atTop)
  exact tendsto_const_nhds.div_atTop hlog

/-- No separate compactness limit is needed once a nonnegative localization
parameter has the stated logarithmic upper bound. -/
theorem eta_tendsto_zero_of_logarithmic_bound
    (η : ℝ → ℝ) (Cη : ℝ)
    (hdata : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ η ε ∧ η ε ≤ Cη / Real.log (1 / ε)) :
    Tendsto η (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact squeeze_zero' (hdata.mono fun _ h ↦ h.1)
    (hdata.mono fun _ h ↦ h.2) (tendsto_logarithmic_rate_zero Cη)

/-- Family-level quantitative relative linearization. All concrete Fourier and
boundary information enters through the displayed eventual hypotheses. -/
theorem relative_first_variation_with_logarithmic_rate
    (F D mass η : ℝ → ℝ) {γ c₀ Cη : ℝ} (hc₀ : 0 < c₀)
    (hdata : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < F ε ∧ 0 ≤ η ε ∧
      c₀ * γ * mass ε ≤ F ε ∧
      |D ε - F ε| ≤ γ * (η ε / (1 - η ε)) * mass ε ∧
      F ε ≤ D ε ∧ η ε ≤ Cη / Real.log (1 / ε)) :
    Tendsto (fun ε ↦ D ε / F ε) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        0 ≤ D ε / F ε - 1 ∧
        D ε / F ε - 1 ≤ (2 * Cη / c₀) / Real.log (1 / ε) := by
  have hη := eta_tendsto_zero_of_logarithmic_bound η Cη
    (hdata.mono fun _ h ↦ ⟨h.2.1, h.2.2.2.2.2⟩)
  refine ⟨relative_first_variation_of_eta_tendsto F D mass η hc₀ hη
    (hdata.mono fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩), ?_⟩
  have hhalf : ∀ᶠ ε in 𝓝[>] (0 : ℝ), η ε < 1 / 2 :=
    hη.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hdata, hhalf, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    with ε hd hh hε
  exact logarithmic_relative_error_bound hd.1 hc₀ hd.2.1 hh.le hε.1 hε.2
    hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2

/-- Operator-family assembly with an explicit logarithmic relative-error rate.
The analytic Fourier-cutoff estimate is the named `hetaRate` hypothesis; its
vanishing limit and the quantitative conclusion are derived here. -/
theorem continuum_even_onset_with_logarithmic_relative_error
    {H P : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [Nontrivial P]
    (ev : ℝ → H →L[ℂ] ℂ) (R : ℝ → H →L[ℂ] P) (U : ℝ → P →L[ℂ] P)
    (K₀ K₁ : ℝ → H) (k : ℝ → ℝ → ℝ) (a : ℝ → ℝ)
    {γ c C Cη εmax : ℝ}
    (hγ : 0 < γ) (hc : 0 < c) (hC : 0 < C)
    (hεmax : 0 < εmax) (hεmaxQuarter : εmax ≤ 1 / 4)
    (hetaRate : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖R ε‖ ^ 2 * ‖U ε‖ ≤ Cη / Real.log (1 / ε))
    (hrep : ∀ ε f, ev ε f = inner ℂ (K₀ ε) f)
    (hEq : ∀ ε, (1 + metricOperator (R ε) (U ε)) (K₁ ε) = K₀ ε)
    (hUnorm : ∀ ε, ‖U ε‖ = γ)
    (hUself : ∀ ε, IsSelfAdjoint (U ε))
    (heven : ∀ ε, ∀ᵐ x ∂volume, k ε (-x) = k ε x)
    (hboundary : ∀ ε, 0 < ε → ε < εmax →
      HasAEBoundaryProfile boundaryProfile (k ε) c C (a ε) (2 * ε))
    (hoverlapInt : ∀ ε, 0 < ε → ε < εmax →
      IntervalIntegrable
        (fun s ↦ leftOnsetTrace (k ε) (a ε) s *
          rightOnsetTrace (k ε) (a ε) ε s) volume 0 (2 * ε))
    (hnearInt : ∀ ε, 0 < ε → ε < εmax →
      IntervalIntegrable (fun d ↦ k ε (a ε - d) ^ 2) volume 0 (2 * ε))
    (hfirstBridge : ∀ ε, 0 < ε → ε < εmax →
      (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re =
        firstOrderOverlap γ (a ε) ε (k ε))
    (hmassBridge : ∀ ε, 0 < ε → ε < εmax →
      ‖R ε (K₀ ε)‖ ^ 2 = boundaryStripMass (a ε) ε (k ε)) :
    Tendsto
      (fun ε ↦ (ev ε (K₁ ε) - ev ε (K₀ ε)).re /
        (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ εmax ∧
      ∀ ε, 0 < ε → ε < ε₀ →
        0 < (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re ∧
        (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re ≤
          (ev ε (K₁ ε) - ev ε (K₀ ε)).re ∧
        (ev ε (K₁ ε) - ev ε (K₀ ε)).im = 0 ∧
        (c ^ 2 / 4) * γ * onsetScale ε ≤ (ev ε (K₁ ε) - ev ε (K₀ ε)).re ∧
        (ev ε (K₁ ε) - ev ε (K₀ ε)).re ≤
          (4 * C ^ 2 + c ^ 2 / 4) * γ * onsetScale ε ∧
        0 ≤ (ev ε (K₁ ε) - ev ε (K₀ ε)).re /
          (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re - 1 ∧
        (ev ε (K₁ ε) - ev ε (K₀ ε)).re /
          (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re - 1 ≤
          (16 * C ^ 2 * Cη / c ^ 2) / Real.log (1 / ε) := by
  have hetaTendsto := eta_tendsto_zero_of_logarithmic_bound
    (fun ε ↦ ‖R ε‖ ^ 2 * ‖U ε‖) Cη
    (hetaRate.mono fun ε h ↦ ⟨by positivity, h⟩)
  have hbase := continuum_even_onset_with_first_variation
    ev R U K₀ K₁ k a hγ hc hC hεmax hεmaxQuarter hetaTendsto
    hrep hEq hUnorm hUself heven hboundary hoverlapInt hnearInt hfirstBridge hmassBridge
  obtain ⟨εs, hεs, hεsmax, hscale⟩ := hbase.2
  have hetaLt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖R ε‖ ^ 2 * ‖U ε‖ < 1 :=
    hetaTendsto.eventually (Iio_mem_nhds (by norm_num))
  have hquant := relative_first_variation_with_logarithmic_rate
    (fun ε ↦ (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re)
    (fun ε ↦ (ev ε (K₁ ε) - ev ε (K₀ ε)).re)
    (fun ε ↦ ‖R ε (K₀ ε)‖ ^ 2) (fun ε ↦ ‖R ε‖ ^ 2 * ‖U ε‖)
    (γ := γ) (c₀ := (c ^ 2 / 2) / (4 * C ^ 2)) (Cη := Cη) (by positivity)
    (by
      filter_upwards [Ioo_mem_nhdsGT hεs, hetaLt, hetaRate] with ε hεsCut hη hrate
      have hεmaxCut := hεsCut.2.trans_le hεsmax
      have hs := hscale ε hεsCut.1 hεsCut.2
      rcases operatorOnsetDatum_core_of_logBoundary
        (ev ε) (R ε) (U ε) (K₀ ε) (K₁ ε) (k ε)
        hεsCut.1 (hεmaxCut.le.trans hεmaxQuarter) hγ.le hc.le hC.le
        (hrep ε) (hEq ε) hη (hUnorm ε) (heven ε)
        (hboundary ε hεsCut.1 hεmaxCut)
        (hoverlapInt ε hεsCut.1 hεmaxCut) (hnearInt ε hεsCut.1 hεmaxCut)
        (hfirstBridge ε hεsCut.1 hεmaxCut) (hmassBridge ε hεsCut.1 hεmaxCut) with
        ⟨hl, _hu, _hm0, hm, hr, hre⟩
      dsimp only [operatorOnsetDatum] at hl hm hr hre
      refine ⟨hs.1, by positivity, ?_, ?_, hs.2.1, hrate⟩
      · calc
          (c ^ 2 / 2) / (4 * C ^ 2) * γ * ‖R ε (K₀ ε)‖ ^ 2 ≤
              (c ^ 2 / 2) / (4 * C ^ 2) * γ * (4 * C ^ 2 * onsetScale ε) := by
            gcongr
          _ = (c ^ 2 / 2) * γ * onsetScale ε := by field_simp
          _ ≤ (-inner ℂ (K₀ ε) (metricOperator (R ε) (U ε) (K₀ ε))).re := hl
      · simpa only [hr, add_sub_cancel_left] using hre)
  obtain ⟨εq, hεq, hqsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hquant.2
  refine ⟨hbase.1, min εs εq, lt_min hεs hεq,
    (min_le_left _ _).trans hεsmax, ?_⟩
  intro ε hε hcut
  have hs := hscale ε hε (hcut.trans_le (min_le_left _ _))
  have hq := hqsub ⟨hε, hcut.trans_le (min_le_right _ _)⟩
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, hq.1, ?_⟩
  have hcoeff : 2 * Cη / (c ^ 2 / 2 / (4 * C ^ 2)) =
      16 * C ^ 2 * Cη / c ^ 2 := by
    field_simp
    ring
  simpa only [hcoeff] using hq.2

end WeilKernelOnset
