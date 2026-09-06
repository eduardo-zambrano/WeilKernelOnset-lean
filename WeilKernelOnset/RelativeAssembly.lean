import WeilKernelOnset.Assembly
import WeilKernelOnset.RelativeOnset
import WeilKernelOnset.PositiveRemainder

/-!
# The onset theorem with relative first variation

This assembly retains the original boundary and concrete-support interfaces.
It adds self-adjointness of the physical update, derives reality and the
nonnegative remainder, and proves the new relative limit.  The direct
mixed-correlation proof of the scale is separately checked in `MixedOnset`.
-/

open Set MeasureTheory Filter
open scoped InnerProduct Interval Topology

namespace WeilKernelOnset

/-- The revised main conclusion: the existing continuum scale together with a
positive first variation, a nonnegative real response remainder, and relative
first-order accuracy.  The concrete analytic inputs remain named hypotheses. -/
theorem continuum_even_onset_with_first_variation
    {H P : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [Nontrivial P]
    (ev : ℝ → H →L[ℂ] ℂ) (R : ℝ → H →L[ℂ] P) (U : ℝ → P →L[ℂ] P)
    (K₀ K₁ : ℝ → H) (k : ℝ → ℝ → ℝ) (a : ℝ → ℝ)
    {γ c C εmax : ℝ}
    (hγ : 0 < γ) (hc : 0 < c) (hC : 0 < C)
    (hεmax : 0 < εmax) (hεmaxQuarter : εmax ≤ 1 / 4)
    (hetaTendsto : Tendsto (fun ε ↦ ‖R ε‖ ^ 2 * ‖U ε‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
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
          (4 * C ^ 2 + c ^ 2 / 4) * γ * onsetScale ε := by
  let datum : ℝ → OnsetDatum := fun ε ↦
    operatorOnsetDatum (ev ε) (R ε) (U ε) (K₀ ε) (K₁ ε)
  have hetaLt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖R ε‖ ^ 2 * ‖U ε‖ < 1 :=
    hetaTendsto.eventually (Iio_mem_nhds (by norm_num))
  have hrelative := relative_first_variation_of_scale
    (datum := datum) (γ := γ) (cF := c ^ 2 / 2) (Cm := 4 * C ^ 2)
    hγ (by positivity) (by positivity)
    (by simpa only [datum, operatorOnsetDatum] using hetaTendsto)
    (by
      filter_upwards [Ioo_mem_nhdsGT hεmax, hetaLt] with ε hεs hη
      rcases operatorOnsetDatum_core_of_logBoundary
        (ev ε) (R ε) (U ε) (K₀ ε) (K₁ ε) (k ε)
        hεs.1 (hεs.2.le.trans hεmaxQuarter) hγ.le hc.le hC.le
        (hrep ε) (hEq ε) hη (hUnorm ε) (heven ε)
        (hboundary ε hεs.1 hεs.2)
        (hoverlapInt ε hεs.1 hεs.2) (hnearInt ε hεs.1 hεs.2)
        (hfirstBridge ε hεs.1 hεs.2) (hmassBridge ε hεs.1 hεs.2) with
        ⟨hl, _hu, _hm0, hm, hr, hre⟩
      refine ⟨hεs.1, hεs.2.trans_le (hεmaxQuarter.trans (by norm_num)),
        hl, hm, ?_, hr, hre⟩
      dsimp only [datum, operatorOnsetDatum]
      positivity)
  refine ⟨?_, ?_⟩
  · simpa only [datum, operatorOnsetDatum] using hrelative
  · obtain ⟨εs, hεs, hεsmax, hscale⟩ := continuum_even_onset_from_operator_family
      ev R U K₀ K₁ k a hγ hc hC.le hεmax hεmaxQuarter hetaTendsto
      hrep hEq hUnorm heven hboundary hoverlapInt hnearInt hfirstBridge hmassBridge
    obtain ⟨εη, hεη, hηsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hetaLt
    refine ⟨min εs εη, lt_min hεs hεη, (min_le_left _ _).trans hεsmax, ?_⟩
    intro ε hε hcut
    have hεsCut : ε < εs := hcut.trans_le (min_le_left _ _)
    have hεmaxCut : ε < εmax := hεsCut.trans_le hεsmax
    have hη : ‖R ε‖ ^ 2 * ‖U ε‖ < 1 :=
      hηsub ⟨hε, hcut.trans_le (min_le_right _ _)⟩
    have hT : ‖metricOperator (R ε) (U ε)‖ < 1 :=
      (metricOperator_norm (R ε) (U ε)).trans_lt (by simpa [mul_comm] using hη)
    have hself := metricOperator_isSelfAdjoint (R ε) (U ε) (hUself ε)
    have hlog := logarithmic_boundary_to_onset_bounds hε
      (hεmaxCut.le.trans hεmaxQuarter) hγ.le hc.le hC.le
      (heven ε) (hboundary ε hε hεmaxCut)
      (hoverlapInt ε hε hεmaxCut) (hnearInt ε hε hεmaxCut)
    have hFpos : 0 < (-inner ℂ (K₀ ε)
        (metricOperator (R ε) (U ε) (K₀ ε))).re := by
      rw [hfirstBridge ε hε hεmaxCut]
      apply lt_of_lt_of_le _ hlog.1
      exact mul_pos (mul_pos (by positivity) hγ)
        (onsetScale_pos hε (hεmaxCut.trans_le (hεmaxQuarter.trans (by norm_num))))
    refine ⟨hFpos, ?_, ?_, (hscale ε hε hεsCut).2.1,
      (hscale ε hε hεsCut).2.2⟩
    · exact first_variation_le_kernel_diagonal_response_re
        (ev ε) (metricOperator (R ε) (U ε)) (K₀ ε) (K₁ ε)
        (hrep ε) hself hT (hEq ε)
    · exact kernel_diagonal_response_im_eq_zero
        (ev ε) (metricOperator (R ε) (U ε)) (K₀ ε) (K₁ ε)
        (hrep ε) hself hT (hEq ε)

end WeilKernelOnset
