import WeilKernelOnset.KernelResponse
import WeilKernelOnset.LogBoundary
import WeilKernelOnset.Onset

/-!
# Assembly of the formal onset mechanism

This file is the executable trust boundary of the companion.  The two named
bridges identify the physical overlap and strip mass with their Hilbert-space
operator expressions.  From those bridges, the a.e. logarithmic boundary
input, and compact-localization smallness, Lean derives every scalar hypothesis
used by the final onset theorem.
-/

open Set MeasureTheory
open scoped InnerProduct Interval

namespace WeilKernelOnset

open Filter
open scoped Topology

/-- The scalar onset data extracted from a factorized Hilbert-space
perturbation.  Real parts are used because mathlib's operator layer is complex,
whereas the even-sector response is real and ordered. -/
noncomputable def operatorOnsetDatum {H P : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (ev : H →L[ℂ] ℂ) (R : H →L[ℂ] P) (U : P →L[ℂ] P)
    (K₀ K₁ : H) : OnsetDatum where
  firstOrder := (-inner ℂ K₀ (metricOperator R U K₀)).re
  stripMass := ‖R K₀‖ ^ 2
  eta := ‖R‖ ^ 2 * ‖U‖
  remainder := (neumannRemainder (metricOperator R U) K₀).re
  response := (ev K₁ - ev K₀).re

/-- Exact response decomposition and the complete nonlinear bound for the
operator-derived datum. -/
theorem operatorOnsetDatum_response
    {H P : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [Nontrivial P]
    (ev : H →L[ℂ] ℂ) (R : H →L[ℂ] P) (U : P →L[ℂ] P)
    (K₀ K₁ : H) {γ : ℝ}
    (hrep : ∀ f : H, ev f = inner ℂ K₀ f)
    (hEq : (1 + metricOperator R U) K₁ = K₀)
    (hη : ‖R‖ ^ 2 * ‖U‖ < 1) (hUnorm : ‖U‖ = γ) :
    (operatorOnsetDatum ev R U K₀ K₁).response =
        (operatorOnsetDatum ev R U K₀ K₁).firstOrder +
          (operatorOnsetDatum ev R U K₀ K₁).remainder ∧
      |(operatorOnsetDatum ev R U K₀ K₁).remainder| ≤
        γ * ((operatorOnsetDatum ev R U K₀ K₁).eta /
          (1 - (operatorOnsetDatum ev R U K₀ K₁).eta)) *
          (operatorOnsetDatum ev R U K₀ K₁).stripMass := by
  rcases factorized_kernel_response ev R U K₀ K₁ hrep hEq hη with ⟨hid, hrem⟩
  constructor
  · simp only [operatorOnsetDatum]
    rw [hid]
    simp
  · simp only [operatorOnsetDatum]
    calc
      |(neumannRemainder (metricOperator R U) K₀).re| ≤
          ‖neumannRemainder (metricOperator R U) K₀‖ := Complex.abs_re_le_norm _
      _ ≤ ‖U‖ * (‖R‖ ^ 2 * ‖U‖) /
          (1 - ‖R‖ ^ 2 * ‖U‖) * ‖R K₀‖ ^ 2 := hrem
      _ = γ * ((‖R‖ ^ 2 * ‖U‖) /
          (1 - (‖R‖ ^ 2 * ‖U‖))) * ‖R K₀‖ ^ 2 := by
        rw [hUnorm]
        ring

/-- One-width assembly theorem.  The only paper-specific interfaces are the
a.e. boundary estimate and the two exact support-identification bridges. -/
theorem operatorOnsetDatum_core_of_logBoundary
    {H P : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [Nontrivial P]
    (ev : H →L[ℂ] ℂ) (R : H →L[ℂ] P) (U : P →L[ℂ] P)
    (K₀ K₁ : H) (k : ℝ → ℝ) {γ c C a ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4)
    (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hrep : ∀ f : H, ev f = inner ℂ K₀ f)
    (hEq : (1 + metricOperator R U) K₁ = K₀)
    (hη : ‖R‖ ^ 2 * ‖U‖ < 1) (hUnorm : ‖U‖ = γ)
    (heven : ∀ᵐ x ∂volume, k (-x) = k x)
    (hboundary : HasAEBoundaryProfile boundaryProfile k c C a (2 * ε))
    (hoverlapInt : IntervalIntegrable
      (fun s ↦ leftOnsetTrace k a s * rightOnsetTrace k a ε s)
      volume 0 (2 * ε))
    (hnearInt : IntervalIntegrable (fun d ↦ k (a - d) ^ 2)
      volume 0 (2 * ε))
    (hfirstBridge :
      (-inner ℂ K₀ (metricOperator R U K₀)).re = firstOrderOverlap γ a ε k)
    (hmassBridge : ‖R K₀‖ ^ 2 = boundaryStripMass a ε k) :
    let d := operatorOnsetDatum ev R U K₀ K₁
    (c ^ 2 / 2) * γ * onsetScale ε ≤ d.firstOrder ∧
      d.firstOrder ≤ 4 * C ^ 2 * γ * onsetScale ε ∧
      0 ≤ d.stripMass ∧ d.stripMass ≤ 4 * C ^ 2 * onsetScale ε ∧
      d.response = d.firstOrder + d.remainder ∧
      |d.remainder| ≤ γ * (d.eta / (1 - d.eta)) * d.stripMass := by
  have hlog := logarithmic_boundary_to_onset_bounds hε hεq hγ hc hC
    heven hboundary hoverlapInt hnearInt
  have hresponse := operatorOnsetDatum_response ev R U K₀ K₁
    hrep hEq hη hUnorm
  dsimp only [operatorOnsetDatum]
  refine ⟨?_, ?_, sq_nonneg _, ?_, hresponse.1, hresponse.2⟩
  · rw [hfirstBridge]
    exact hlog.1
  · rw [hfirstBridge]
    exact hlog.2.1
  · rw [hmassBridge]
    exact hlog.2.2.2

/-- Family-level assembly: the a.e. logarithmic boundary input, the exact
support bridges, and norm-null compact localization imply a positive
two-sided continuum onset law after shrinking the cutoff. -/
theorem continuum_even_onset_from_operator_family
    {H P : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [Nontrivial P]
    (ev : ℝ → H →L[ℂ] ℂ) (R : ℝ → H →L[ℂ] P) (U : ℝ → P →L[ℂ] P)
    (K₀ K₁ : ℝ → H) (k : ℝ → ℝ → ℝ) (a : ℝ → ℝ)
    {γ c C εmax : ℝ}
    (hγ : 0 < γ) (hc : 0 < c) (hC : 0 ≤ C)
    (hεmax : 0 < εmax) (hεmaxQuarter : εmax ≤ 1 / 4)
    (hetaTendsto : Tendsto (fun ε ↦ ‖R ε‖ ^ 2 * ‖U ε‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hrep : ∀ ε f, ev ε f = inner ℂ (K₀ ε) f)
    (hEq : ∀ ε, (1 + metricOperator (R ε) (U ε)) (K₁ ε) = K₀ ε)
    (hUnorm : ∀ ε, ‖U ε‖ = γ)
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
    ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ εmax ∧
      ∀ ε, 0 < ε → ε < ε₀ →
        0 < (ev ε (K₁ ε) - ev ε (K₀ ε)).re ∧
          (c ^ 2 / 4) * γ * onsetScale ε ≤
            (ev ε (K₁ ε) - ev ε (K₀ ε)).re ∧
          (ev ε (K₁ ε) - ev ε (K₀ ε)).re ≤
            (4 * C ^ 2 + c ^ 2 / 4) * γ * onsetScale ε := by
  let datum : ℝ → OnsetDatum := fun ε ↦
    operatorOnsetDatum (ev ε) (R ε) (U ε) (K₀ ε) (K₁ ε)
  have hetaDatum : Tendsto (fun ε ↦ (datum ε).eta)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [datum, operatorOnsetDatum] using hetaTendsto
  have hetaLtOne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (datum ε).eta < 1 :=
    hetaDatum.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨εη, hεη, hηsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hetaLtOne
  let εbase := min εmax εη
  have hεbase : 0 < εbase := lt_min hεmax hεη
  have hεbaseMax : εbase ≤ εmax := min_le_left _ _
  have hεbaseOne : εbase ≤ 1 :=
    hεbaseMax.trans (hεmaxQuarter.trans (by norm_num))
  have hfinal := continuum_even_onset_of_eta_tendsto
    (datum := datum) (γ := γ) (cF := c ^ 2 / 2)
    (CF := 4 * C ^ 2) (Cm := 4 * C ^ 2) (εmax := εbase)
    hγ.le (by positivity) hεbase hεbaseOne
    (fun ε _ _ ↦ by
      dsimp only [datum, operatorOnsetDatum]
      positivity)
    hetaDatum
    (fun ε hε hεcut ↦ by
      have hεMaxCut : ε < εmax := hεcut.trans_le hεbaseMax
      have hεEtaCut : ε < εη := hεcut.trans_le (min_le_right _ _)
      have hη : ‖R ε‖ ^ 2 * ‖U ε‖ < 1 :=
        hηsub ⟨hε, hεEtaCut⟩
      simpa only [datum] using
        operatorOnsetDatum_core_of_logBoundary
          (ev ε) (R ε) (U ε) (K₀ ε) (K₁ ε) (k ε)
          hε (hεMaxCut.le.trans hεmaxQuarter) hγ.le hc.le hC
          (hrep ε) (hEq ε) hη (hUnorm ε) (heven ε)
          (hboundary ε hε hεMaxCut)
          (hoverlapInt ε hε hεMaxCut) (hnearInt ε hε hεMaxCut)
          (hfirstBridge ε hε hεMaxCut) (hmassBridge ε hε hεMaxCut))
  rcases hfinal with ⟨ε₀, hε₀, hε₀base, hout⟩
  refine ⟨ε₀, hε₀, hε₀base.trans hεbaseMax, ?_⟩
  intro ε hε hεcut
  have hbounds := hout ε hε hεcut
  have hεOne : ε < 1 := hεcut.trans_le
    (hε₀base.trans (hεbaseMax.trans
      (hεmaxQuarter.trans (by norm_num))))
  have hlowerPos : 0 < (c ^ 2 / 4) * γ * onsetScale ε := by
    exact mul_pos (mul_pos (div_pos (sq_pos_of_pos hc) (by norm_num)) hγ)
      (onsetScale_pos hε hεOne)
  refine ⟨?_, ?_, ?_⟩
  · exact hlowerPos.trans_le (by
      simpa only [datum, operatorOnsetDatum,
        show (c ^ 2 / 2) / 2 = c ^ 2 / 4 by ring] using hbounds.1)
  · simpa only [datum, operatorOnsetDatum,
      show (c ^ 2 / 2) / 2 = c ^ 2 / 4 by ring] using hbounds.1
  · simpa only [datum, operatorOnsetDatum,
      show (c ^ 2 / 2) / 2 = c ^ 2 / 4 by ring] using hbounds.2

end WeilKernelOnset
