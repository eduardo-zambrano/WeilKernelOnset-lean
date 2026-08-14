import WeilKernelOnset.CompactLocalization
import WeilKernelOnset.LogScale

/-!
# Explicit remainder absorption and the conditional onset law

This file isolates the final quantitative step of Theorem 8.2.  The hypotheses
are exactly the outputs of the boundary-correlation and compact-localization
arguments: two-sided first-order control, strip-mass control, the exact response
decomposition, and a geometric nonlinear remainder.
-/

namespace WeilKernelOnset

open Filter Set
open scoped Topology

/-- Scalar data at one positive onset width.  Keeping this structure scalar
makes the dependency boundary explicit and prevents any hidden analytic axiom. -/
structure OnsetDatum where
  firstOrder : ℝ
  stripMass : ℝ
  eta : ℝ
  remainder : ℝ
  response : ℝ

/-- Explicit one-width remainder absorption.  This is the final logical step in
Theorem 8.2, with no asymptotic notation hidden in the statement. -/
theorem absorb_nonlinear_remainder
    {γ s cF CF Cm : ℝ} (d : OnsetDatum)
    (hγ : 0 ≤ γ) (hs : 0 ≤ s)
    (hfirstLower : cF * γ * s ≤ d.firstOrder)
    (hfirstUpper : d.firstOrder ≤ CF * γ * s)
    (hmass : d.stripMass ≤ Cm * s)
    (heta0 : 0 ≤ d.eta) (heta1 : d.eta < 1)
    (hresponse : d.response = d.firstOrder + d.remainder)
    (hremainder : |d.remainder| ≤ γ * (d.eta / (1 - d.eta)) * d.stripMass)
    (hsmall : (d.eta / (1 - d.eta)) * Cm ≤ cF / 2) :
    (cF / 2) * γ * s ≤ d.response ∧
      d.response ≤ (CF + cF / 2) * γ * s := by
  have hden : 0 < 1 - d.eta := sub_pos.mpr heta1
  have hratio0 : 0 ≤ d.eta / (1 - d.eta) := div_nonneg heta0 hden.le
  have hremScale : |d.remainder| ≤ (cF / 2) * γ * s := by
    calc
      |d.remainder| ≤ γ * (d.eta / (1 - d.eta)) * d.stripMass := hremainder
      _ ≤ γ * (d.eta / (1 - d.eta)) * (Cm * s) := by
        gcongr
      _ = ((d.eta / (1 - d.eta)) * Cm) * γ * s := by ring
      _ ≤ (cF / 2) * γ * s := by gcongr
  constructor
  · rw [hresponse]
    have hremLower : -(cF / 2 * γ * s) ≤ d.remainder :=
      (neg_le_of_abs_le hremScale)
    linarith
  · rw [hresponse]
    have hremUpper : d.remainder ≤ cF / 2 * γ * s :=
      (le_of_abs_le hremScale)
    nlinarith

/-- Uniform conditional onset theorem with explicit constants and cutoff.  It
corresponds to Theorem 8.2 once the analytic construction supplies `datum` and
the hypotheses below for every sufficiently small `ε`. -/
theorem continuum_even_onset
    {γ cF CF Cm ε₀ : ℝ} (datum : ℝ → OnsetDatum)
    (hγ : 0 ≤ γ)
    (hε₀ : 0 < ε₀) (hε₀one : ε₀ ≤ 1)
    (hdata : ∀ ε, 0 < ε → ε < ε₀ →
      let d := datum ε
      cF * γ * onsetScale ε ≤ d.firstOrder ∧
      d.firstOrder ≤ CF * γ * onsetScale ε ∧
      0 ≤ d.stripMass ∧ d.stripMass ≤ Cm * onsetScale ε ∧
      0 ≤ d.eta ∧ d.eta < 1 ∧
      d.response = d.firstOrder + d.remainder ∧
      |d.remainder| ≤ γ * (d.eta / (1 - d.eta)) * d.stripMass ∧
      (d.eta / (1 - d.eta)) * Cm ≤ cF / 2) :
    0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      (cF / 2) * γ * onsetScale ε ≤ (datum ε).response ∧
      (datum ε).response ≤ (CF + cF / 2) * γ * onsetScale ε := by
  refine ⟨hε₀, ?_⟩
  intro ε hε hεcut
  have hε1 : ε < 1 := lt_of_lt_of_le hεcut hε₀one
  rcases hdata ε hε hεcut with
    ⟨hfirstLower, hfirstUpper, _hmass0, hmass, heta0, heta1,
      hresponse, hremainder, hsmall⟩
  exact absorb_nonlinear_remainder (datum ε) hγ (onsetScale_nonneg hε hε1)
    hfirstLower hfirstUpper hmass heta0 heta1
    hresponse hremainder hsmall

/-- Asymptotic form of the onset theorem.  Compact localization naturally
produces `eta ε → 0`; this theorem extracts a smaller positive cutoff on which
the complete nonlinear remainder can be absorbed. -/
theorem continuum_even_onset_of_eta_tendsto
    {γ cF CF Cm εmax : ℝ} (datum : ℝ → OnsetDatum)
    (hγ : 0 ≤ γ) (hcF : 0 < cF)
    (hεmax : 0 < εmax) (hεmaxOne : εmax ≤ 1)
    (hetaNonneg : ∀ ε, 0 < ε → ε < εmax → 0 ≤ (datum ε).eta)
    (hetaTendsto : Tendsto (fun ε ↦ (datum ε).eta)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcore : ∀ ε, 0 < ε → ε < εmax →
      let d := datum ε
      cF * γ * onsetScale ε ≤ d.firstOrder ∧
      d.firstOrder ≤ CF * γ * onsetScale ε ∧
      0 ≤ d.stripMass ∧ d.stripMass ≤ Cm * onsetScale ε ∧
      d.response = d.firstOrder + d.remainder ∧
      |d.remainder| ≤ γ * (d.eta / (1 - d.eta)) * d.stripMass) :
    ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ εmax ∧
      ∀ ε, 0 < ε → ε < ε₀ →
        (cF / 2) * γ * onsetScale ε ≤ (datum ε).response ∧
        (datum ε).response ≤ (CF + cF / 2) * γ * onsetScale ε := by
  have hratio : Tendsto
      (fun ε ↦ (datum ε).eta / (1 - (datum ε).eta) * Cm)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hg : ContinuousAt (fun x : ℝ ↦ x / (1 - x) * Cm) 0 := by
      exact (continuousAt_id.div
        (continuousAt_const.sub continuousAt_id) (by norm_num)).mul continuousAt_const
    simpa using hg.tendsto.comp hetaTendsto
  have hetaLtOne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (datum ε).eta < 1 :=
    hetaTendsto.eventually (Iio_mem_nhds (by norm_num))
  have hratioSmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (datum ε).eta / (1 - (datum ε).eta) * Cm < cF / 2 :=
    hratio.eventually (Iio_mem_nhds (by linarith))
  have heventual :
      {ε | (datum ε).eta < 1 ∧
        (datum ε).eta / (1 - (datum ε).eta) * Cm < cF / 2} ∈
        𝓝[>] (0 : ℝ) := hetaLtOne.and hratioSmall
  obtain ⟨εη, hεη, hηsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp heventual
  let ε₀ := min εmax εη
  have hε₀ : 0 < ε₀ := lt_min hεmax hεη
  refine ⟨ε₀, hε₀, min_le_left _ _, ?_⟩
  intro ε hε hεcut
  have hεmaxCut : ε < εmax := hεcut.trans_le (min_le_left _ _)
  have hεηCut : ε < εη := hεcut.trans_le (min_le_right _ _)
  have hsmallData := hηsub ⟨hε, hεηCut⟩
  rcases hcore ε hε hεmaxCut with
    ⟨hfirstLower, hfirstUpper, _hmass0, hmass, hresponse, hremainder⟩
  exact absorb_nonlinear_remainder (datum ε) hγ
    (onsetScale_nonneg hε (hεmaxCut.trans_le hεmaxOne))
    hfirstLower hfirstUpper hmass (hetaNonneg ε hε hεmaxCut)
    hsmallData.1 hresponse hremainder hsmallData.2.le

end WeilKernelOnset
