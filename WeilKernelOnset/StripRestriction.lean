import WeilKernelOnset.CompactStrong
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Restriction to shrinking endpoint strips

This file supplies the concrete strong-null family used in the compact
localization argument.  Its codomain retains the restricted measure, so no
noncanonical identification of the varying `L²` spaces is needed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace WeilKernelOnset

/-- The fixed physical Hilbert space. -/
abbrev PhysicalL2 := ↥(Lp ℂ 2 (volume : Measure ℝ))

/-- The union of the closed `ε`-neighborhoods of two finite endpoints. -/
def endpointStrips (a b ε : ℝ) : Set ℝ :=
  Icc (a - ε) (a + ε) ∪ Icc (b - ε) (b + ε)

theorem measurableSet_endpointStrips (a b ε : ℝ) :
    MeasurableSet (endpointStrips a b ε) := by
  exact measurableSet_Icc.union measurableSet_Icc

/-- Each endpoint contributes length at most `2ε`. -/
theorem volume_endpointStrips_le {a b ε : ℝ} (hε : 0 ≤ ε) :
    (volume : Measure ℝ) (endpointStrips a b ε) ≤ ENNReal.ofReal (4 * ε) := by
  calc
    (volume : Measure ℝ) (endpointStrips a b ε)
        ≤ (volume : Measure ℝ) (Icc (a - ε) (a + ε)) +
            (volume : Measure ℝ) (Icc (b - ε) (b + ε)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * ε) + ENNReal.ofReal (2 * ε) := by
      simp only [Real.volume_Icc]
      congr 1 <;> ring_nf
    _ = ENNReal.ofReal (4 * ε) := by
      rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hε)
        (mul_nonneg (by norm_num) hε)]
      congr 1
      ring

/-- The volume of the two endpoint strips tends to zero with their radius. -/
theorem tendsto_volume_endpointStrips (a b : ℝ) :
    Tendsto (fun ε : ℝ ↦ (volume : Measure ℝ) (endpointStrips a b ε))
      (𝓝[>] 0) (𝓝 0) := by
  have hupper : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (4 * ε))
      (𝓝[>] 0) (𝓝 0) := by
    have hfull : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (4 * ε))
        (𝓝 0) (𝓝 0) := by
      have hm : Tendsto (fun ε : ℝ ↦ 4 * ε) (𝓝 0) (𝓝 0) := by
        simpa using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ ↦ (4 : ℝ)) (𝓝 0) (𝓝 4)).mul
            (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0))
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hm
    exact hfull.mono_left inf_le_left
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ ↦ (0 : ℝ≥0∞)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    hupper
  · exact Eventually.of_forall fun _ ↦ zero_le _
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact volume_endpointStrips_le hε.le

/-- Restriction from the fixed physical space to the `L²` space carrying the
restricted strip measure. -/
noncomputable def endpointStripRestriction (a b ε : ℝ) :
    PhysicalL2 →L[ℂ]
      ↥(Lp ℂ 2 ((volume : Measure ℝ).restrict (endpointStrips a b ε))) :=
  LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (endpointStrips a b ε)

theorem endpointStripRestriction_apply_norm_le (a b ε : ℝ) (f : PhysicalL2) :
    ‖endpointStripRestriction a b ε f‖ ≤ ‖f‖ := by
  exact norm_Lp_toLp_restrict_le (endpointStrips a b ε) f

theorem endpointStripRestriction_opNorm_le (a b ε : ℝ) :
    ‖endpointStripRestriction a b ε‖ ≤ 1 := by
  apply (endpointStripRestriction a b ε).opNorm_le_bound zero_le_one
  intro f
  simpa using endpointStripRestriction_apply_norm_le a b ε f

/-- Restriction of each fixed physical `L²` vector to the shrinking endpoint
strips converges to zero in norm. -/
theorem tendsto_endpointStripRestriction_norm (a b : ℝ) (f : PhysicalL2) :
    Tendsto (fun ε : ℝ ↦ ‖endpointStripRestriction a b ε f‖)
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hsmall⟩ :=
    (Lp.memLp f).eLpNorm_indicator_le (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) (half_pos hη)
  have hmeasure : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (volume : Measure ℝ) (endpointStrips a b ε) ≤ ENNReal.ofReal δ := by
    have ht := (tendsto_volume_endpointStrips a b).eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.2 hδ))
    exact ht.mono fun _ h ↦ h.le
  filter_upwards [hmeasure] with ε hεmeasure
  have hseminorm :
      eLpNorm ((endpointStrips a b ε).indicator (fun x ↦ f x)) 2 volume ≤
        ENNReal.ofReal (η / 2) :=
    hsmall (endpointStrips a b ε) (measurableSet_endpointStrips a b ε) hεmeasure
  have hnorm : ‖endpointStripRestriction a b ε f‖ ≤ η / 2 := by
    have hrestricted :
        eLpNorm (fun x ↦ f x) 2
            ((volume : Measure ℝ).restrict (endpointStrips a b ε)) ≤
          ENNReal.ofReal (η / 2) := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict
        (measurableSet_endpointStrips a b ε)]
      exact hseminorm
    unfold endpointStripRestriction
    rw [Lp.norm_def,
      eLpNorm_congr_ae (LpToLpRestrictCLM_coeFn ℂ (endpointStrips a b ε) f)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hrestricted).trans_eq
      (ENNReal.toReal_ofReal (half_pos hη).le)
  have hnormlt : ‖endpointStripRestriction a b ε f‖ < η :=
    hnorm.trans_lt (half_lt_self hη)
  simpa [Real.dist_eq] using hnormlt

/-- Lemma 7.3 in its concrete fixed-horizon form: after any compact physical
embedding, restriction to the shrinking endpoint strips is norm-null. -/
theorem tendsto_endpointStripRestriction_compact_opNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E →L[ℂ] PhysicalL2) (hJ : IsCompactOperator J) (a b : ℝ) :
    Tendsto
      (fun ε : ℝ ↦ ‖endpointStripRestriction a b ε ∘L J‖)
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_opNorm_compact_of_strong_norm J hJ
    (fun ε ↦ endpointStripRestriction a b ε) 1 zero_le_one
    (fun ε ↦ endpointStripRestriction_opNorm_le a b ε)
    (tendsto_endpointStripRestriction_norm a b)

end WeilKernelOnset
