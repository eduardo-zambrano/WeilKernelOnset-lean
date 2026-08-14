import WeilKernelOnset.BoundaryProfile
import WeilKernelOnset.BoundaryCorrelation

/-!
# The logarithmic boundary input at onset scale

This module specializes the a.e. boundary-correlation bridge to the exact
square-root logarithmic profile.  It converts the potential-theoretic input
into explicit first-order and strip-mass estimates at the scale
`ε / log (1 / ε)`.
-/

open Set MeasureTheory
open scoped Interval

namespace WeilKernelOnset

/-- An a.e. two-sided logarithmic boundary estimate implies the precise
order bounds needed in the even onset argument. -/
theorem logarithmic_boundary_to_onset_bounds
    {k : ℝ → ℝ} {γ c C a ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4)
    (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (heven : ∀ᵐ x ∂volume, k (-x) = k x)
    (hboundary : HasAEBoundaryProfile boundaryProfile k c C a (2 * ε))
    (hoverlapInt : IntervalIntegrable
      (fun s ↦ leftOnsetTrace k a s * rightOnsetTrace k a ε s)
      volume 0 (2 * ε))
    (hnearInt : IntervalIntegrable (fun d ↦ k (a - d) ^ 2)
      volume 0 (2 * ε)) :
    (c ^ 2 / 2) * γ * onsetScale ε ≤ firstOrderOverlap γ a ε k ∧
      firstOrderOverlap γ a ε k ≤ 4 * C ^ 2 * γ * onsetScale ε ∧
      (c ^ 2 / 2) * onsetScale ε ≤ boundaryStripMass a ε k ∧
      boundaryStripMass a ε k ≤ 4 * C ^ 2 * onsetScale ε := by
  have hraw := boundaryProfile_to_firstOrder_and_mass
    (b := boundaryProfile) (k := k) (γ := γ) (c := c) (C := C)
    (a := a) (ε := ε) hε.le hγ hc hC
    (boundaryProfile_monotoneOn.mono (fun _ hx ↦ hx.1))
    (fun x _ ↦ boundaryProfile_nonneg x) heven hboundary
    (boundaryProfile_product_intervalIntegrable hε.le)
    (boundaryProfile_sq_intervalIntegrable hε.le) hoverlapInt hnearInt
  have hhalfScale : onsetScale ε / 4 ≤
      ε * boundaryProfile (ε / 2) ^ 2 := by
    calc
      onsetScale ε / 4 = ε * (1 / (4 * Real.log (1 / ε))) := by
        unfold onsetScale
        ring
      _ ≤ ε * boundaryProfile (ε / 2) ^ 2 := by
        gcongr
        exact one_div_four_log_le_boundaryProfile_half_sq hε hεq
  have hhalfLe : boundaryProfile (ε / 2) ≤ boundaryProfile ε := by
    apply boundaryProfile_monotoneOn
    · exact mem_Ici.mpr (by linarith)
    · exact mem_Ici.mpr hε.le
    · linarith
  have hhalfSqLe : boundaryProfile (ε / 2) ^ 2 ≤ boundaryProfile ε ^ 2 := by
    nlinarith [boundaryProfile_nonneg (ε / 2), boundaryProfile_nonneg ε]
  have hepsScale : onsetScale ε / 4 ≤ ε * boundaryProfile ε ^ 2 :=
    hhalfScale.trans (mul_le_mul_of_nonneg_left hhalfSqLe hε.le)
  have htopScale : 2 * ε * boundaryProfile (2 * ε) ^ 2 ≤
      2 * onsetScale ε := by
    calc
      2 * ε * boundaryProfile (2 * ε) ^ 2 ≤
          2 * ε * (1 / Real.log (1 / ε)) := by
        gcongr
        exact boundaryProfile_two_mul_sq_le hε hεq
      _ = 2 * onsetScale ε := by
        unfold onsetScale
        ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (c ^ 2 / 2) * γ * onsetScale ε =
          2 * γ * (c ^ 2 * (onsetScale ε / 4)) := by ring
      _ ≤ 2 * γ * (c ^ 2 *
          (ε * boundaryProfile (ε / 2) ^ 2)) := by gcongr
      _ ≤ firstOrderOverlap γ a ε k := hraw.1
  · calc
      firstOrderOverlap γ a ε k ≤
          2 * γ * (C ^ 2 *
            (2 * ε * boundaryProfile (2 * ε) ^ 2)) := hraw.2.1
      _ ≤ 2 * γ * (C ^ 2 * (2 * onsetScale ε)) := by gcongr
      _ = 4 * C ^ 2 * γ * onsetScale ε := by ring
  · calc
      (c ^ 2 / 2) * onsetScale ε =
          2 * (c ^ 2 * (onsetScale ε / 4)) := by ring
      _ ≤ 2 * (c ^ 2 * (ε * boundaryProfile ε ^ 2)) := by gcongr
      _ ≤ boundaryStripMass a ε k := hraw.2.2.1
  · calc
      boundaryStripMass a ε k ≤
          2 * (C ^ 2 * (2 * ε * boundaryProfile (2 * ε) ^ 2)) :=
        hraw.2.2.2
      _ ≤ 2 * (C ^ 2 * (2 * onsetScale ε)) := by gcongr
      _ = 4 * C ^ 2 * onsetScale ε := by ring

end WeilKernelOnset
