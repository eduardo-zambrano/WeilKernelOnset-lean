import WeilKernelOnset.LogBoundary
import WeilKernelOnset.TwoMetric

/-!
# Direct onset from the mixed-kernel correlation

The revised proof bounds the exact diagonal response using the boundary
profiles of both kernels.  The support computation is an explicit bridge;
no compactness, operator-norm smallness, or Neumann expansion is required.
-/

open Set MeasureTheory
open scoped InnerProduct Interval

namespace WeilKernelOnset

/-- The exact mixed correlation, with the post-arrival kernel on the left
strip and the base kernel on the translated right strip.  Evenness turns the
left trace into the manuscript's right-boundary value `k₁ (a - s)`. -/
noncomputable def mixedOnsetOverlap (γ a ε : ℝ) (k₀ k₁ : ℝ → ℝ) : ℝ :=
  2 * γ * ∫ s in 0..(2 * ε),
    leftOnsetTrace k₁ a s * rightOnsetTrace k₀ a ε s

/-- Common a.e. logarithmic profiles for the two physical kernels give the
exact-response onset scale, without comparing the two kernels to each other. -/
theorem mixed_logarithmic_boundary_to_onset_bounds
    {k₀ k₁ : ℝ → ℝ} {γ c C a ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4)
    (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (heven₀ : ∀ᵐ x ∂volume, k₀ (-x) = k₀ x)
    (heven₁ : ∀ᵐ x ∂volume, k₁ (-x) = k₁ x)
    (hboundary₀ : HasAEBoundaryProfile boundaryProfile k₀ c C a (2 * ε))
    (hboundary₁ : HasAEBoundaryProfile boundaryProfile k₁ c C a (2 * ε))
    (hoverlapInt : IntervalIntegrable
      (fun s ↦ leftOnsetTrace k₁ a s * rightOnsetTrace k₀ a ε s)
      volume 0 (2 * ε)) :
    (c ^ 2 / 2) * γ * onsetScale ε ≤ mixedOnsetOverlap γ a ε k₀ k₁ ∧
      mixedOnsetOverlap γ a ε k₀ k₁ ≤ 4 * C ^ 2 * γ * onsetScale ε := by
  have hleft := (onsetTrace_profile_bounds_ae heven₁ hboundary₁).1
  have hright := (onsetTrace_profile_bounds_ae heven₀ hboundary₀).2
  have hprofile := boundaryProfile_product_integral_bounds hε hεq
  have hcompare := overlapIntegral_bounds_of_ae_profile hε.le hc hC
    (Filter.Eventually.of_forall boundaryProfile_nonneg) hleft hright
    (boundaryProfile_product_intervalIntegrable hε.le) hoverlapInt
  have hfactor : 0 ≤ 2 * γ := by positivity
  constructor
  · calc
      (c ^ 2 / 2) * γ * onsetScale ε =
          2 * γ * (c ^ 2 * (onsetScale ε / 4)) := by ring
      _ ≤ 2 * γ * (c ^ 2 *
          (∫ s in 0..(2 * ε), boundaryProfile s * boundaryProfile (2 * ε - s))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hprofile.1 (sq_nonneg c)) hfactor
      _ ≤ mixedOnsetOverlap γ a ε k₀ k₁ :=
        mul_le_mul_of_nonneg_left hcompare.1 hfactor
  · calc
      mixedOnsetOverlap γ a ε k₀ k₁ ≤ 2 * γ * (C ^ 2 *
          (∫ s in 0..(2 * ε), boundaryProfile s * boundaryProfile (2 * ε - s))) :=
        mul_le_mul_of_nonneg_left hcompare.2 hfactor
      _ ≤ 2 * γ * (C ^ 2 * (2 * onsetScale ε)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hprofile.2 (sq_nonneg C)) hfactor
      _ = 4 * C ^ 2 * γ * onsetScale ε := by ring

/-- The two Riesz identities and the exact physical support bridge turn the
mixed correlation bounds into a positive, two-sided diagonal onset law.
The boundary-profile and support hypotheses record the analytic inputs;
compactness is needed only for the separate relative first-variation result. -/
theorem diagonal_response_onset_of_mixed_logBoundary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ev : H →L[ℂ] ℂ) (T : H →L[ℂ] H) (K₀ K₁ : H)
    (k₀ k₁ : ℝ → ℝ) {γ c C a ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4)
    (hγ : 0 < γ) (hc : 0 < c) (hC : 0 ≤ C)
    (hrep₀ : ∀ f : H, ev f = inner ℂ K₀ f)
    (hrep₁ : ∀ f : H, ev f = inner ℂ K₁ f + inner ℂ (T K₁) f)
    (heven₀ : ∀ᵐ x ∂volume, k₀ (-x) = k₀ x)
    (heven₁ : ∀ᵐ x ∂volume, k₁ (-x) = k₁ x)
    (hboundary₀ : HasAEBoundaryProfile boundaryProfile k₀ c C a (2 * ε))
    (hboundary₁ : HasAEBoundaryProfile boundaryProfile k₁ c C a (2 * ε))
    (hoverlapInt : IntervalIntegrable
      (fun s ↦ leftOnsetTrace k₁ a s * rightOnsetTrace k₀ a ε s)
      volume 0 (2 * ε))
    (hmixedBridge : (-inner ℂ K₀ (T K₁)).re = mixedOnsetOverlap γ a ε k₀ k₁) :
    0 < (ev K₁ - ev K₀).re ∧
      (c ^ 2 / 2) * γ * onsetScale ε ≤ (ev K₁ - ev K₀).re ∧
      (ev K₁ - ev K₀).re ≤ 4 * C ^ 2 * γ * onsetScale ε := by
  have hEq : (1 + T) K₁ = K₀ :=
    twoMetric_kernel_identity T K₀ K₁ (fun f ↦ by rw [← hrep₀ f]; exact hrep₁ f)
  have hresponse : (ev K₁ - ev K₀).re = mixedOnsetOverlap γ a ε k₀ k₁ := by
    rw [mixed_kernel_difference ev T K₀ K₁ hrep₀ hEq, hmixedBridge]
  have hbounds := mixed_logarithmic_boundary_to_onset_bounds hε hεq hγ.le hc.le hC
    heven₀ heven₁ hboundary₀ hboundary₁ hoverlapInt
  rw [hresponse]
  refine ⟨?_, hbounds.1, hbounds.2⟩
  have hscale : 0 < onsetScale ε := onsetScale_pos hε (hεq.trans_lt (by norm_num))
  exact (mul_pos (mul_pos (div_pos (sq_pos_of_pos hc) (by norm_num)) hγ)
    hscale).trans_le hbounds.1

end WeilKernelOnset
