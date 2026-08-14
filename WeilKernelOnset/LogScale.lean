import WeilKernelOnset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Logarithmic strip estimates

The two sandwich lemmas are the order-theoretic heart of Lemma 8.1.  They are
stated for an arbitrary nonnegative monotone boundary profile, so they can be
reused when the potential-theoretic boundary input is instantiated.
-/

open Set MeasureTheory
open scoped Interval

namespace WeilKernelOnset

theorem square_strip_sandwich (b : ℝ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hbmono : MonotoneOn b (Icc 0 (2 * ε)))
    (hbnonneg : ∀ x ∈ Icc 0 (2 * ε), 0 ≤ b x)
    (hint : IntervalIntegrable (fun x ↦ b x ^ 2) volume 0 (2 * ε)) :
    ε * b ε ^ 2 ≤ (∫ x in 0..(2 * ε), b x ^ 2) ∧
      (∫ x in 0..(2 * ε), b x ^ 2) ≤ 2 * ε * b (2 * ε) ^ 2 := by
  have hε_mem : ε ∈ Icc 0 (2 * ε) := by constructor <;> linarith
  have h2ε_mem : 2 * ε ∈ Icc 0 (2 * ε) := by constructor <;> linarith
  constructor
  · have hsub : IntervalIntegrable (fun x ↦ b x ^ 2) volume ε (2 * ε) := by
      apply hint.mono_set
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc hε le_rfl
    calc
      ε * b ε ^ 2 = ∫ _x in ε..(2 * ε), b ε ^ 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ x in ε..(2 * ε), b x ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hsub
        intro x hx
        have hxfull : x ∈ Icc 0 (2 * ε) := ⟨hε.trans hx.1, hx.2⟩
        have hbx := hbmono hε_mem hxfull hx.1
        have hbε := hbnonneg ε hε_mem
        nlinarith [sq_nonneg (b x - b ε)]
      _ ≤ ∫ x in 0..(2 * ε), b x ^ 2 := by
        apply intervalIntegral.integral_mono_interval hε (by linarith) le_rfl
        · filter_upwards [] with x
          exact sq_nonneg (b x)
        · exact hint
  · calc
      (∫ x in 0..(2 * ε), b x ^ 2) ≤ ∫ _x in 0..(2 * ε), b (2 * ε) ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
        intro x hx
        have hbx := hbmono hx h2ε_mem hx.2
        have hx0 := hbnonneg x hx
        nlinarith [sq_nonneg (b (2 * ε) - b x)]
      _ = 2 * ε * b (2 * ε) ^ 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

theorem product_strip_sandwich (b : ℝ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hbmono : MonotoneOn b (Icc 0 (2 * ε)))
    (hbnonneg : ∀ x ∈ Icc 0 (2 * ε), 0 ≤ b x)
    (hint : IntervalIntegrable (fun x ↦ b x * b (2 * ε - x)) volume 0 (2 * ε)) :
    ε * b (ε / 2) ^ 2 ≤ (∫ x in 0..(2 * ε), b x * b (2 * ε - x)) ∧
      (∫ x in 0..(2 * ε), b x * b (2 * ε - x)) ≤
        2 * ε * b (2 * ε) ^ 2 := by
  have hhalf_mem : ε / 2 ∈ Icc 0 (2 * ε) := by constructor <;> linarith
  have h2ε_mem : 2 * ε ∈ Icc 0 (2 * ε) := by constructor <;> linarith
  have hprod_nonneg : ∀ x ∈ Icc 0 (2 * ε), 0 ≤ b x * b (2 * ε - x) := by
    intro x hx
    exact mul_nonneg (hbnonneg x hx)
      (hbnonneg (2 * ε - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  constructor
  · have hsub : IntervalIntegrable (fun x ↦ b x * b (2 * ε - x)) volume
        (ε / 2) (3 * ε / 2) := by
      apply hint.mono_set
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc (by linarith) (by linarith)
    calc
      ε * b (ε / 2) ^ 2 = ∫ _x in (ε / 2)..(3 * ε / 2), b (ε / 2) ^ 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ x in (ε / 2)..(3 * ε / 2), b x * b (2 * ε - x) := by
        apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hsub
        intro x hx
        have hxfull : x ∈ Icc 0 (2 * ε) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hreflect : 2 * ε - x ∈ Icc 0 (2 * ε) :=
          ⟨by linarith [hx.2], by linarith [hx.1]⟩
        have hleft := hbmono hhalf_mem hxfull (by linarith [hx.1])
        have hright := hbmono hhalf_mem hreflect (by linarith [hx.2])
        have hbhalf := hbnonneg (ε / 2) hhalf_mem
        nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright)]
      _ ≤ ∫ x in 0..(2 * ε), b x * b (2 * ε - x) := by
        apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact hprod_nonneg x ⟨hx.1.le, hx.2⟩
        · exact hint
  · calc
      (∫ x in 0..(2 * ε), b x * b (2 * ε - x)) ≤
          ∫ _x in 0..(2 * ε), b (2 * ε) ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
        intro x hx
        have hreflect : 2 * ε - x ∈ Icc 0 (2 * ε) :=
          ⟨by linarith [hx.2], by linarith [hx.1]⟩
        have hleft := hbmono hx h2ε_mem hx.2
        have hright := hbmono hreflect h2ε_mem (by linarith [hx.1])
        have hx0 := hbnonneg x hx
        have hr0 := hbnonneg (2 * ε - x) hreflect
        have htop := hbnonneg (2 * ε) h2ε_mem
        simpa [pow_two] using mul_le_mul hleft hright hr0 htop
      _ = 2 * ε * b (2 * ε) ^ 2 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

end WeilKernelOnset
