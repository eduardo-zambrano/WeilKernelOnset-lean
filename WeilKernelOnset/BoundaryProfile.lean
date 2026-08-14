import WeilKernelOnset.LogScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exact logarithmic boundary profile

This file instantiates the abstract strip-integral estimates from `LogScale`
with the profile

`b(d) = 1 / sqrt (log (1 + d⁻²))`,

extended at the origin by `b(0) = 0`.  The final two theorems give explicit
constants on the range `0 < ε ≤ 1 / 4`.
-/

open Set MeasureTheory
open scoped Interval

namespace WeilKernelOnset

/-- The square-root logarithmic boundary profile, with its continuous value
`0` at the origin supplied by the totalized inverse operations on `ℝ`. -/
noncomputable def boundaryProfile (d : ℝ) : ℝ :=
  (Real.sqrt (Real.log (1 + (d ^ 2)⁻¹)))⁻¹

theorem boundaryProfile_nonneg (d : ℝ) : 0 ≤ boundaryProfile d := by
  unfold boundaryProfile
  positivity

@[simp] theorem boundaryProfile_zero : boundaryProfile 0 = 0 := by
  simp [boundaryProfile]

/-- Away from the origin, squaring the profile removes the square root. -/
theorem boundaryProfile_sq {d : ℝ} (hd : d ≠ 0) :
    boundaryProfile d ^ 2 = (Real.log (1 + (d ^ 2)⁻¹))⁻¹ := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hlog : 0 ≤ Real.log (1 + (d ^ 2)⁻¹) := by
    apply Real.log_nonneg
    have : 0 ≤ (d ^ 2)⁻¹ := inv_nonneg.mpr hd2.le
    linarith
  simp [boundaryProfile, inv_pow, Real.sq_sqrt hlog]

/-- The logarithmic boundary profile is increasing on the nonnegative axis. -/
theorem boundaryProfile_monotoneOn : MonotoneOn boundaryProfile (Ici 0) := by
  intro x hx y hy hxy
  by_cases hx0 : x = 0
  · subst x
    simpa using boundaryProfile_nonneg y
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hinv : (y ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ := by
    exact inv_anti₀ (sq_pos_of_pos hxpos) hsq
  have hone : 1 + (y ^ 2)⁻¹ ≤ 1 + (x ^ 2)⁻¹ := by linarith
  have hargy : 0 < 1 + (y ^ 2)⁻¹ := by positivity
  have hargx : 0 < 1 + (x ^ 2)⁻¹ := by positivity
  have hlog : Real.log (1 + (y ^ 2)⁻¹) ≤
      Real.log (1 + (x ^ 2)⁻¹) := by
    exact Real.strictMonoOn_log.monotoneOn hargy hargx hone
  have hlogy : 0 < Real.log (1 + (y ^ 2)⁻¹) := by
    apply Real.log_pos
    have : 0 < (y ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hypos)
    linarith
  have hsqrt : Real.sqrt (Real.log (1 + (y ^ 2)⁻¹)) ≤
      Real.sqrt (Real.log (1 + (x ^ 2)⁻¹)) :=
    Real.sqrt_le_sqrt hlog
  unfold boundaryProfile
  exact inv_anti₀ (Real.sqrt_pos.2 hlogy) hsqrt

/-- The upper endpoint comparison used for both strip integrals. -/
theorem boundaryProfile_two_mul_sq_le {ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4) :
    boundaryProfile (2 * ε) ^ 2 ≤ 1 / Real.log (1 / ε) := by
  have htwo : 2 * ε ≠ 0 := by positivity
  rw [boundaryProfile_sq htwo]
  have harg : 1 / ε ≤ 1 + ((2 * ε) ^ 2)⁻¹ := by
    field_simp [ne_of_gt hε]
    nlinarith [sq_nonneg (2 * ε - 1)]
  have hleft : 0 < 1 / ε := one_div_pos.mpr hε
  have hright : 0 < 1 + ((2 * ε) ^ 2)⁻¹ := by positivity
  have hlog : Real.log (1 / ε) ≤
      Real.log (1 + ((2 * ε) ^ 2)⁻¹) :=
    Real.strictMonoOn_log.monotoneOn hleft hright harg
  have hlogpos : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hε).2 (by linarith)
  simpa [one_div] using one_div_le_one_div_of_le hlogpos hlog

/-- The lower endpoint comparison used for the product strip integral. -/
theorem one_div_four_log_le_boundaryProfile_half_sq {ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4) :
    1 / (4 * Real.log (1 / ε)) ≤ boundaryProfile (ε / 2) ^ 2 := by
  have he2 : ε ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
    mul_self_le_mul_self hε.le hεq |> (by simpa [pow_two] using ·)
  have he4raw : (ε ^ 2) ^ 2 ≤ ((1 / 4 : ℝ) ^ 2) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (sq_nonneg ε) he2
  have hpoly : ε ^ 4 + 4 * ε ^ 2 ≤ 1 := by
    norm_num at he2 he4raw ⊢
    nlinarith
  have hhalf : ε / 2 ≠ 0 := by positivity
  rw [boundaryProfile_sq hhalf]
  have harg : 1 + ((ε / 2) ^ 2)⁻¹ ≤ (1 / ε) ^ 4 := by
    field_simp [ne_of_gt hε]
    nlinarith
  have hargleft : 0 < 1 + ((ε / 2) ^ 2)⁻¹ := by positivity
  have hargright : 0 < (1 / ε) ^ 4 := by positivity
  have hlog : Real.log (1 + ((ε / 2) ^ 2)⁻¹) ≤
      4 * Real.log (1 / ε) := by
    calc
      Real.log (1 + ((ε / 2) ^ 2)⁻¹) ≤ Real.log ((1 / ε) ^ 4) :=
        Real.strictMonoOn_log.monotoneOn hargleft hargright harg
      _ = 4 * Real.log (1 / ε) := by rw [Real.log_pow]; norm_num
  have hlogleft : 0 < Real.log (1 + ((ε / 2) ^ 2)⁻¹) := by
    apply Real.log_pos
    have : 0 < ((ε / 2) ^ 2)⁻¹ := by positivity
    linarith
  simpa [one_div] using one_div_le_one_div_of_le hlogleft hlog

/-- The squared profile is interval-integrable on every nonnegative strip. -/
theorem boundaryProfile_sq_intervalIntegrable {ε : ℝ} (hε : 0 ≤ ε) :
    IntervalIntegrable (fun d ↦ boundaryProfile d ^ 2) volume 0 (2 * ε) := by
  apply MonotoneOn.intervalIntegrable
  rw [uIcc_of_le (by linarith)]
  intro x hx y hy hxy
  have hxyb := boundaryProfile_monotoneOn hx.1 hy.1 hxy
  have hx0 := boundaryProfile_nonneg x
  have hy0 := boundaryProfile_nonneg y
  nlinarith

/-- The reflected product of two boundary profiles is interval-integrable on
the onset strip. -/
theorem boundaryProfile_product_intervalIntegrable {ε : ℝ} (hε : 0 ≤ ε) :
    IntervalIntegrable
      (fun x ↦ boundaryProfile x * boundaryProfile (2 * ε - x))
      volume 0 (2 * ε) := by
  have hleft : IntervalIntegrable boundaryProfile volume 0 (2 * ε) := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact boundaryProfile_monotoneOn.mono (fun _ hx ↦ hx.1)
  have hright : IntervalIntegrable (fun x ↦ boundaryProfile (2 * ε - x))
      volume 0 (2 * ε) := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    intro x hx y hy hxy
    apply boundaryProfile_monotoneOn
    · change 0 ≤ 2 * ε - y
      exact sub_nonneg.mpr hy.2
    · change 0 ≤ 2 * ε - x
      exact sub_nonneg.mpr hx.2
    · linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at hleft hright ⊢
  refine hleft.mul_bdd (c := boundaryProfile (2 * ε))
    hright.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hreflect : 2 * ε - x ∈ Icc 0 (2 * ε) :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hle := boundaryProfile_monotoneOn hreflect.1 (by linarith : 0 ≤ 2 * ε)
    (by linarith [hreflect.2])
  simpa [Real.norm_eq_abs, abs_of_nonneg (boundaryProfile_nonneg _)] using hle

/-- Explicit two-sided square-strip bounds at logarithmic scale. -/
theorem boundaryProfile_square_integral_bounds {ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4) :
    onsetScale ε / 4 ≤
        (∫ d in 0..(2 * ε), boundaryProfile d ^ 2) ∧
      (∫ d in 0..(2 * ε), boundaryProfile d ^ 2) ≤
        2 * onsetScale ε := by
  have hsandwich := square_strip_sandwich boundaryProfile ε hε.le
    (boundaryProfile_monotoneOn.mono (fun _ hx ↦ hx.1))
    (fun x _ ↦ boundaryProfile_nonneg x)
    (boundaryProfile_sq_intervalIntegrable hε.le)
  have hhalfle : boundaryProfile (ε / 2) ≤ boundaryProfile ε := by
    apply boundaryProfile_monotoneOn
    · change 0 ≤ ε / 2
      positivity
    · exact hε.le
    · linarith
  have hsqle : boundaryProfile (ε / 2) ^ 2 ≤ boundaryProfile ε ^ 2 := by
    nlinarith [boundaryProfile_nonneg (ε / 2), boundaryProfile_nonneg ε]
  constructor
  · calc
      onsetScale ε / 4 = ε * (1 / (4 * Real.log (1 / ε))) := by
        unfold onsetScale
        ring
      _ ≤ ε * boundaryProfile (ε / 2) ^ 2 := by
        gcongr
        exact one_div_four_log_le_boundaryProfile_half_sq hε hεq
      _ ≤ ε * boundaryProfile ε ^ 2 := by gcongr
      _ ≤ (∫ d in 0..(2 * ε), boundaryProfile d ^ 2) := hsandwich.1
  · calc
      (∫ d in 0..(2 * ε), boundaryProfile d ^ 2)
          ≤ 2 * ε * boundaryProfile (2 * ε) ^ 2 := hsandwich.2
      _ ≤ 2 * ε * (1 / Real.log (1 / ε)) := by
        gcongr
        exact boundaryProfile_two_mul_sq_le hε hεq
      _ = 2 * onsetScale ε := by
        unfold onsetScale
        ring

/-- Explicit two-sided reflected-product bounds at logarithmic scale. -/
theorem boundaryProfile_product_integral_bounds {ε : ℝ}
    (hε : 0 < ε) (hεq : ε ≤ 1 / 4) :
    onsetScale ε / 4 ≤
        (∫ x in 0..(2 * ε),
          boundaryProfile x * boundaryProfile (2 * ε - x)) ∧
      (∫ x in 0..(2 * ε),
          boundaryProfile x * boundaryProfile (2 * ε - x)) ≤
        2 * onsetScale ε := by
  have hsandwich := product_strip_sandwich boundaryProfile ε hε.le
    (boundaryProfile_monotoneOn.mono (fun _ hx ↦ hx.1))
    (fun x _ ↦ boundaryProfile_nonneg x)
    (boundaryProfile_product_intervalIntegrable hε.le)
  constructor
  · calc
      onsetScale ε / 4 = ε * (1 / (4 * Real.log (1 / ε))) := by
        unfold onsetScale
        ring
      _ ≤ ε * boundaryProfile (ε / 2) ^ 2 := by
        gcongr
        exact one_div_four_log_le_boundaryProfile_half_sq hε hεq
      _ ≤ (∫ x in 0..(2 * ε),
          boundaryProfile x * boundaryProfile (2 * ε - x)) := hsandwich.1
  · calc
      (∫ x in 0..(2 * ε),
          boundaryProfile x * boundaryProfile (2 * ε - x))
          ≤ 2 * ε * boundaryProfile (2 * ε) ^ 2 := hsandwich.2
      _ ≤ 2 * ε * (1 / Real.log (1 / ε)) := by
        gcongr
        exact boundaryProfile_two_mul_sq_le hε hεq
      _ = 2 * onsetScale ε := by
        unfold onsetScale
        ring

end WeilKernelOnset
