import WeilKernelOnset.KernelResponse

/-!
# Exact positive resolvent remainder

The rewritten paper uses the second-order resolvent identity instead of a
termwise Neumann argument.  The identity is exact, and self-adjointness makes
its remainder real and nonnegative.  Norm-smallness proves positivity of the
inverse quadratic form; positivity of the remainder is not an assumption.
The existing Neumann-series API is retained and identified with this formula.
-/

open scoped InnerProduct

namespace WeilKernelOnset

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact second-order term in the resolvent response. -/
noncomputable def resolventRemainder (T : H →L[ℂ] H) (f : H) : ℂ :=
  inner ℂ (T f) (Ring.inverse (1 + T) (T f))

theorem isUnit_one_add_of_norm_lt_one (T : H →L[ℂ] H) (hT : ‖T‖ < 1) :
    IsUnit (1 + T) := by
  simpa only [sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one (x := -T) (by simpa only [norm_neg] using hT))

/-- The resolvent solves the perturbed metric equation. -/
theorem one_add_inverse_apply (T : H →L[ℂ] H) (hT : ‖T‖ < 1) (v : H) :
    (1 + T) (Ring.inverse (1 + T) v) = v := by
  change ((1 + T) * Ring.inverse (1 + T)) v = v
  rw [Ring.mul_inverse_cancel (1 + T) (isUnit_one_add_of_norm_lt_one T hT)]
  rfl

/-- Elementary pointwise resolvent bound, obtained from the inverse equation. -/
theorem norm_inverse_one_add_apply_le (T : H →L[ℂ] H) (hT : ‖T‖ < 1) (v : H) :
    ‖Ring.inverse (1 + T) v‖ ≤ ‖v‖ / (1 - ‖T‖) := by
  let y := Ring.inverse (1 + T) v
  have hEq : y + T y = v := one_add_inverse_apply T hT v
  have hy : y = v - T y := by rw [← hEq]; abel
  have hb : ‖y‖ ≤ ‖v‖ + ‖T‖ * ‖y‖ := by
    calc
      ‖y‖ = ‖v - T y‖ := congrArg norm hy
      _ ≤ ‖v‖ + ‖T y‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + ‖T‖ * ‖y‖ := add_le_add_right (T.le_opNorm y) _
  apply (le_div_iff₀ (sub_pos.mpr hT)).2
  nlinarith

omit [CompleteSpace H] in
/-- Coercivity of `1 + T`, stated in the inner-product order used by mathlib. -/
theorem one_add_inner_re_lower (T : H →L[ℂ] H) (v : H) :
    (1 - ‖T‖) * ‖v‖ ^ 2 ≤ (inner ℂ ((1 + T) v) v).re := by
  have hinner : ‖inner ℂ (T v) v‖ ≤ ‖T‖ * ‖v‖ ^ 2 := by
    calc
      ‖inner ℂ (T v) v‖ ≤ ‖T v‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖v‖) * ‖v‖ := by
        gcongr
        exact T.le_opNorm v
      _ = ‖T‖ * ‖v‖ ^ 2 := by ring
  have hre := (abs_le.mp (Complex.abs_re_le_norm (inner ℂ (T v) v))).1
  have hself : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    inner_add_left, Complex.add_re, hself] at ⊢
  nlinarith

/-- The inverse quadratic form is nonnegative because `1 + T` is coercive. -/
theorem inverse_one_add_inner_re_nonneg (T : H →L[ℂ] H) (hT : ‖T‖ < 1) (v : H) :
    0 ≤ (inner ℂ v (Ring.inverse (1 + T) v)).re := by
  have h := one_add_inner_re_lower T (Ring.inverse (1 + T) v)
  rw [one_add_inverse_apply T hT v] at h
  exact (mul_nonneg (sub_pos.mpr hT).le (sq_nonneg _)).trans h

/-- Self-adjointness makes the inverse quadratic form real. -/
theorem inverse_one_add_inner_im_eq_zero (T : H →L[ℂ] H)
    (hself : IsSelfAdjoint T) (hT : ‖T‖ < 1) (v : H) :
    (inner ℂ v (Ring.inverse (1 + T) v)).im = 0 := by
  let y := Ring.inverse (1 + T) v
  have hEq : y + T y = v := one_add_inverse_apply T hT v
  change (inner ℂ v y).im = 0
  rw [← hEq, inner_add_left, Complex.add_im]
  have hsym : (inner ℂ (T y) y).im = 0 := hself.isSymmetric.im_inner_apply_self y
  have hy : (inner ℂ y y).im = 0 := inner_self_im (𝕜 := ℂ) y
  rw [hy, hsym, add_zero]

/-- The complete kernel response is its first-order term plus the exact
resolvent quadratic form. -/
theorem kernel_diagonal_response_resolvent
    (ev : H →L[ℂ] ℂ) (T : H →L[ℂ] H) (K₀ K₁ : H)
    (hrep : ∀ f : H, ev f = inner ℂ K₀ f)
    (hself : IsSelfAdjoint T) (hT : ‖T‖ < 1)
    (hEq : (1 + T) K₁ = K₀) :
    ev K₁ - ev K₀ = -inner ℂ K₀ (T K₀) + resolventRemainder T K₀ := by
  have hsolve := neumann_solution T K₀ K₁ hT hEq
  have hleft : Ring.inverse (1 + T) ((1 + T) K₀) = K₀ := by
    change (Ring.inverse (1 + T) * (1 + T)) K₀ = K₀
    rw [Ring.inverse_mul_cancel (1 + T) (isUnit_one_add_of_norm_lt_one T hT)]
    rfl
  have hdiff : Ring.inverse (1 + T) (T K₀) = K₀ - K₁ := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, map_add,
      ← hsolve] at hleft
    exact eq_sub_of_add_eq' hleft
  have hs₀ : inner ℂ (T K₀) K₀ = inner ℂ K₀ (T K₀) := hself.isSymmetric K₀ K₀
  have hs₁ : inner ℂ (T K₀) K₁ = inner ℂ K₀ (T K₁) := hself.isSymmetric K₀ K₁
  rw [mixed_kernel_difference ev T K₀ K₁ hrep hEq, resolventRemainder,
    hdiff, inner_sub_right, hs₀, hs₁]
  ring

/-- The former series remainder equals the new exact quadratic form. -/
theorem neumannRemainder_eq_resolventRemainder (T : H →L[ℂ] H) (f : H)
    (hself : IsSelfAdjoint T) (hT : ‖T‖ < 1) :
    neumannRemainder T f = resolventRemainder T f := by
  let ev := InnerProductSpace.toDual ℂ H f
  have hrep : ∀ x : H, ev x = inner ℂ f x := fun _ ↦ rfl
  have hEq := one_add_inverse_apply T hT f
  have h₁ := kernel_diagonal_response_expansion ev T f
    (Ring.inverse (1 + T) f) hrep hT hEq
  have h₂ := kernel_diagonal_response_resolvent ev T f
    (Ring.inverse (1 + T) f) hrep hself hT hEq
  exact add_left_cancel (h₁.symm.trans h₂)

theorem resolventRemainder_re_nonneg (T : H →L[ℂ] H) (f : H) (hT : ‖T‖ < 1) :
    0 ≤ (resolventRemainder T f).re :=
  inverse_one_add_inner_re_nonneg T hT (T f)

theorem resolventRemainder_im_eq_zero (T : H →L[ℂ] H) (f : H)
    (hself : IsSelfAdjoint T) (hT : ‖T‖ < 1) :
    (resolventRemainder T f).im = 0 :=
  inverse_one_add_inner_im_eq_zero T hself hT (T f)

/-- The exact remainder is bounded using only the inverse equation and
Cauchy--Schwarz. -/
theorem norm_resolventRemainder_le (T : H →L[ℂ] H) (f : H) (hT : ‖T‖ < 1) :
    ‖resolventRemainder T f‖ ≤ ‖T f‖ ^ 2 / (1 - ‖T‖) := by
  calc
    ‖resolventRemainder T f‖ ≤ ‖T f‖ * ‖Ring.inverse (1 + T) (T f)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖T f‖ * (‖T f‖ / (1 - ‖T‖)) := by
      gcongr
      exact norm_inverse_one_add_apply_le T hT (T f)
    _ = ‖T f‖ ^ 2 / (1 - ‖T‖) := by ring

variable {K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A self-adjoint physical perturbation induces a self-adjoint metric operator. -/
theorem metricOperator_isSelfAdjoint (R : H →L[ℂ] K) (U : K →L[ℂ] K)
    (hU : IsSelfAdjoint U) : IsSelfAdjoint (metricOperator R U) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (metricOperator R U f) g = inner ℂ f (metricOperator R U g)
  rw [metricOperator_inner]
  have hsym : inner ℂ (U (R f)) (R g) = inner ℂ (R f) (U (R g)) := hU.isSymmetric _ _
  rw [hsym]
  change inner ℂ (R f) (U (R g)) = inner ℂ f ((R†) (U (R g)))
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- Compactly localized estimate for the exact resolvent remainder, proved
from the pointwise inverse bound without summing a Neumann series. -/
theorem norm_resolventRemainder_metricOperator_le
    (R : H →L[ℂ] K) (U : K →L[ℂ] K) (f : H)
    (hη : ‖R‖ ^ 2 * ‖U‖ < 1) :
    ‖resolventRemainder (metricOperator R U) f‖ ≤
      ‖U‖ * (‖R‖ ^ 2 * ‖U‖) / (1 - ‖R‖ ^ 2 * ‖U‖) * ‖R f‖ ^ 2 := by
  have hnorm : ‖metricOperator R U‖ ≤ ‖R‖ ^ 2 * ‖U‖ := by
    simpa [mul_comm] using metricOperator_norm R U
  have hT : ‖metricOperator R U‖ < 1 := hnorm.trans_lt hη
  have hpoint : ‖metricOperator R U f‖ ≤ ‖R‖ * ‖U‖ * ‖R f‖ := by
    calc
      ‖metricOperator R U f‖ ≤ ‖R†‖ * ‖U (R f)‖ := (R†).le_opNorm _
      _ ≤ ‖R†‖ * (‖U‖ * ‖R f‖) := by
        gcongr
        exact U.le_opNorm _
      _ = ‖R‖ * ‖U‖ * ‖R f‖ := by
        rw [LinearIsometryEquiv.norm_map]
        ring
  have hsquare : ‖metricOperator R U f‖ ^ 2 ≤
      ‖U‖ * (‖R‖ ^ 2 * ‖U‖) * ‖R f‖ ^ 2 := by
    calc
      ‖metricOperator R U f‖ ^ 2 ≤ (‖R‖ * ‖U‖ * ‖R f‖) ^ 2 := by
        gcongr
      _ = _ := by ring
  calc
    ‖resolventRemainder (metricOperator R U) f‖ ≤
        ‖metricOperator R U f‖ ^ 2 / (1 - ‖metricOperator R U‖) :=
      norm_resolventRemainder_le _ f hT
    _ ≤ ‖metricOperator R U f‖ ^ 2 / (1 - ‖R‖ ^ 2 * ‖U‖) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hη) (sub_le_sub_left hnorm 1)
    _ ≤ (‖U‖ * (‖R‖ ^ 2 * ‖U‖) * ‖R f‖ ^ 2) / (1 - ‖R‖ ^ 2 * ‖U‖) :=
      div_le_div_of_nonneg_right hsquare (sub_pos.mpr hη).le
    _ = _ := by ring

/-- For a self-adjoint perturbation the kernel response is real. -/
theorem kernel_diagonal_response_im_eq_zero
    (ev : H →L[ℂ] ℂ) (T : H →L[ℂ] H) (K₀ K₁ : H)
    (hrep : ∀ f : H, ev f = inner ℂ K₀ f)
    (hself : IsSelfAdjoint T) (hT : ‖T‖ < 1)
    (hEq : (1 + T) K₁ = K₀) :
    (ev K₁ - ev K₀).im = 0 := by
  have him : (inner ℂ K₀ (T K₀)).im = 0 := hself.isSymmetric.im_inner_self_apply K₀
  rw [kernel_diagonal_response_resolvent ev T K₀ K₁ hrep hself hT hEq,
    Complex.add_im, Complex.neg_im, him, resolventRemainder_im_eq_zero T K₀ hself hT]
  norm_num

/-- The exact response lies above its first variation.  The excess is the
nonnegative resolvent remainder. -/
theorem first_variation_le_kernel_diagonal_response_re
    (ev : H →L[ℂ] ℂ) (T : H →L[ℂ] H) (K₀ K₁ : H)
    (hrep : ∀ f : H, ev f = inner ℂ K₀ f)
    (hself : IsSelfAdjoint T) (hT : ‖T‖ < 1)
    (hEq : (1 + T) K₁ = K₀) :
    (-inner ℂ K₀ (T K₀)).re ≤ (ev K₁ - ev K₀).re := by
  rw [kernel_diagonal_response_resolvent ev T K₀ K₁ hrep hself hT hEq,
    Complex.add_re]
  exact le_add_of_nonneg_right (resolventRemainder_re_nonneg T K₀ hT)

end WeilKernelOnset
