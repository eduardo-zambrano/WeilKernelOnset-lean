import WeilKernelOnset.Basic

/-!
# One-space encoding of the two metrics

This file formalizes Proposition 7.1.  There is one Hilbert-space instance: the
base metric.  The post-arrival metric is represented by `1 + T`.  This avoids
installing two competing `InnerProductSpace` instances on one type.
-/

open scoped InnerProduct

namespace WeilKernelOnset

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- If `K₀` and `K₁` represent the same evaluation functional in the base and
perturbed metrics, then `(1 + T) K₁ = K₀`.  This is Proposition 7.1's first
identity, translated to mathlib's inner-product convention. -/
theorem twoMetric_kernel_identity (T : H →L[ℂ] H) (K₀ K₁ : H)
    (hrep : ∀ f : H,
      inner ℂ K₀ f = inner ℂ K₁ f + inner ℂ (T K₁) f) :
    (1 + T) K₁ = K₀ := by
  apply ext_inner_right ℂ
  intro f
  rw [hrep]
  exact inner_add_left _ _ _

/-- The mixed-kernel difference identity from Proposition 7.1. -/
theorem mixed_kernel_difference (ev : H →L[ℂ] ℂ) (T : H →L[ℂ] H) (K₀ K₁ : H)
    (h₀ : ∀ f : H, ev f = inner ℂ K₀ f)
    (hEq : (1 + T) K₁ = K₀) :
    ev K₁ - ev K₀ = -inner ℂ K₀ (T K₁) := by
  have hdiff : K₁ - K₀ = -(T K₁) := by
    rw [← hEq]
    simp
  rw [← map_sub, h₀, hdiff, inner_neg_right]

variable [CompleteSpace H]

/-- Neumann series for the inverse of `1 + T`. -/
theorem neumann_plus (T : H →L[ℂ] H) (hT : ‖T‖ < 1) :
    HasSum (fun m : ℕ ↦ (-T) ^ m) (Ring.inverse (1 + T)) := by
  simpa only [sub_neg_eq_add] using
    (hasSum_geom_series_inverse (-T) (by simpa only [norm_neg] using hT))

/-- Pointwise form of `neumann_plus`. -/
theorem neumann_plus_apply (T : H →L[ℂ] H) (hT : ‖T‖ < 1) (f : H) :
    HasSum (fun m : ℕ ↦ ((-T) ^ m) f) ((Ring.inverse (1 + T)) f) := by
  exact (neumann_plus T hT).mapL (ContinuousLinearMap.apply ℂ H f)

/-- The post-metric kernel vector is the Neumann inverse applied to the base
kernel vector. -/
theorem neumann_solution (T : H →L[ℂ] H) (K₀ K₁ : H)
    (hT : ‖T‖ < 1) (hEq : (1 + T) K₁ = K₀) :
    K₁ = Ring.inverse (1 + T) K₀ := by
  have hunit : IsUnit (1 + T) := by
    simpa only [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one (x := -T) (by simpa only [norm_neg] using hT))
  calc
    K₁ = (1 : H →L[ℂ] H) K₁ := by simp
    _ = (Ring.inverse (1 + T) * (1 + T)) K₁ := by
      rw [Ring.inverse_mul_cancel (1 + T) hunit]
    _ = Ring.inverse (1 + T) ((1 + T) K₁) := rfl
    _ = Ring.inverse (1 + T) K₀ := by rw [hEq]

/-- The scalar Neumann expansion obtained by applying the base Riesz
functional term by term. -/
theorem neumann_diagonal_hasSum (T : H →L[ℂ] H) (K₀ : H) (hT : ‖T‖ < 1) :
    HasSum (fun m : ℕ ↦ inner ℂ K₀ (((-T) ^ m) K₀))
      (inner ℂ K₀ ((Ring.inverse (1 + T)) K₀)) := by
  exact (neumann_plus_apply T hT K₀).mapL (InnerProductSpace.toDual ℂ H K₀)

end WeilKernelOnset
