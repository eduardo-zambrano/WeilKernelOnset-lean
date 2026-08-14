import WeilKernelOnset.CompactLocalization

/-!
# Kernel response and the nonlinear Neumann remainder

This file joins Proposition 7.1 to Theorem 7.4.  It identifies the exact
first-order term in the change of a kernel diagonal and proves that every
higher Neumann term is controlled by the strip-localized geometric majorant.
-/

open scoped InnerProduct

namespace WeilKernelOnset

/-- The nonlinear (order at least two) part of the Neumann response. -/
noncomputable def neumannRemainder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →L[ℂ] H) (f : H) : ℂ :=
  ∑' m : ℕ, inner ℂ f (((-T) ^ (m + 2)) f)

/-- Alternating signs do not affect the absolute value of a diagonal term.
The reversal of the two inner-product slots accounts for mathlib's convention
that the inner product is linear in its second argument. -/
theorem norm_alternating_diagonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (T : H →L[ℂ] H) (f : H) (m : ℕ) :
    ‖inner ℂ f (((-T) ^ (m + 2)) f)‖ =
      ‖inner ℂ ((T ^ (m + 2)) f) f‖ := by
  rcases Nat.even_or_odd (m + 2) with hn | hn
  · rw [hn.neg_pow]
    exact norm_inner_symm _ _
  · rw [hn.neg_pow]
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, norm_neg]
    exact norm_inner_symm _ _

/-- Exact first-order-plus-remainder expansion for a kernel diagonal. -/
theorem kernel_diagonal_response_expansion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (ev : H →L[ℂ] ℂ) (T : H →L[ℂ] H) (K₀ K₁ : H)
    (hrep : ∀ f : H, ev f = inner ℂ K₀ f)
    (hT : ‖T‖ < 1) (hEq : (1 + T) K₁ = K₀) :
    ev K₁ - ev K₀ =
      -inner ℂ K₀ (T K₀) + neumannRemainder T K₀ := by
  let a : ℕ → ℂ := fun m ↦ inner ℂ K₀ (((-T) ^ m) K₀)
  have hseries := neumann_diagonal_hasSum T K₀ hT
  have hsum : Summable a := by
    simpa only [a] using hseries.summable
  have htotal : (∑' m, a m) = ev K₁ := by
    rw [show (∑' m, a m) = inner ℂ K₀ (Ring.inverse (1 + T) K₀) by
      simpa only [a] using hseries.tsum_eq]
    rw [← neumann_solution T K₀ K₁ hT hEq]
    exact (hrep K₁).symm
  have hshift : Summable (fun m ↦ a (m + 1)) :=
    (summable_nat_add_iff 1).2 hsum
  calc
    ev K₁ - ev K₀ = (∑' m, a m) - a 0 := by
      rw [htotal]
      simp only [a, pow_zero, ContinuousLinearMap.one_apply]
      rw [← hrep K₀]
    _ = ∑' m, a (m + 1) := by
      rw [hsum.tsum_eq_zero_add]
      abel
    _ = a 1 + ∑' m, a (m + 2) := by
      rw [hshift.tsum_eq_zero_add]
    _ = -inner ℂ K₀ (T K₀) + neumannRemainder T K₀ := by
      simp only [a, pow_one, ContinuousLinearMap.neg_apply, inner_neg_right,
        neumannRemainder]

/-- The norm of the complete nonlinear response is bounded by the exact
geometric factor from compact localization. -/
theorem norm_neumannRemainder_metricOperator_le
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Nontrivial K]
    (R : H →L[ℂ] K) (U : K →L[ℂ] K) (f : H)
    (hη : ‖R‖ ^ 2 * ‖U‖ < 1) :
    ‖neumannRemainder (metricOperator R U) f‖ ≤
      ‖U‖ * (‖R‖ ^ 2 * ‖U‖) / (1 - ‖R‖ ^ 2 * ‖U‖) * ‖R f‖ ^ 2 := by
  have hsumnorm : Summable (fun m : ℕ ↦
      ‖inner ℂ f (((-(metricOperator R U)) ^ (m + 2)) f)‖) := by
    have h := summable_nonlinear_terms R U f hη
    exact h.congr
      (fun m ↦ (norm_alternating_diagonal (metricOperator R U) f m).symm)
  calc
    ‖neumannRemainder (metricOperator R U) f‖ ≤
        ∑' m : ℕ, ‖inner ℂ f (((-(metricOperator R U)) ^ (m + 2)) f)‖ := by
      exact norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' m : ℕ,
        ‖inner ℂ (((metricOperator R U) ^ (m + 2)) f) f‖ := by
      apply tsum_congr
      exact fun m ↦ norm_alternating_diagonal (metricOperator R U) f m
    _ ≤ _ := nonlinear_tsum_bound R U f hη

/-- Combined response identity and nonlinear estimate for a factorized strip
perturbation `T = R† U R`. -/
theorem factorized_kernel_response
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Nontrivial K]
    (ev : H →L[ℂ] ℂ) (R : H →L[ℂ] K) (U : K →L[ℂ] K) (K₀ K₁ : H)
    (hrep : ∀ f : H, ev f = inner ℂ K₀ f)
    (hEq : (1 + metricOperator R U) K₁ = K₀)
    (hη : ‖R‖ ^ 2 * ‖U‖ < 1) :
    ev K₁ - ev K₀ =
        -inner ℂ K₀ (metricOperator R U K₀) +
          neumannRemainder (metricOperator R U) K₀ ∧
      ‖neumannRemainder (metricOperator R U) K₀‖ ≤
        ‖U‖ * (‖R‖ ^ 2 * ‖U‖) / (1 - ‖R‖ ^ 2 * ‖U‖) * ‖R K₀‖ ^ 2 := by
  have hT : ‖metricOperator R U‖ < 1 :=
    (metricOperator_norm R U).trans_lt (by simpa [mul_comm] using hη)
  exact ⟨kernel_diagonal_response_expansion ev (metricOperator R U) K₀ K₁
      hrep hT hEq,
    norm_neumannRemainder_metricOperator_le R U K₀ hη⟩

end WeilKernelOnset
