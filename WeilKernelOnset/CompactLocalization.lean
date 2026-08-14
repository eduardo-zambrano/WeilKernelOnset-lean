import WeilKernelOnset.TwoMetric

/-!
# Factorized metric perturbations and compact localization

The operator `metricOperator R U = R† U R` is the base-metric Riesz
representative of a physical perturbation supported on the onset strips.  The
main estimate below is the quantitative core of Theorem 7.4.
-/

open scoped InnerProduct

namespace WeilKernelOnset

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The Riesz representative of a factorized physical perturbation. -/
noncomputable def metricOperator (R : H →L[ℂ] K) (U : K →L[ℂ] K) : H →L[ℂ] H :=
  R† ∘L U ∘L R

theorem metricOperator_apply (R : H →L[ℂ] K) (U : K →L[ℂ] K) (f : H) :
    metricOperator R U f = (R†) (U (R f)) := rfl

/-- Exact factorization of the perturbation form. -/
theorem metricOperator_inner (R : H →L[ℂ] K) (U : K →L[ℂ] K) (f g : H) :
    inner ℂ (metricOperator R U f) g = inner ℂ (U (R f)) (R g) := by
  change inner ℂ ((R†) (U (R f))) g = inner ℂ (U (R f)) (R g)
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- Operator-norm smallness after passing to the stronger form metric. -/
theorem metricOperator_norm (R : H →L[ℂ] K) (U : K →L[ℂ] K) :
    ‖metricOperator R U‖ ≤ ‖U‖ * ‖R‖ ^ 2 := by
  calc
    ‖R† ∘L U ∘L R‖ ≤ ‖R†‖ * ‖U ∘L R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖R†‖ * (‖U‖ * ‖R‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖U‖ * ‖R‖ ^ 2 := by
      rw [LinearIsometryEquiv.norm_map]
      ring

theorem metricOperator_pow_factorization (R : H →L[ℂ] K) (U : K →L[ℂ] K)
    (m : ℕ) :
    (metricOperator R U) ^ (m + 1) =
      R† ∘L U ∘L ((R ∘L R† ∘L U) ^ m) ∘L R := by
  induction m with
  | zero =>
      ext x
      simp [metricOperator]
  | succ m ih =>
      rw [pow_succ, ih]
      ext x
      simp [pow_succ, metricOperator]

theorem bridgeOperator_norm (R : H →L[ℂ] K) (U : K →L[ℂ] K) :
    ‖R ∘L R† ∘L U‖ ≤ ‖R‖ ^ 2 * ‖U‖ := by
  calc
    ‖R ∘L R† ∘L U‖ ≤ ‖R‖ * ‖R† ∘L U‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖R‖ * (‖R†‖ * ‖U‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖R‖ ^ 2 * ‖U‖ := by
      rw [LinearIsometryEquiv.norm_map]
      ring

theorem metricOperator_pow_inner (R : H →L[ℂ] K) (U : K →L[ℂ] K)
    (m : ℕ) (f : H) :
    inner ℂ (((metricOperator R U) ^ (m + 1)) f) f =
      inner ℂ (U (((R ∘L R† ∘L U) ^ m) (R f))) (R f) := by
  rw [metricOperator_pow_factorization]
  change inner ℂ ((R†) (U (((R ∘L R† ∘L U) ^ m) (R f)))) f = _
  rw [ContinuousLinearMap.adjoint_inner_left]

variable [Nontrivial K]

/-- The `m`-fold estimate in Theorem 7.4 (with the paper's exponent indexed as
`m + 1`). -/
theorem metricOperator_pow_inner_bound (R : H →L[ℂ] K) (U : K →L[ℂ] K)
    (m : ℕ) (f : H) :
    ‖inner ℂ (((metricOperator R U) ^ (m + 1)) f) f‖ ≤
      ‖U‖ * (‖R‖ ^ 2 * ‖U‖) ^ m * ‖R f‖ ^ 2 := by
  rw [metricOperator_pow_inner]
  let B : K →L[ℂ] K := R ∘L R† ∘L U
  calc
    ‖inner ℂ (U ((B ^ m) (R f))) (R f)‖
        ≤ ‖U ((B ^ m) (R f))‖ * ‖R f‖ := norm_inner_le_norm _ _
    _ ≤ (‖U‖ * ‖(B ^ m) (R f)‖) * ‖R f‖ := by
      gcongr
      exact U.le_opNorm _
    _ ≤ (‖U‖ * (‖B ^ m‖ * ‖R f‖)) * ‖R f‖ := by
      gcongr
      exact (B ^ m).le_opNorm _
    _ ≤ (‖U‖ * (‖B‖ ^ m * ‖R f‖)) * ‖R f‖ := by
      gcongr
      exact norm_pow_le _ _
    _ ≤ (‖U‖ * ((‖R‖ ^ 2 * ‖U‖) ^ m * ‖R f‖)) * ‖R f‖ := by
      gcongr
      exact bridgeOperator_norm R U
    _ = ‖U‖ * (‖R‖ ^ 2 * ‖U‖) ^ m * ‖R f‖ ^ 2 := by ring

/-- Closed form of the geometric majorant for all nonlinear terms. -/
theorem geometric_tail_hasSum {γ η mass : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    HasSum (fun k : ℕ ↦ γ * η ^ (k + 1) * mass)
      (γ * η / (1 - η) * mass) := by
  convert (hasSum_geometric_of_lt_one hη0 hη1).mul_left (γ * η * mass) using 1
  · funext k
    rw [pow_succ]
    ring
  · field_simp

/-- The nonlinear terms are summable when the form-metric size
`η = ‖R‖² ‖U‖` is below one. -/
theorem summable_nonlinear_terms (R : H →L[ℂ] K) (U : K →L[ℂ] K) (f : H)
    (hη : ‖R‖ ^ 2 * ‖U‖ < 1) :
    Summable (fun m : ℕ ↦
      ‖inner ℂ (((metricOperator R U) ^ (m + 2)) f) f‖) := by
  let η : ℝ := ‖R‖ ^ 2 * ‖U‖
  let majorant : ℕ → ℝ := fun m ↦ ‖U‖ * η ^ (m + 1) * ‖R f‖ ^ 2
  have hmajorant : Summable majorant :=
    (geometric_tail_hasSum (γ := ‖U‖) (η := η) (mass := ‖R f‖ ^ 2)
      (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hη).summable
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hmajorant
  intro m
  simpa [majorant, η, Nat.add_assoc] using metricOperator_pow_inner_bound R U (m + 1) f

/-- Summed version of the nonlinear remainder estimate in Theorem 7.4. -/
theorem nonlinear_tsum_bound (R : H →L[ℂ] K) (U : K →L[ℂ] K) (f : H)
    (hη : ‖R‖ ^ 2 * ‖U‖ < 1) :
    (∑' m : ℕ, ‖inner ℂ (((metricOperator R U) ^ (m + 2)) f) f‖) ≤
      ‖U‖ * (‖R‖ ^ 2 * ‖U‖) / (1 - ‖R‖ ^ 2 * ‖U‖) * ‖R f‖ ^ 2 := by
  let η : ℝ := ‖R‖ ^ 2 * ‖U‖
  let majorant : ℕ → ℝ := fun m ↦ ‖U‖ * η ^ (m + 1) * ‖R f‖ ^ 2
  have hmajorantSum := geometric_tail_hasSum
    (γ := ‖U‖) (η := η) (mass := ‖R f‖ ^ 2)
    (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hη
  have hterms := summable_nonlinear_terms R U f hη
  calc
    (∑' m : ℕ, ‖inner ℂ (((metricOperator R U) ^ (m + 2)) f) f‖)
        ≤ ∑' m : ℕ, majorant m := by
          exact hterms.tsum_le_tsum
            (fun m ↦ by
              simpa [majorant, η, Nat.add_assoc] using
                metricOperator_pow_inner_bound R U (m + 1) f)
            hmajorantSum.summable
    _ = ‖U‖ * η / (1 - η) * ‖R f‖ ^ 2 := hmajorantSum.tsum_eq
    _ = _ := rfl

end WeilKernelOnset
