import WeilKernelOnset.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Strongly null families after compact maps

This is the abstract compactness lemma used in Lemma 7.3.  Its proof is the
standard finite-net argument on the compact image of the closed unit ball.
-/

open Filter Metric Set
open scoped Topology

namespace WeilKernelOnset

variable {ι E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A globally bounded, strongly null family converges in operator norm after
precomposition with a compact operator. -/
theorem tendsto_opNorm_compact_of_strong
    {l : Filter ι} (K : E →L[ℂ] F) (hK : IsCompactOperator K)
    (M : ι → F →L[ℂ] G) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i, ‖M i‖ ≤ C)
    (hstrong : ∀ y : F, Tendsto (fun i ↦ M i y) l (𝓝 0)) :
    Tendsto (fun i ↦ ‖M i ∘L K‖) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (4 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC1)
  obtain ⟨S, hScompact, hKS⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨t, _htS, htfinite, hcover⟩ := hScompact.finite_cover_balls hδ
  have hcenters : ∀ᶠ i in l, ∀ y ∈ t, ‖M i y‖ < ε / 4 := by
    apply htfinite.eventually_all.mpr
    intro y hy
    have hy0 : Tendsto (fun i ↦ ‖M i y‖) l (𝓝 0) := by
      simpa using tendsto_norm.comp (hstrong y)
    exact hy0.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hcenters] with i hi
  have hCδ : C * δ ≤ ε / 4 := by
    calc
      C * δ ≤ (C + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 4 := by
        dsimp [δ]
        field_simp
  have hop : ‖M i ∘L K‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith)
    intro x hx
    have hxball : x ∈ closedBall (0 : E) 1 := by
      simpa [mem_closedBall, dist_zero_right] using hx.le
    have hKxS : K x ∈ S := hKS ⟨x, hxball, rfl⟩
    have hKxcover := hcover hKxS
    rcases mem_iUnion.mp hKxcover with ⟨y, hKxcover⟩
    rcases mem_iUnion.mp hKxcover with ⟨hyt, hKxy⟩
    have hdiff : ‖K x - y‖ < δ := by
      simpa [mem_ball, dist_eq_norm] using hKxy
    apply le_of_lt
    calc
      ‖(M i ∘L K) x‖ = ‖M i (K x - y) + M i y‖ := by
        congr 1
        rw [map_sub]
        abel
      _ ≤ ‖M i (K x - y)‖ + ‖M i y‖ := norm_add_le _ _
      _ ≤ ‖M i‖ * ‖K x - y‖ + ‖M i y‖ := by
        gcongr
        exact (M i).le_opNorm _
      _ ≤ C * ‖K x - y‖ + ‖M i y‖ := by
        gcongr
        exact hM i
      _ ≤ C * δ + ‖M i y‖ := by
        gcongr
      _ < ε / 4 + ε / 4 := add_lt_add_of_le_of_lt hCδ (hi y hyt)
      _ = ε / 2 := by ring
  have hop_lt : ‖M i ∘L K‖ < ε := lt_of_le_of_lt hop (by linarith)
  simpa [Real.dist_eq] using hop_lt

/-- Dependent-codomain version of the compact-localization lemma.  Only the
norms `‖Mᵢ y‖` must converge, so this applies directly to restrictions into
the varying spaces `L²(Eᵢ)`. -/
theorem tendsto_opNorm_compact_of_strong_norm
    {G' : ι → Type*}
    [∀ i, NormedAddCommGroup (G' i)] [∀ i, NormedSpace ℂ (G' i)]
    {l : Filter ι} (K : E →L[ℂ] F) (hK : IsCompactOperator K)
    (M : ∀ i, F →L[ℂ] G' i) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i, ‖M i‖ ≤ C)
    (hstrong : ∀ y : F, Tendsto (fun i ↦ ‖M i y‖) l (𝓝 0)) :
    Tendsto (fun i ↦ ‖M i ∘L K‖) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (4 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC1)
  obtain ⟨S, hScompact, hKS⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨t, _htS, htfinite, hcover⟩ := hScompact.finite_cover_balls hδ
  have hcenters : ∀ᶠ i in l, ∀ y ∈ t, ‖M i y‖ < ε / 4 := by
    apply htfinite.eventually_all.mpr
    intro y hy
    exact (hstrong y).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hcenters] with i hi
  have hCδ : C * δ ≤ ε / 4 := by
    calc
      C * δ ≤ (C + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 4 := by
        dsimp [δ]
        field_simp
  have hop : ‖M i ∘L K‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith)
    intro x hx
    have hxball : x ∈ closedBall (0 : E) 1 := by
      simpa [mem_closedBall, dist_zero_right] using hx.le
    have hKxS : K x ∈ S := hKS ⟨x, hxball, rfl⟩
    have hKxcover := hcover hKxS
    rcases mem_iUnion.mp hKxcover with ⟨y, hKxcover⟩
    rcases mem_iUnion.mp hKxcover with ⟨hyt, hKxy⟩
    have hdiff : ‖K x - y‖ < δ := by
      simpa [mem_ball, dist_eq_norm] using hKxy
    apply le_of_lt
    calc
      ‖(M i ∘L K) x‖ = ‖M i (K x - y) + M i y‖ := by
        congr 1
        rw [map_sub]
        abel
      _ ≤ ‖M i (K x - y)‖ + ‖M i y‖ := norm_add_le _ _
      _ ≤ ‖M i‖ * ‖K x - y‖ + ‖M i y‖ := by
        gcongr
        exact (M i).le_opNorm _
      _ ≤ C * ‖K x - y‖ + ‖M i y‖ := by
        gcongr
        exact hM i
      _ ≤ C * δ + ‖M i y‖ := by gcongr
      _ < ε / 4 + ε / 4 := add_lt_add_of_le_of_lt hCδ (hi y hyt)
      _ = ε / 2 := by ring
  have hop_lt : ‖M i ∘L K‖ < ε := lt_of_le_of_lt hop (by linarith)
  simpa [Real.dist_eq] using hop_lt

/-- A family dominated in operator norm by the compactly localized maps is
itself norm-null.  This is the moving-window form of Lemma 7.3. -/
theorem tendsto_opNorm_of_le_compactStrong
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {l : Filter ι} (K : E →L[ℂ] F) (hK : IsCompactOperator K)
    (M : ι → F →L[ℂ] G) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i, ‖M i‖ ≤ C)
    (hstrong : ∀ y : F, Tendsto (fun i ↦ M i y) l (𝓝 0))
    (R : ι → H →L[ℂ] G)
    (hR : ∀ i, ‖R i‖ ≤ ‖M i ∘L K‖) :
    Tendsto (fun i ↦ ‖R i‖) l (𝓝 0) := by
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun i ↦ norm_nonneg (R i))
    (Filter.Eventually.of_forall hR)
    (tendsto_opNorm_compact_of_strong K hK M C hC hM hstrong)

/-- Consequently the localization parameter `‖Rᵢ‖² γ` tends to zero. -/
theorem tendsto_localizationParameter
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {l : Filter ι} (K : E →L[ℂ] F) (hK : IsCompactOperator K)
    (M : ι → F →L[ℂ] G) (C γ : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i, ‖M i‖ ≤ C)
    (hstrong : ∀ y : F, Tendsto (fun i ↦ M i y) l (𝓝 0))
    (R : ι → H →L[ℂ] G)
    (hR : ∀ i, ‖R i‖ ≤ ‖M i ∘L K‖) :
    Tendsto (fun i ↦ ‖R i‖ ^ 2 * γ) l (𝓝 0) := by
  have hzero := tendsto_opNorm_of_le_compactStrong K hK M C hC hM hstrong R hR
  simpa using (hzero.pow 2).mul_const γ

end WeilKernelOnset
