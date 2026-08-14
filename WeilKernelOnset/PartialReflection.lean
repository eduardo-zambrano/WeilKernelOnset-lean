import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Exact off-diagonal partial reflection

The active collar in Proposition 6.1 splits into two isometric strips.  After
that identification, the physical update is `-γ` times the off-diagonal
reflection constructed here.  The construction is independent of coordinates
and records the exact norm-one jump.
-/

namespace WeilKernelOnset

variable {H K : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- The off-diagonal reflection associated with an isometric equivalence
between the two collar spaces.  Raw products carry the max norm; the same block
map is unitary for the Hilbert direct-sum norm. -/
def offDiagonalReflection (J : H ≃ₗᵢ[ℂ] K) : H × K ≃ₗᵢ[ℂ] H × K where
  toLinearEquiv :=
    { toFun := fun z ↦ (J.symm z.2, J z.1)
      invFun := fun z ↦ (J.symm z.2, J z.1)
      left_inv := by
        rintro ⟨x, y⟩
        simp
      right_inv := by
        rintro ⟨x, y⟩
        simp
      map_add' := by
        rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
        simp
      map_smul' := by
        intro c z
        ext <;> simp }
  norm_map' := by
    rintro ⟨x, y⟩
    change max ‖J.symm y‖ ‖J x‖ = max ‖x‖ ‖y‖
    rw [J.norm_map, J.symm.norm_map, max_comm]

@[simp] theorem offDiagonalReflection_apply (J : H ≃ₗᵢ[ℂ] K) (x : H) (y : K) :
    offDiagonalReflection J (x, y) = (J.symm y, J x) := rfl

@[simp] theorem offDiagonalReflection_involutive (J : H ≃ₗᵢ[ℂ] K) (z : H × K) :
    offDiagonalReflection J (offDiagonalReflection J z) = z := by
  rcases z with ⟨x, y⟩
  simp

/-- The physical update `-γ [[0,J⁻¹],[J,0]]`. -/
noncomputable def partialReflectionUpdate (γ : ℝ) (J : H ≃ₗᵢ[ℂ] K) :
    H × K →L[ℂ] H × K :=
  (-(γ : ℂ)) • (offDiagonalReflection J).toLinearIsometry.toContinuousLinearMap

@[simp] theorem partialReflectionUpdate_apply (γ : ℝ) (J : H ≃ₗᵢ[ℂ] K)
    (x : H) (y : K) :
    partialReflectionUpdate γ J (x, y) =
      (-(γ : ℂ) • J.symm y, -(γ : ℂ) • J x) := by
  simp [partialReflectionUpdate, offDiagonalReflection]

/-- Squaring the physical update gives `γ²` on the active collars. -/
theorem partialReflectionUpdate_sq_apply (γ : ℝ) (J : H ≃ₗᵢ[ℂ] K)
    (z : H × K) :
    partialReflectionUpdate γ J (partialReflectionUpdate γ J z) =
      ((γ ^ 2 : ℝ) : ℂ) • z := by
  rcases z with ⟨x, y⟩
  simp only [partialReflectionUpdate_apply, Prod.smul_mk]
  rw [Prod.ext_iff]
  constructor
  · rw [J.symm.map_smul, J.symm_apply_apply, smul_smul]
    rw [show (-(γ : ℂ)) * (-(γ : ℂ)) = ((γ ^ 2 : ℝ) : ℂ) by
      push_cast
      ring]
  · rw [J.map_smul, J.apply_symm_apply, smul_smul]
    rw [show (-(γ : ℂ)) * (-(γ : ℂ)) = ((γ ^ 2 : ℝ) : ℂ) by
      push_cast
      ring]

theorem partialReflectionUpdate_sq (γ : ℝ) (J : H ≃ₗᵢ[ℂ] K) :
    partialReflectionUpdate γ J * partialReflectionUpdate γ J =
      ((γ ^ 2 : ℝ) : ℂ) • (1 : H × K →L[ℂ] H × K) := by
  apply ContinuousLinearMap.ext
  intro z
  exact partialReflectionUpdate_sq_apply γ J z

/-- Exact norm in the disjoint-strip regime. -/
theorem norm_partialReflectionUpdate [Nontrivial H] (γ : ℝ) (hγ : 0 ≤ γ)
    (J : H ≃ₗᵢ[ℂ] K) :
    ‖partialReflectionUpdate γ J‖ = γ := by
  rw [partialReflectionUpdate, norm_smul,
    LinearIsometry.norm_toContinuousLinearMap]
  simp [abs_of_nonneg hγ]

/-- Every compression by contractions has norm at most the physical jump
weight. -/
theorem compression_norm_le [Nontrivial H] (γ : ℝ) (hγ : 0 ≤ γ)
    (J : H ≃ₗᵢ[ℂ] K) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ι : E →L[ℂ] H × K) (P : H × K →L[ℂ] E)
    (hι : ‖ι‖ ≤ 1) (hP : ‖P‖ ≤ 1) :
    ‖P ∘L partialReflectionUpdate γ J ∘L ι‖ ≤ γ := by
  calc
    ‖P ∘L partialReflectionUpdate γ J ∘L ι‖
        ≤ ‖P‖ * ‖partialReflectionUpdate γ J ∘L ι‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖P‖ * (‖partialReflectionUpdate γ J‖ * ‖ι‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (γ * 1) := by
      rw [norm_partialReflectionUpdate γ hγ J]
      gcongr
    _ = γ := by ring

end WeilKernelOnset
