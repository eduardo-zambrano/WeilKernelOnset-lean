import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Basic definitions for the Weil-kernel onset formalization

The manuscript uses inner products linear in the first variable.  Mathlib uses
the opposite convention.  Consequently a reproducing vector `K` represents an
evaluation functional `ev` through `inner ℂ K f = ev f`.
-/

open scoped InnerProduct

namespace WeilKernelOnset

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Riesz representative of a continuous evaluation functional. -/
noncomputable def kernelVector (ev : H →L[ℂ] ℂ) : H :=
  (InnerProductSpace.toDual ℂ H).symm ev

@[simp] theorem kernelVector_reproduces (ev : H →L[ℂ] ℂ) (f : H) :
    inner ℂ (kernelVector ev) f = ev f := by
  exact InnerProductSpace.toDual_symm_apply

/-- The scalar scale occurring in the continuum onset theorem. -/
noncomputable def onsetScale (ε : ℝ) : ℝ :=
  ε / Real.log (1 / ε)

theorem onsetScale_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 ≤ onsetScale ε := by
  have hlog : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hε).2 (by simpa using hε1)
  exact div_nonneg hε.le hlog.le

theorem onsetScale_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 < onsetScale ε := by
  have hlog : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hε).2 (by simpa using hε1)
  exact div_pos hε hlog

end WeilKernelOnset
