import WeilKernelOnset.LogScale
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# From boundary profiles to the first-order overlap

This file formalizes the bridge used in Section 8 of the paper.  A boundary
profile is an almost-everywhere statement, as it should be for physical
representatives living in `L²`.  Evenness identifies the left onset trace with
the right-boundary trace, while reflection of the integration variable gives
the other factor.  The resulting product and square integrals are then bounded
by the profile integrals from `LogScale`.

There are no axioms in this file: compactness and the potential-theoretic
boundary estimate enter later as ordinary theorem hypotheses.
-/

open Set MeasureTheory
open scoped Interval

namespace WeilKernelOnset

/-- The value sampled on the left onset strip, in coordinates measured from
its left endpoint. -/
def leftOnsetTrace (k : ℝ → ℝ) (a : ℝ) (s : ℝ) : ℝ :=
  k (-a + s)

/-- The value sampled on the right onset strip after translation by the new
prime-power displacement. -/
def rightOnsetTrace (k : ℝ → ℝ) (a ε : ℝ) (s : ℝ) : ℝ :=
  k (a - 2 * ε + s)

/-- The first-order signed contribution after the support computation of
Section 6.  For the nonnegative even kernel this is positive. -/
noncomputable def firstOrderOverlap (γ a ε : ℝ) (k : ℝ → ℝ) : ℝ :=
  2 * γ * ∫ s in 0..(2 * ε), leftOnsetTrace k a s * rightOnsetTrace k a ε s

/-- Twice the right-boundary mass, equal to the mass of the two onset strips
for an even physical representative. -/
noncomputable def boundaryStripMass (a ε : ℝ) (k : ℝ → ℝ) : ℝ :=
  2 * ∫ d in 0..(2 * ε), k (a - d) ^ 2

/-- Lebesgue measure is preserved by reflection about `c / 2`. -/
theorem measurePreserving_reflection (c : ℝ) :
    MeasurePreserving (fun x : ℝ ↦ c - x) volume volume := by
  simpa only [Function.comp_apply, sub_eq_add_neg] using
    (measurePreserving_add_left volume c).comp
      (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- Pull an almost-everywhere assertion through an affine reflection. -/
theorem ae_reflection {P : ℝ → Prop} (c : ℝ) (hP : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x ∂volume, P (c - x) := by
  exact (measurePreserving_reflection c).quasiMeasurePreserving.ae hP

/-- Reflection preserves almost-everywhere assertions on a symmetric interval
`[0,L]`. -/
theorem ae_restrict_Icc_reflection {P : ℝ → Prop} {L : ℝ}
    (hP : ∀ᵐ x ∂volume.restrict (Icc 0 L), P x) :
    ∀ᵐ x ∂volume.restrict (Icc 0 L), P (L - x) := by
  have hpre : (fun x : ℝ ↦ L - x) ⁻¹' Icc 0 L = Icc 0 L := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro hx <;> constructor <;> linarith
  have hmp := (measurePreserving_reflection L).restrict_preimage
    (s := Icc (0 : ℝ) L) measurableSet_Icc
  rw [hpre] at hmp
  exact hmp.quasiMeasurePreserving.ae hP

/-- The manuscript's right-boundary estimate, recorded with its correct
almost-everywhere semantics. -/
def HasAEBoundaryProfile (b k : ℝ → ℝ) (c C a L : ℝ) : Prop :=
  ∀ᵐ d ∂volume.restrict (Icc 0 L),
    c * b d ≤ k (a - d) ∧ k (a - d) ≤ C * b d

/-- Evenness and reflection turn one right-boundary estimate into the two
profile estimates used in the first-order overlap integral. -/
theorem onsetTrace_profile_bounds_ae
    {b k : ℝ → ℝ} {c C a ε : ℝ}
    (heven : ∀ᵐ x ∂volume, k (-x) = k x)
    (hboundary : HasAEBoundaryProfile b k c C a (2 * ε)) :
    (∀ᵐ s ∂volume.restrict (Icc 0 (2 * ε)),
        c * b s ≤ leftOnsetTrace k a s ∧ leftOnsetTrace k a s ≤ C * b s) ∧
      (∀ᵐ s ∂volume.restrict (Icc 0 (2 * ε)),
        c * b (2 * ε - s) ≤ rightOnsetTrace k a ε s ∧
          rightOnsetTrace k a ε s ≤ C * b (2 * ε - s)) := by
  have hevenTraceGlobal : ∀ᵐ s ∂volume, k (-a + s) = k (a - s) := by
    have h := ae_reflection a heven
    filter_upwards [h] with s hs
    calc
      k (-a + s) = k (-(a - s)) := by
        congr 1
        ring
      _ = k (a - s) := hs
  have hevenTrace :
      ∀ᵐ s ∂volume.restrict (Icc 0 (2 * ε)), k (-a + s) = k (a - s) :=
    ae_restrict_of_ae hevenTraceGlobal
  constructor
  · filter_upwards [hboundary, hevenTrace] with s hs heq
    simpa only [leftOnsetTrace, heq] using hs
  · have hreflected := ae_restrict_Icc_reflection hboundary
    filter_upwards [hreflected] with s hs
    constructor
    · calc
        c * b (2 * ε - s) ≤ k (a - (2 * ε - s)) := hs.1
        _ = rightOnsetTrace k a ε s := by
          change k (a - (2 * ε - s)) = k (a - 2 * ε + s)
          congr 1
          ring
    · calc
        rightOnsetTrace k a ε s = k (a - (2 * ε - s)) := by
          change k (a - 2 * ε + s) = k (a - (2 * ε - s))
          congr 1
          ring
        _ ≤ C * b (2 * ε - s) := hs.2

/-- Generic a.e. comparison for the overlap integral.  This theorem is useful
independently of the logarithmic profile. -/
theorem overlapIntegral_bounds_of_ae_profile
    {b left right : ℝ → ℝ} {c C ε : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbnonneg : ∀ᵐ s ∂volume.restrict (Icc 0 (2 * ε)), 0 ≤ b s)
    (hleft : ∀ᵐ s ∂volume.restrict (Icc 0 (2 * ε)),
      c * b s ≤ left s ∧ left s ≤ C * b s)
    (hright : ∀ᵐ s ∂volume.restrict (Icc 0 (2 * ε)),
      c * b (2 * ε - s) ≤ right s ∧ right s ≤ C * b (2 * ε - s))
    (hprofileInt : IntervalIntegrable (fun s ↦ b s * b (2 * ε - s)) volume 0 (2 * ε))
    (hoverlapInt : IntervalIntegrable (fun s ↦ left s * right s) volume 0 (2 * ε)) :
    c ^ 2 * (∫ s in 0..(2 * ε), b s * b (2 * ε - s)) ≤
        ∫ s in 0..(2 * ε), left s * right s ∧
      (∫ s in 0..(2 * ε), left s * right s) ≤
        C ^ 2 * ∫ s in 0..(2 * ε), b s * b (2 * ε - s) := by
  have hbreflect := ae_restrict_Icc_reflection hbnonneg
  have hlower :
      (fun s ↦ c ^ 2 * (b s * b (2 * ε - s))) ≤ᵐ[
        volume.restrict (Icc 0 (2 * ε))] (fun s ↦ left s * right s) := by
    filter_upwards [hbnonneg, hbreflect, hleft, hright] with s hbs hbr hls hrs
    calc
      c ^ 2 * (b s * b (2 * ε - s)) = (c * b s) * (c * b (2 * ε - s)) := by ring
      _ ≤ left s * right s :=
        mul_le_mul hls.1 hrs.1 (mul_nonneg hc hbr) (hls.1.trans' (mul_nonneg hc hbs))
  have hupper :
      (fun s ↦ left s * right s) ≤ᵐ[
        volume.restrict (Icc 0 (2 * ε))]
        (fun s ↦ C ^ 2 * (b s * b (2 * ε - s))) := by
    filter_upwards [hbnonneg, hbreflect, hleft, hright] with s hbs hbr hls hrs
    calc
      left s * right s ≤ (C * b s) * (C * b (2 * ε - s)) :=
        mul_le_mul hls.2 hrs.2 (hrs.1.trans' (mul_nonneg hc hbr)) (mul_nonneg hC hbs)
      _ = C ^ 2 * (b s * b (2 * ε - s)) := by ring
  constructor
  · simpa only [intervalIntegral.integral_const_mul] using
      intervalIntegral.integral_mono_ae_restrict (show 0 ≤ 2 * ε by linarith)
        (hprofileInt.const_mul (c ^ 2)) hoverlapInt hlower
  · simpa only [intervalIntegral.integral_const_mul] using
      intervalIntegral.integral_mono_ae_restrict (show 0 ≤ 2 * ε by linarith)
        hoverlapInt (hprofileInt.const_mul (C ^ 2)) hupper

/-- Generic a.e. comparison for the one-sided square mass. -/
theorem squareIntegral_bounds_of_ae_profile
    {b near : ℝ → ℝ} {c C ε : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbnonneg : ∀ᵐ d ∂volume.restrict (Icc 0 (2 * ε)), 0 ≤ b d)
    (hnear : ∀ᵐ d ∂volume.restrict (Icc 0 (2 * ε)),
      c * b d ≤ near d ∧ near d ≤ C * b d)
    (hprofileInt : IntervalIntegrable (fun d ↦ b d ^ 2) volume 0 (2 * ε))
    (hnearInt : IntervalIntegrable (fun d ↦ near d ^ 2) volume 0 (2 * ε)) :
    c ^ 2 * (∫ d in 0..(2 * ε), b d ^ 2) ≤
        ∫ d in 0..(2 * ε), near d ^ 2 ∧
      (∫ d in 0..(2 * ε), near d ^ 2) ≤
        C ^ 2 * ∫ d in 0..(2 * ε), b d ^ 2 := by
  have hlower :
      (fun d ↦ c ^ 2 * b d ^ 2) ≤ᵐ[volume.restrict (Icc 0 (2 * ε))]
        (fun d ↦ near d ^ 2) := by
    filter_upwards [hbnonneg, hnear] with d hbd hnd
    have hcb : 0 ≤ c * b d := mul_nonneg hc hbd
    nlinarith [mul_self_le_mul_self hcb hnd.1]
  have hupper :
      (fun d ↦ near d ^ 2) ≤ᵐ[volume.restrict (Icc 0 (2 * ε))]
        (fun d ↦ C ^ 2 * b d ^ 2) := by
    filter_upwards [hbnonneg, hnear] with d hbd hnd
    have hn0 : 0 ≤ near d := (mul_nonneg hc hbd).trans hnd.1
    have hCb : 0 ≤ C * b d := mul_nonneg hC hbd
    nlinarith [mul_self_le_mul_self hn0 hnd.2]
  constructor
  · simpa only [intervalIntegral.integral_const_mul] using
      intervalIntegral.integral_mono_ae_restrict (show 0 ≤ 2 * ε by linarith)
        (hprofileInt.const_mul (c ^ 2)) hnearInt hlower
  · simpa only [intervalIntegral.integral_const_mul] using
      intervalIntegral.integral_mono_ae_restrict (show 0 ≤ 2 * ε by linarith)
        hnearInt (hprofileInt.const_mul (C ^ 2)) hupper

/-- Explicit Section 8 bounds obtained from a nonnegative monotone profile.
The endpoint expressions are those used before specializing `b` to the
square-root logarithmic boundary profile. -/
theorem boundaryProfile_to_firstOrder_and_mass
    {b k : ℝ → ℝ} {γ c C a ε : ℝ}
    (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hbmono : MonotoneOn b (Icc 0 (2 * ε)))
    (hbnonneg : ∀ x ∈ Icc 0 (2 * ε), 0 ≤ b x)
    (heven : ∀ᵐ x ∂volume, k (-x) = k x)
    (hboundary : HasAEBoundaryProfile b k c C a (2 * ε))
    (hprofileProductInt :
      IntervalIntegrable (fun s ↦ b s * b (2 * ε - s)) volume 0 (2 * ε))
    (hprofileSquareInt : IntervalIntegrable (fun d ↦ b d ^ 2) volume 0 (2 * ε))
    (hoverlapInt : IntervalIntegrable
      (fun s ↦ leftOnsetTrace k a s * rightOnsetTrace k a ε s) volume 0 (2 * ε))
    (hnearInt : IntervalIntegrable (fun d ↦ k (a - d) ^ 2) volume 0 (2 * ε)) :
    2 * γ * (c ^ 2 * (ε * b (ε / 2) ^ 2)) ≤ firstOrderOverlap γ a ε k ∧
      firstOrderOverlap γ a ε k ≤ 2 * γ * (C ^ 2 * (2 * ε * b (2 * ε) ^ 2)) ∧
      2 * (c ^ 2 * (ε * b ε ^ 2)) ≤ boundaryStripMass a ε k ∧
      boundaryStripMass a ε k ≤ 2 * (C ^ 2 * (2 * ε * b (2 * ε) ^ 2)) := by
  have hbnonnegAE : ∀ᵐ x ∂volume.restrict (Icc 0 (2 * ε)), 0 ≤ b x :=
    ae_restrict_of_forall_mem measurableSet_Icc hbnonneg
  rcases onsetTrace_profile_bounds_ae heven hboundary with ⟨hleft, hright⟩
  have hoverlap := overlapIntegral_bounds_of_ae_profile hε hc hC hbnonnegAE
    hleft hright hprofileProductInt hoverlapInt
  have hmass := squareIntegral_bounds_of_ae_profile hε hc hC hbnonnegAE hboundary
    hprofileSquareInt hnearInt
  have hproductSandwich := product_strip_sandwich b ε hε hbmono hbnonneg hprofileProductInt
  have hsquareSandwich := square_strip_sandwich b ε hε hbmono hbnonneg hprofileSquareInt
  have hoverlapLower :
      c ^ 2 * (ε * b (ε / 2) ^ 2) ≤
        ∫ s in 0..(2 * ε), leftOnsetTrace k a s * rightOnsetTrace k a ε s :=
    (mul_le_mul_of_nonneg_left hproductSandwich.1 (sq_nonneg c)).trans hoverlap.1
  have hoverlapUpper :
      (∫ s in 0..(2 * ε), leftOnsetTrace k a s * rightOnsetTrace k a ε s) ≤
        C ^ 2 * (2 * ε * b (2 * ε) ^ 2) :=
    hoverlap.2.trans (mul_le_mul_of_nonneg_left hproductSandwich.2 (sq_nonneg C))
  have hmassLower :
      c ^ 2 * (ε * b ε ^ 2) ≤ ∫ d in 0..(2 * ε), k (a - d) ^ 2 :=
    (mul_le_mul_of_nonneg_left hsquareSandwich.1 (sq_nonneg c)).trans hmass.1
  have hmassUpper :
      (∫ d in 0..(2 * ε), k (a - d) ^ 2) ≤
        C ^ 2 * (2 * ε * b (2 * ε) ^ 2) :=
    hmass.2.trans (mul_le_mul_of_nonneg_left hsquareSandwich.2 (sq_nonneg C))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [firstOrderOverlap] using
      mul_le_mul_of_nonneg_left hoverlapLower (mul_nonneg (by norm_num) hγ)
  · simpa only [firstOrderOverlap] using
      mul_le_mul_of_nonneg_left hoverlapUpper (mul_nonneg (by norm_num) hγ)
  · simpa only [boundaryStripMass] using
      mul_le_mul_of_nonneg_left hmassLower (by norm_num : (0 : ℝ) ≤ 2)
  · simpa only [boundaryStripMass] using
      mul_le_mul_of_nonneg_left hmassUpper (by norm_num : (0 : ℝ) ≤ 2)

end WeilKernelOnset
