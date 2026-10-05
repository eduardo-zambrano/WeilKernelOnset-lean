# Lean companion: prime-power onset and first variation for shifted Weil kernels

[![Lean CI](https://github.com/eduardo-zambrano/WeilKernelOnset-lean/actions/workflows/lean_action.yml/badge.svg)](https://github.com/eduardo-zambrano/WeilKernelOnset-lean/actions/workflows/lean_action.yml)

Formal verification companion to **Prime-power onset and first variation for
shifted Weil kernels**, by Eduardo Zambrano. Lean and Mathlib are pinned to
4.28.0, with exact dependency commits in `lake-manifest.json`.

## October 2026 manuscript revision

The current development includes the revised paper's direct mixed-correlation
argument, exact nonnegative resolvent remainder, and relative first-variation
limit. The October revision adds the explicit relative-error bound
`0 ≤ D/F - 1 ≤ Crel / log (1/ε)`, conditional on the analytic Fourier-cutoff
estimate for the localization parameter. These additions follow the existing
**v0.1.0** release; that tag remains unchanged. Cite the commit used when
referring to these additions. The older Neumann-series declarations remain
available.

The formalization checks abstract implications with the analytic and concrete
operator-space inputs stated explicitly as theorem hypotheses. It is not an
end-to-end construction of the localized Weil operator.

## What is checked

The revised argument has three checked parts:

1. **Onset scale from both boundary profiles.**
   `diagonal_response_onset_of_mixed_logBoundary` combines the Riesz identities,
   an exact support bridge, and almost-everywhere logarithmic bounds on the two
   physical kernels. It derives a positive two-sided bound for the real part of
   the diagonal response, with constants `c²/2` and `4 C²`. This proof uses
   neither compactness nor operator-norm smallness.
2. **Relative accuracy of the first variation.**
   `kernel_diagonal_response_resolvent` expresses the response as its first
   variation plus the exact inverse quadratic form. In the norm-small regime,
   coercivity proves this remainder's nonnegativity; self-adjointness proves
   reality. A direct factorization estimate bounds it on the strip-mass scale.
   `relative_first_variation_of_eta_tendsto` proves `D/F → 1`.
3. **Logarithmic rate of relative accuracy.**
   `logarithmic_relative_error_bound` transfers `η ≤ Cη / log (1/ε)` and
   `η ≤ 1/2` to `0 ≤ D/F - 1 ≤ (2 Cη/c₀) / log (1/ε)`.
   `eta_tendsto_zero_of_logarithmic_bound` derives `η → 0`, and
   `relative_first_variation_with_logarithmic_rate` checks the eventual
   relative-error estimate. The concrete Fourier-cutoff estimate is an
   explicit analytic hypothesis, not a result formalized in this companion.

The assembled theorem `continuum_even_onset_with_first_variation` derives the
ratio limit, positivity of the first variation, `D ≥ F`, reality of the
response, and two-sided onset bounds from the existing operator-family and
boundary interfaces plus self-adjointness of the physical update. The final
assembly retains the earlier scale proof; the independent direct proof of the
scale is checked in `MixedOnset.lean`.

The strengthened assembly
`continuum_even_onset_with_logarithmic_relative_error` derives all these
conclusions from the logarithmic localization bound and the existing
operator/boundary interfaces. It also gives
`0 ≤ D/F - 1 ≤ (16 C² Cη/c²) / log (1/ε)` for all sufficiently small positive
`ε`. No separate localization-limit hypothesis is required.

Additional verified components include the abstract partial-reflection norm,
compactness after strong convergence, restriction to shrinking endpoint strips,
explicit logarithmic profile integrals, the almost-everywhere support-coordinate
bridge, and the earlier Neumann expansion and remainder absorption. The exact
resolvent remainder is proved equal to the earlier series remainder.

## Manuscript correspondence

| Result | Main declarations | Scope |
|---|---|---|
| Partial-reflection geometry | `partialReflectionUpdate_sq`, `norm_partialReflectionUpdate`, `compression_norm_le` | Abstract block algebra and norm/compression bounds. |
| Mixed identity | `twoMetric_kernel_identity`, `mixed_kernel_difference` | One-evaluation Riesz and diagonal-response identities. |
| Exact nonnegative remainder | `kernel_diagonal_response_resolvent`, `resolventRemainder_re_nonneg`, `kernel_diagonal_response_im_eq_zero` | The regime `‖T‖ < 1`, sufficient for the local theorem; the paper's broader arbitrary positive-invertible formulation is not claimed here. |
| Compact localization | `tendsto_endpointStripRestriction_compact_opNorm`, `norm_resolventRemainder_metricOperator_le` | Compact-after-strong restriction and direct localized remainder bound. |
| Logarithmic strip estimates | `boundaryProfile_square_integral_bounds`, `boundaryProfile_product_integral_bounds` | Explicit bounds for `1 / sqrt (log (1 + d⁻²))`. |
| Direct mixed-correlation onset | `mixed_logarithmic_boundary_to_onset_bounds`, `diagonal_response_onset_of_mixed_logBoundary` | Real-response bounds from two a.e. boundary profiles and the mixed support bridge. |
| Relative first variation | `relative_response_error_bound`, `relative_first_variation_of_eta_tendsto`, `relative_first_variation_of_scale` | Quantitative relative error and the one-sided limit `D/F → 1`. |
| Qualitative main conclusion | `continuum_even_onset_with_first_variation` | Operator-family assembly of scale, ratio limit, reality, and `D ≥ F`. |
| Logarithmic relative-error rate | `logarithmic_relative_error_bound`, `relative_first_variation_with_logarithmic_rate` | Scalar transfer of the explicit analytic localization-rate hypothesis. |
| Quantitative main conclusion | `continuum_even_onset_with_logarithmic_relative_error` | Operator-family assembly with the rate `0 ≤ D/F - 1 ≤ (16 C² Cη/c²) / log (1/ε)`. |

## Explicit analytic and realization hypotheses

The companion does not prove:

- the digamma/Lévy representation, killed part form, arithmetic rate budget,
  torsion comparison, or geometric-stable boundary estimate;
- compactness of the particular logarithmic Weil form embedding or the
  Fourier-cutoff estimate giving its quantitative shrinking-strip rate;
- realization of the abstract reflection block by the concrete interval
  translations, parity restrictions, and physical support projections;
- the boundary estimates and evenness of the concrete Weil kernel vectors;
- the exact support bridges identifying the operator expressions with physical
  first-order or mixed overlaps and strip mass;
- realization of the moving window spaces in the final fixed-space family
  interface, or the concrete localization-parameter bound and interval
  integrability inputs. In the quantitative assembly, the localization limit
  is derived from the assumed logarithmic bound.

These remain ordinary theorem hypotheses, not project axioms. The updated
self-adjoint operator layer now derives the reality of the response; it does not
assume that reality. The direct mixed theorem, without self-adjointness, states
its conclusion for the response's real part.

## Files

- `Basic.lean`: Riesz conventions and onset scale.
- `PartialReflection.lean`: block reflection algebra.
- `TwoMetric.lean`: Riesz identities and the retained Neumann inverse API.
- `CompactStrong.lean`, `StripRestriction.lean`: compact localization.
- `CompactLocalization.lean`, `KernelResponse.lean`: retained factorized series
  bounds and response expansion.
- `PositiveRemainder.lean`: exact inverse quadratic remainder, positivity,
  reality, and its direct localized bound.
- `LogScale.lean`, `BoundaryProfile.lean`: profile integrals.
- `BoundaryCorrelation.lean`, `LogBoundary.lean`: a.e. boundary-to-overlap bridge.
- `MixedOnset.lean`: direct onset from the two kernel profiles.
- `Onset.lean`, `Assembly.lean`: retained scale and operator-family assembly.
- `RelativeOnset.lean`, `RelativeAssembly.lean`: ratio limit and qualitative assembly.
- `QuantitativeOnset.lean`: logarithmic relative-error transfer and quantitative
  operator-family assembly.
- `AxiomAudit.lean`: trusted dependencies of the principal declarations.

`WeilKernelOnset.lean` imports the public modules.

## Build and audit

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
lake build WeilKernelOnset.AxiomAudit
```

Project Lean source contains no proof placeholders or project-level axioms or
opaque declarations. The printed audit exposes standard logical foundations
such as `propext`, `Quot.sound`, and `Classical.choice`. CI rebuilds the project,
checks for placeholders and project axioms, and runs the dependency audit.

## Citation and license

`CITATION.cff` records the existing tagged release. For the September and October additions,
also cite the source commit and the revised manuscript. Copyright 2026 Eduardo
Zambrano. [Apache License 2.0](LICENSE).
