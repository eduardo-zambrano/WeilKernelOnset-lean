# WeilKernelOnset

[![Lean CI](https://github.com/eduardo-zambrano/WeilKernelOnset-lean/actions/workflows/lean_action.yml/badge.svg)](https://github.com/eduardo-zambrano/WeilKernelOnset-lean/actions/workflows/lean_action.yml)

A Lean 4 companion to Eduardo Zambrano's manuscript *A Continuum
Prime-Power Onset Law for the Localized Weil Kernel*.

This repository machine-checks an abstract proof core drawn from Sections 6--8
of the manuscript: off-diagonal reflection algebra, change of metric by a
bounded operator, compact localization of strongly null families, factorized
nonlinear-response estimates, monotone strip-integral bounds, and the final
explicit remainder-absorption step.

It is intentionally **not** an end-to-end formalization of the paper's main
theorem. In particular, it does not formalize the arithmetic and killed-Levy
construction in Sections 3--5, nor does it instantiate every abstract object
below with the manuscript's concrete localized Weil spaces.

## Verified scope and trust boundary

The Lean kernel verifies the following reusable implications:

- an off-diagonal block built from an isometric equivalence squares to a scalar
  multiple of the identity and has the exact expected norm;
- representing the perturbed metric by `1 + T` yields the two-metric Riesz-vector
  identity, its diagonal response identity, and its Neumann-series expansion
  when `‖T‖ < 1`;
- a uniformly bounded, strongly null operator family converges in operator norm
  after precomposition with a compact operator, including when the codomains
  vary with the strip width;
- restriction of physical `L²(ℝ)` vectors to two shrinking endpoint strips is
  strongly null, and its composition with any compact physical embedding is
  operator-norm null;
- a factorization `T = R† U R` gives the power bounds and summable geometric
  majorant used to control the nonlinear kernel response;
- the exact kernel-diagonal response equals its signed first-order term plus a
  complete Neumann remainder obeying that geometric bound;
- a nonnegative monotone boundary profile satisfies the two strip-integral
  sandwich estimates used in the logarithmic-scale argument;
- the manuscript's exact square-root logarithmic profile satisfies explicit
  two-sided integral bounds at the onset scale;
- an almost-everywhere boundary comparison, together with evenness, gives the
  first-order overlap and strip-mass estimates used in Section 8;
- those inputs assemble into an operator-family theorem giving a positive
  two-sided `ε / log (1 / ε)` bound for the real part of the abstract response
  after shrinking the cutoff.

The following mathematical inputs remain outside the formalized trust boundary:

- the digamma/Lévy representation, killed part form, Green-function comparison,
  and geometric-stable torsion estimate of Sections 3--5;
- the concrete compact embedding of the logarithmic form domain (Lemma 7.2);
- proof that the paper's concrete reproducing vector satisfies the required
  almost-everywhere boundary comparison and evenness/nonnegativity properties;
- identification of the paper's window spaces with the fixed Hilbert-space
  operator-family interface, including the two exact support bridges equating
  the operator quadratic term and norm with the physical overlap and strip
  mass;
- the concrete self-adjoint/positive metric interpretation, reality of the
  kernel-diagonal response, and the Riesz/change-of-metric hypotheses `hrep`
  and `hEq` for those Weil spaces;
- a fixed-codomain realization connecting the varying restricted `L²(Eε)`
  theorem to the final family's assumed localization-parameter limit
  `hetaTendsto`, together with the two local interval-integrability inputs.

These are exposed as ordinary theorem hypotheses rather than declared as Lean
axioms. Thus the artifact checks the paper-specific abstract mechanism without
misrepresenting the imported analytic results as having been formalized.

## Manuscript correspondence

| Manuscript result | Lean declarations | Precisely checked here |
|---|---|---|
| Proposition 6.1, exact partial reflection | `offDiagonalReflection`, `partialReflectionUpdate_sq`, `norm_partialReflectionUpdate`, `compression_norm_le` | Abstract max-norm off-diagonal block algebra, exact norm, and contraction-compression bound. The Hilbert direct-sum realization, concrete interval translation, support projections, and parity statement are not instantiated. |
| Proposition 7.1, two-metric kernel identity | `twoMetric_kernel_identity`, `mixed_kernel_difference`, `neumann_plus`, `neumann_solution`, `neumann_diagonal_hasSum` | Riesz-vector identity, one-evaluation/diagonal difference identity, inverse representation, and diagonal Neumann series in one base Hilbert metric. The full two-point identity is not required by the onset proof and is not formalized. |
| Lemma 7.3, norm-small strip restriction | `endpointStripRestriction`, `tendsto_endpointStripRestriction_norm`, `tendsto_opNorm_compact_of_strong_norm`, `tendsto_endpointStripRestriction_compact_opNorm` | The concrete shrinking endpoint strips in physical `L²`, strong-nullity, the dependent-codomain compactness lemma, and operator-norm convergence after a compact embedding. Compactness of the manuscript's specific embedding remains an input. |
| Theorem 7.4, nonlinear compact localization | `metricOperator`, `metricOperator_pow_inner_bound`, `nonlinear_tsum_bound`, `kernel_diagonal_response_expansion`, `factorized_kernel_response` | Factorization, power estimates, exact first-order-plus-Neumann response, summability, and the explicit complete nonlinear bound. |
| Lemma 8.1, logarithmic strip integrals | `square_strip_sandwich`, `product_strip_sandwich`, `boundaryProfile_square_integral_bounds`, `boundaryProfile_product_integral_bounds` | The abstract integral sandwiches and their specialization to `1 / sqrt (log (1 + d⁻²))`, with explicit lower constant `1/4` and upper constant `2` for `0 < ε ≤ 1/4`. |
| Section 8, first-order correlation and strip mass | `HasAEBoundaryProfile`, `boundaryProfile_to_firstOrder_and_mass`, `logarithmic_boundary_to_onset_bounds` | The a.e. even-boundary bridge and its specialization to explicit first-order and strip-mass constants at logarithmic scale. Satisfaction of the comparison by the concrete Weil-kernel vector remains external. |
| Theorem 8.2, continuum even onset | `continuum_even_onset_of_eta_tendsto`, `operatorOnsetDatum_core_of_logBoundary`, `continuum_even_onset_from_operator_family` | Abstract assembly from operator families, exact support bridges, the a.e. logarithmic boundary input, and localization-parameter convergence to strict positivity and two-sided bounds for the real response. The cutoff is extracted existentially from convergence. The theorem remains conditional on instantiating its named interfaces with the manuscript's Weil spaces and proving response reality there. |

The auxiliary declarations `kernelVector`, `kernelVector_reproduces`,
`onsetScale_nonneg`, and `onsetScale_pos` record the Riesz convention and basic
properties of the onset scale.

## Repository layout

```text
WeilKernelOnset/
├── Basic.lean                 # Riesz vectors and the onset scale
├── PartialReflection.lean     # abstract Proposition 6.1 core
├── TwoMetric.lean             # Proposition 7.1 core
├── CompactStrong.lean         # compact-after-strong convergence lemma
├── StripRestriction.lean      # concrete shrinking endpoint restrictions
├── CompactLocalization.lean   # factorization and nonlinear tail bounds
├── KernelResponse.lean        # exact response and complete remainder
├── LogScale.lean              # strip-integral sandwich estimates
├── BoundaryProfile.lean       # explicit logarithmic-profile bounds
├── BoundaryCorrelation.lean   # a.e. profile-to-overlap/mass bridge
├── LogBoundary.lean           # explicit logarithmic overlap/mass scale
├── Onset.lean                 # cutoff extraction and scalar onset theorem
├── Assembly.lean              # operator-family continuum onset theorem
└── AxiomAudit.lean            # printed dependencies of principal theorems
```

`WeilKernelOnset.lean` is the public import root.

## Reproducible build

The project pins Lean and mathlib to version 4.28.0. The exact dependency
commits are recorded in `lake-manifest.json`.

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

To print the trusted dependencies of the principal declarations:

```sh
lake build WeilKernelOnset.AxiomAudit
```

## Proof and axiom audit

The project source contains no `sorry`, `admit`, project-level `axiom`, or
`opaque` declarations. `AxiomAudit.lean` applies Lean's `#print axioms` command
to the main results. Its output may include Lean's standard logical foundations,
such as propositional extensionality, quotient soundness, and classical choice;
these are part of Lean/mathlib's normal trusted base, not assumptions introduced
by this project.

Continuous integration rebuilds the project, runs the printed-dependency audit,
and rejects the addition of source-level placeholders or project axioms.

## Citation

Citation metadata are provided in [`CITATION.cff`](CITATION.cff). Until the
manuscript has a permanent identifier, please cite both the software release and
the accompanying manuscript.

## License

Copyright 2026 Eduardo Zambrano. Released under the
[Apache License 2.0](LICENSE).
