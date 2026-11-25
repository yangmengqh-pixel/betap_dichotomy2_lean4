# Errata and deviations

This record compares the Lean formalization with Section 2 and the proofs
in Sections 4–7 of Meng Yang’s *On the dichotomy of p-walk dimensions on
metric measure spaces II*, arXiv:2611.02422v1. Counts are by entry. A change
in proof route or an explicit convention is recorded as a deviation.

| Source | Errata | Deviations |
| --- | ---: | ---: |
| Yang, arXiv:2611.02422v1 | 0 | 3 |

## Errata

None identified for Theorems 2.1 and 2.5.

## Deviations

1. **Section 2, Theorems 2.1 and 2.5.** The open interval is represented by
   an open, preconnected, nonempty subset of the real line. Nonemptiness is
   explicit because the two alternatives both hold vacuously on the empty
   set. The energy witness at each exponent supplies the bound `1 < p`.
   [Theorem 2.1](../WalkDimensions/Theorem21.lean) · [Theorem 2.5](../WalkDimensions/Theorem25.lean)
2. **Section 4, Theorem 2.1.** The strict ratio comparison uses a bounded
   variational minimizer with two constant plates. The proof obtains the
   singular energy measure needed for this test and uses weighted path
   connectivity for propagation of the first-order endpoint.
   [Singular test](../WalkDimensions/SingularPlateTest.lean) · [First-order endpoint](../WalkDimensions/FirstOrderEndpoint.lean)
3. **Section 7, Theorem 2.5.** In the positive normalized exponent range,
   the strict comparison uses a finite transport argument with Lipschitz
   test functions in the original metric.
   [Strict comparison](../WalkDimensions/PositiveGammaStrictness.lean)

The package exports the two main theorems and their supporting results.
Applications to specific fractals are outside its scope.
