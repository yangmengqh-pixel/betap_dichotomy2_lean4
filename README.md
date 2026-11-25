# Walk dimensions in Lean

This package formalizes Theorems 2.1 and 2.5 of Meng Yang’s *On the dichotomy of
p-walk dimensions on metric measure spaces II*. [Paper, arXiv:2611.02422v1](https://arxiv.org/abs/2611.02422v1)

**Manuscript PDF SHA-256** (`2611.02422v1.pdf`)  
`30710500dec406c9cc704f219d6ee76ba098896eddf4ff7ac4af085d5b736e89`

## Install Git and Elan

1. Install Git. On macOS, run `git --version` and accept the Command Line
   Tools prompt if it appears. On Debian or Ubuntu, run `sudo apt install git`.
   On Windows, use the [Git for Windows installer](https://git-scm.com/download/win).
   For other systems, see the [Git installation guide](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git).
2. Install [Elan](https://github.com/leanprover/elan), the Lean toolchain manager.
   On macOS or Linux, run the following command.

   ```sh
   curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
   ```

   On Windows, follow the [Elan installation guide](https://github.com/leanprover/elan#installation).
3. Open a new terminal and check that both tools are available.

   ```sh
   git --version
   elan --version
   ```

## Build

Run the commands below from the directory containing `lakefile.toml`.
Elan selects Lean **4.37.0-rc1** from `lean-toolchain`, and Lake uses the Mathlib
revision `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` from `lake-manifest.json`.

On a fresh checkout, download Mathlib’s precompiled artifacts and build the
library. The default target `WalkDimensions` checks the full library and
produces the Lean files needed to import both theorems.

```sh
lake exe cache get && lake build
```

If the build is very slow on a machine with limited memory, run
`LEAN_NUM_THREADS=1 lake build` on macOS or Linux to use one Lake worker.

To build only the two theorem modules and their dependencies, run
`lake build +WalkDimensions.Theorem21:olean +WalkDimensions.Theorem25:olean`.

## Check the theorems

From the project directory, run the audit after a successful build.

```sh
lake env lean scripts/CheckAxioms.lean
```

If the theorem files have yet to be built, run the focused build and audit
together.

```sh
lake build +WalkDimensions.Theorem21:olean +WalkDimensions.Theorem25:olean && lake env lean scripts/CheckAxioms.lean
```

Each theorem should report only `propext`, `Classical.choice`, and `Quot.sound`.

## Proof status

Both theorem declarations are complete. Mathlib supplies the general Lean
infrastructure. The theorem proofs and the energy-measure construction are
in this package.

## Errata and deviations

The [comparison with the paper](docs/ERRATA-AND-DEVIATIONS.md) records zero
errata and three deviations in conventions or proof routes. It explains the
nonempty interval convention and the arguments used for strict comparison.

## Correspondence with the manuscript

| Manuscript | Lean declaration | Source file |
| --- | --- | --- |
| Theorem 2.1, dichotomy for the ratio of walk and energy exponents | `WalkDimensions.theorem_2_1` | [Theorem21.lean](WalkDimensions/Theorem21.lean) |
| Theorem 2.5, monotonicity, endpoint propagation, and dichotomy for the normalized walk exponent | `WalkDimensions.theorem_2_5` | [Theorem25.lean](WalkDimensions/Theorem25.lean) |

### Library entry point

[WalkDimensions.lean](WalkDimensions.lean) imports the library and exposes both main theorems.
[scripts/CheckAxioms.lean](scripts/CheckAxioms.lean) checks the dependencies of
both theorem declarations.

### File index

The index covers all 206 modules under `WalkDimensions/`. Each file is listed
under its main role. Shared infrastructure and alternate proof steps are
listed by the material they support, since they may serve several sections.

#### Section 2. Metric measure spaces and energy forms

| Lean file | Role |
| --- | --- |
| [ChainDistance.lean](WalkDimensions/ChainDistance.lean) | Distances defined by fine chains |
| [ChainPaths.lean](WalkDimensions/ChainPaths.lean) | Controlled paths from the chain condition |
| [ClarksonComplements.lean](WalkDimensions/ClarksonComplements.lean) | Complementary Clarkson inequalities |
| [CompactCore.lean](WalkDimensions/CompactCore.lean) | Operations on the continuous compact core |
| [CompactEnergyLimit.lean](WalkDimensions/CompactEnergyLimit.lean) | Energy sublevels and uniform approximation on a fixed set |
| [ConnectedChains.lean](WalkDimensions/ConnectedChains.lean) | Uniform chains through compact connected subsets |
| [CoreCapacityCutoffs.lean](WalkDimensions/CoreCapacityCutoffs.lean) | Continuous quantitative cutoffs from the capacity upper bound |
| [CoreCutoffs.lean](WalkDimensions/CoreCutoffs.lean) | Cutoffs in the continuous energy core |
| [CoreLatticeConvergence.lean](WalkDimensions/CoreLatticeConvergence.lean) | Convergence of a fixed localization in the graph norm |
| [CoreProductRoot.lean](WalkDimensions/CoreProductRoot.lean) | Quantitative product estimate on bounded core functions |
| [CoreRestriction.lean](WalkDimensions/CoreRestriction.lean) | Cutting a core function along a separated open region |
| [Doubling.lean](WalkDimensions/Doubling.lean) | Ball comparisons for doubling measures |
| [DoublingCovers.lean](WalkDimensions/DoublingCovers.lean) | Separated covers and packing on doubling spaces |
| [DyadicMidpoints.lean](WalkDimensions/DyadicMidpoints.lean) | Dyadic chains of exact midpoints |
| [EnergyClarkson.lean](WalkDimensions/EnergyClarkson.lean) | Clarkson estimates for the energy seminorm |
| [EnergyClosedness.lean](WalkDimensions/EnergyClosedness.lean) | Lower semicontinuity of the p-energy in Lp |
| [EnergyEvaluation.lean](WalkDimensions/EnergyEvaluation.lean) | Point evaluation in the energy graph norm |
| [EnergyFirstVariation.lean](WalkDimensions/EnergyFirstVariation.lean) | The linear first variation of p-energy |
| [EnergyFold.lean](WalkDimensions/EnergyFold.lean) | Preservation of energy under folding values |
| [EnergyGluing.lean](WalkDimensions/EnergyGluing.lean) | Energy bounded by local extensions |
| [EnergyLattice.lean](WalkDimensions/EnergyLattice.lean) | Shifted lattice operations |
| [EnergyLatticeIdentity.lean](WalkDimensions/EnergyLatticeIdentity.lean) | Energy of pointwise minima and maxima |
| [EnergyLocality.lean](WalkDimensions/EnergyLocality.lean) | Local sums of compactly supported functions |
| [EnergyMidpointLimit.lean](WalkDimensions/EnergyMidpointLimit.lean) | Vanishing energy under a midpoint bound |
| [EnergyNondegeneracy.lean](WalkDimensions/EnergyNondegeneracy.lean) | Nondegeneracy of continuous test functions |
| [EnergyStrongConvergence.lean](WalkDimensions/EnergyStrongConvergence.lean) | Strong energy convergence from ambient convergence and norm convergence |
| [EnergyTestFunctions.lean](WalkDimensions/EnergyTestFunctions.lean) | Nonconstant tests in the energy domain |
| [EnergyTruncation.lean](WalkDimensions/EnergyTruncation.lean) | Splitting energy at a level |
| [Geometry.lean](WalkDimensions/Geometry.lean) | Metric measure space hypotheses |
| [IntrinsicDistance.lean](WalkDimensions/IntrinsicDistance.lean) | Intrinsic distance under the chain condition |
| [IntrinsicMidpoint.lean](WalkDimensions/IntrinsicMidpoint.lean) | Midpoints of the intrinsic chain distance |
| [MidpointContraction.lean](WalkDimensions/MidpointContraction.lean) | Contractions of midpoints |
| [PEnergy.lean](WalkDimensions/PEnergy.lean) | The p-energy, Poincaré inequality, and capacity bound |
| [PathComponents.lean](WalkDimensions/PathComponents.lean) | Open path components and restriction of core functions |
| [PathTail.lean](WalkDimensions/PathTail.lean) | The portion of a path after it last leaves a ball |
| [ShortPaths.lean](WalkDimensions/ShortPaths.lean) | Short paths and snowflake lengths |
| [StrongLocality.lean](WalkDimensions/StrongLocality.lean) | Locality on the support of a continuous representative |

#### Section 2. Canonical and signed energy measures

| Lean file | Role |
| --- | --- |
| [CompactLevelTest.lean](WalkDimensions/CompactLevelTest.lean) | Representing compact sets by exact energy sublevels |
| [CoreEnergyClarkson.lean](WalkDimensions/CoreEnergyClarkson.lean) | Passing the energy inequalities to local measures |
| [CoreEnergyClarksonLower.lean](WalkDimensions/CoreEnergyClarksonLower.lean) | The lower Clarkson inequality for the core measure |
| [CoreEnergyDyadic.lean](WalkDimensions/CoreEnergyDyadic.lean) | Affine locality at dyadic offsets |
| [CoreEnergyLevels.lean](WalkDimensions/CoreEnergyLevels.lean) | Level sets carry no energy for the associated function |
| [CoreEnergyLocality.lean](WalkDimensions/CoreEnergyLocality.lean) | Locality on Borel sets |
| [CoreEnergyMeasure.lean](WalkDimensions/CoreEnergyMeasure.lean) | Mass and open-set locality of the core energy measure |
| [CoreEnergyMidpoint.lean](WalkDimensions/CoreEnergyMidpoint.lean) | Midpoint bounds for local energy sublevels |
| [CoreEnergyOscillation.lean](WalkDimensions/CoreEnergyOscillation.lean) | The local measure of an oscillation |
| [CoreEnergyPairs.lean](WalkDimensions/CoreEnergyPairs.lean) | Localized Clarkson estimates |
| [CoreEnergyScaling.lean](WalkDimensions/CoreEnergyScaling.lean) | Scalar homogeneity of the core energy measure |
| [CoreEnergySeminorm.lean](WalkDimensions/CoreEnergySeminorm.lean) | The triangle inequality for the localized core energy root |
| [CoreEnergySublevels.lean](WalkDimensions/CoreEnergySublevels.lean) | Sublevel values and localization of the core measure |
| [CoreEnergyTruncation.lean](WalkDimensions/CoreEnergyTruncation.lean) | Energy carried by lower value sets |
| [CoreMeasureContinuity.lean](WalkDimensions/CoreMeasureContinuity.lean) | Setwise continuity of core energy measures |
| [CoreMeasureConvergence.lean](WalkDimensions/CoreMeasureConvergence.lean) | Upper semicontinuity on compact sets |
| [DyadicOscillation.lean](WalkDimensions/DyadicOscillation.lean) | Identities for nested oscillations |
| [EnergyContent.lean](WalkDimensions/EnergyContent.lean) | The compact content of the energy measure |
| [EnergyDerivativeClip.lean](WalkDimensions/EnergyDerivativeClip.lean) | The signed energy derivative of a clipped local deviation |
| [EnergyDerivativeLaws.lean](WalkDimensions/EnergyDerivativeLaws.lean) | Linearity, locality and variation bounds for the signed energy measure |
| [EnergyDerivativeProduct.lean](WalkDimensions/EnergyDerivativeProduct.lean) | The Leibniz rule for the signed energy measure on the compact core |
| [EnergyDerivativeSquare.lean](WalkDimensions/EnergyDerivativeSquare.lean) | The quadratic chain rule in the second argument |
| [EnergyDerivativeWeights.lean](WalkDimensions/EnergyDerivativeWeights.lean) | Weighted derivatives and their local bounds |
| [EnergyMeasureClarkson.lean](WalkDimensions/EnergyMeasureClarkson.lean) | Clarkson inequalities on the full domain |
| [EnergyMeasureConstruction.lean](WalkDimensions/EnergyMeasureConstruction.lean) | The canonical energy measure on the full domain |
| [EnergyMeasureDerivative.lean](WalkDimensions/EnergyMeasureDerivative.lean) | Signed energy measures from first variation |
| [EnergyMeasureLocality.lean](WalkDimensions/EnergyMeasureLocality.lean) | The mass, seminorm and locality properties of energy measures |
| [EnergyMeasureRoot.lean](WalkDimensions/EnergyMeasureRoot.lean) | Extension of the localized root to the energy domain |
| [EnergyStrip.lean](WalkDimensions/EnergyStrip.lean) | Energy of a strip between two level sets |
| [OscillationLimit.lean](WalkDimensions/OscillationLimit.lean) | Convergence of localized oscillation energies |
| [OscillationShift.lean](WalkDimensions/OscillationShift.lean) | Changing the threshold of a localized oscillation |
| [OscillatoryTruncation.lean](WalkDimensions/OscillatoryTruncation.lean) | Oscillatory truncations for constructing energy measures |
| [RampEnergy.lean](WalkDimensions/RampEnergy.lean) | Vanishing energy of thin sublevel ramps |
| [SawtoothCells.lean](WalkDimensions/SawtoothCells.lean) | Affine pieces of the sawtooth |
| [SawtoothEnergy.lean](WalkDimensions/SawtoothEnergy.lean) | Energy of the sawtooth |
| [SawtoothPeriod.lean](WalkDimensions/SawtoothPeriod.lean) | Translation and reflection of the oscillation grid |
| [SignedMeasureWeights.lean](WalkDimensions/SignedMeasureWeights.lean) | Bounded scalar weights for signed measures |
| [SublevelComparison.lean](WalkDimensions/SublevelComparison.lean) | Comparison of energy sublevels |
| [SublevelDistribution.lean](WalkDimensions/SublevelDistribution.lean) | Distribution functions of localized energy |
| [SublevelEnergy.lean](WalkDimensions/SublevelEnergy.lean) | Sublevel distribution of energy |
| [ThinTruncation.lean](WalkDimensions/ThinTruncation.lean) | Thin truncations |
| [UniformMeasureLimit.lean](WalkDimensions/UniformMeasureLimit.lean) | Uniform limits of finite measures on measurable sets |
| [VariationStability.lean](WalkDimensions/VariationStability.lean) | Stability of first variation with bounded varying directions |

#### Section 3. Besov estimates, capacity, and resistance

| Lean file | Role |
| --- | --- |
| [AverageHolder.lean](WalkDimensions/AverageHolder.lean) | Hölder estimates from comparisons of averages |
| [AverageOscillation.lean](WalkDimensions/AverageOscillation.lean) | Mean oscillation estimates |
| [BallDifferentiation.lean](WalkDimensions/BallDifferentiation.lean) | Lebesgue differentiation for the paper's open balls |
| [BallIntegration.lean](WalkDimensions/BallIntegration.lean) | Integration over a moving ball |
| [BallPotential.lean](WalkDimensions/BallPotential.lean) | Compactly supported Hölder tests |
| [Besov.lean](WalkDimensions/Besov.lean) | Local Besov energies |
| [BesovCoercivity.lean](WalkDimensions/BesovCoercivity.lean) | Contradictions from vanishing Besov energy |
| [BesovConvolution.lean](WalkDimensions/BesovConvolution.lean) | Discrete convolution bounds for measurable compactly supported inputs |
| [BesovExponentAntitone.lean](WalkDimensions/BesovExponentAntitone.lean) | Antitonicity of the critical Besov exponent |
| [BesovExponentMonotonicity.lean](WalkDimensions/BesovExponentMonotonicity.lean) | Monotonicity of the unnormalized critical Besov exponent |
| [BesovHolder.lean](WalkDimensions/BesovHolder.lean) | Hölder regularity from a Besov bound |
| [BesovMaskedOscillation.lean](WalkDimensions/BesovMaskedOscillation.lean) | Increment bounds for a masked oscillation |
| [BesovMembership.lean](WalkDimensions/BesovMembership.lean) | Besov membership of a Hölder test function |
| [BesovRecovery.lean](WalkDimensions/BesovRecovery.lean) | Global recovery from the small-scale Besov liminf |
| [BesovStability.lean](WalkDimensions/BesovStability.lean) | Stability of the Besov increment bounds at a fixed scale |
| [CapacityCutoffs.lean](WalkDimensions/CapacityCutoffs.lean) | Cutoff functions from the capacity bound |
| [CompactBesovTest.lean](WalkDimensions/CompactBesovTest.lean) | Compactly supported tests in a supercritical Besov space |
| [ContinuousConvolution.lean](WalkDimensions/ContinuousConvolution.lean) | Continuous discrete convolutions |
| [ConvolutionApproximation.lean](WalkDimensions/ConvolutionApproximation.lean) | Approximation in the ambient space by discrete convolutions |
| [ConvolutionEnergy.lean](WalkDimensions/ConvolutionEnergy.lean) | Energy of a discrete convolution |
| [ConvolutionRecovery.lean](WalkDimensions/ConvolutionRecovery.lean) | Recovery of compactly supported continuous functions |
| [CriticalBesov.lean](WalkDimensions/CriticalBesov.lean) | The lower bound for the critical Besov exponent |
| [CutoffNormalization.lean](WalkDimensions/CutoffNormalization.lean) | Normalizing cutoffs |
| [CutoffPartition.lean](WalkDimensions/CutoffPartition.lean) | Finite partitions of unity in the energy domain |
| [DiscreteConvolution.lean](WalkDimensions/DiscreteConvolution.lean) | Discrete convolutions in the energy domain |
| [DiscreteOscillation.lean](WalkDimensions/DiscreteOscillation.lean) | Oscillation of neighbouring ball averages |
| [Interpolation.lean](WalkDimensions/Interpolation.lean) | Small-scale interpolation |
| [LargeScale.lean](WalkDimensions/LargeScale.lean) | Large-scale Besov control on Ahlfors-regular spaces |
| [LintegralHolderMass.lean](WalkDimensions/LintegralHolderMass.lean) | A moment bound with the mass of the underlying measure |
| [LocalBesov.lean](WalkDimensions/LocalBesov.lean) | Local Besov bound from the ball Poincaré inequality |
| [LocalBesovDomain.lean](WalkDimensions/LocalBesovDomain.lean) | Local reverse Besov estimates on the whole energy domain |
| [LocalBesovRecovery.lean](WalkDimensions/LocalBesovRecovery.lean) | The reverse local Besov estimate |
| [LocalEnergyBound.lean](WalkDimensions/LocalEnergyBound.lean) | Local energy bounded by the energy of an extension |
| [LocalMorrey.lean](WalkDimensions/LocalMorrey.lean) | The localized Morrey estimate |
| [Morrey.lean](WalkDimensions/Morrey.lean) | Morrey estimates from Poincaré and Ahlfors regularity |
| [PointBarrier.lean](WalkDimensions/PointBarrier.lean) | A point-to-boundary barrier |
| [PointCapacityApproximation.lean](WalkDimensions/PointCapacityApproximation.lean) | Point values and compact capacity approximants |
| [PointDifferenceCapacity.lean](WalkDimensions/PointDifferenceCapacity.lean) | Point capacity bounded by a unit difference |
| [PointResistance.lean](WalkDimensions/PointResistance.lean) | Point capacity and resistance |
| [ResistanceExponentBound.lean](WalkDimensions/ResistanceExponentBound.lean) | The resistance exponent is at most one |
| [ResistanceMetric.lean](WalkDimensions/ResistanceMetric.lean) | The power of point resistance is a metric |
| [ResistanceTriangle.lean](WalkDimensions/ResistanceTriangle.lean) | The resistance triangle inequality |
| [SmallCutoffs.lean](WalkDimensions/SmallCutoffs.lean) | Exhaustion by small-energy cutoffs |
| [SmallEnergyCutoff.lean](WalkDimensions/SmallEnergyCutoff.lean) | Large cutoffs with arbitrarily small normalized energy |
| [UnitIntervalMeasure.lean](WalkDimensions/UnitIntervalMeasure.lean) | A characterization of Lebesgue measure on the unit interval |

#### Theorem 2.1 and Section 4. Strict comparison via singular energy

| Lean file | Role |
| --- | --- |
| [AdjacentAverageDensity.lean](WalkDimensions/AdjacentAverageDensity.lean) | Nearby averages when energy mass is bounded by volume |
| [BoundedSupportCoercivity.lean](WalkDimensions/BoundedSupportCoercivity.lean) | Control of the graph norm on functions vanishing on a set of positive mass |
| [ChainOscillation.lean](WalkDimensions/ChainOscillation.lean) | Vanishing normalized oscillation at a positive density point |
| [ClippedHarmonicEstimate.lean](WalkDimensions/ClippedHarmonicEstimate.lean) | A bounded perturbation captures energy on its unclipped values |
| [DensityTangents.lean](WalkDimensions/DensityTangents.lean) | Uniform estimates on subsets at Radon–Nikodym density points |
| [HarmonicBand.lean](WalkDimensions/HarmonicBand.lean) | Energy in the bounded values of a harmonic domain element |
| [HarmonicPlateTest.lean](WalkDimensions/HarmonicPlateTest.lean) | Bounded harmonic test functions from almost-everywhere plate constraints |
| [HarmonicSingularity.lean](WalkDimensions/HarmonicSingularity.lean) | Singularity of the energy measure on a region of harmonicity |
| [LocalPlateauMeasure.lean](WalkDimensions/LocalPlateauMeasure.lean) | Vanishing energy measure on an almost-everywhere constant open set |
| [SingularComparison.lean](WalkDimensions/SingularComparison.lean) | Vanishing at matching normalized exponents |
| [SingularPlateTest.lean](WalkDimensions/SingularPlateTest.lean) | A nonconstant test function with singular energy measure |
| [Theorem21.lean](WalkDimensions/Theorem21.lean) | Theorem 2.1 of arXiv:2611.02422v1 |
| [WalkRatioStrictness.lean](WalkDimensions/WalkRatioStrictness.lean) | Strict ratio comparison from a singular energy measure |

#### Theorem 2.1. Propagation of the first-order endpoint

| Lean file | Role |
| --- | --- |
| [BesovSlope.lean](WalkDimensions/BesovSlope.lean) | First-order energy control by the local Lipschitz slope |
| [ConnectivitySelfImprovement.lean](WalkDimensions/ConnectivitySelfImprovement.lean) | Openness of bounded-weight connectivity below its exponent |
| [ContinuousConnectivity.lean](WalkDimensions/ContinuousConnectivity.lean) | Finite-cost paths from the first-order Poincaré estimate |
| [FirstOrderEndpoint.lean](WalkDimensions/FirstOrderEndpoint.lean) | A first-order connectivity estimate forces first-order energy scaling |
| [FirstOrderInterpolation.lean](WalkDimensions/FirstOrderInterpolation.lean) | Lipschitz interpolants of a compact plateau test with small first-order cost |
| [LipschitzBallTents.lean](WalkDimensions/LipschitzBallTents.lean) | Lipschitz interpolants of a finite family of ball averages |
| [LipschitzPoincare.lean](WalkDimensions/LipschitzPoincare.lean) | The first-order endpoint yields a metric Poincaré inequality |
| [LocalMaximalAverage.lean](WalkDimensions/LocalMaximalAverage.lean) | Local uncentered maximal averages |
| [LowerSemicontinuousWeights.lean](WalkDimensions/LowerSemicontinuousWeights.lean) | Increasing continuous approximations of bounded lower semicontinuous weights |
| [MaximalSuperlevel.lean](WalkDimensions/MaximalSuperlevel.lean) | Localized measure estimates for maximal superlevel sets |
| [ObstaclePaths.lean](WalkDimensions/ObstaclePaths.lean) | Selecting and replacing a short obstacle excursion |
| [ObstacleWeights.lean](WalkDimensions/ObstacleWeights.lean) | Lacunary obstacle weights for the exponent improvement |
| [OpenTimeIntervals.lean](WalkDimensions/OpenTimeIntervals.lean) | Finite approximations of the excursions into an open set of times |
| [PathSplicing.lean](WalkDimensions/PathSplicing.lean) | Replacing finitely many disjoint time intervals of a path |
| [PointwiseSlope.lean](WalkDimensions/PointwiseSlope.lean) | The measurable pointwise Lipschitz slope |
| [PointwiseSlopePoincare.lean](WalkDimensions/PointwiseSlopePoincare.lean) | The pointwise consequence of the slope Poincaré inequality |
| [TimedPathLimits.lean](WalkDimensions/TimedPathLimits.lean) | Compactness of bounded-duration paths and monotone lower bounds on costs |
| [TimedPathSlope.lean](WalkDimensions/TimedPathSlope.lean) | Controlling the change along a timed path by Lipschitz slopes |
| [TimedPaths.lean](WalkDimensions/TimedPaths.lean) | Unit-speed bounds and weighted costs on timed paths |
| [UnitWeightConnectivity.lean](WalkDimensions/UnitWeightConnectivity.lean) | Unit-bounded weights and rescaling weighted connections |
| [WeightedDistance.lean](WalkDimensions/WeightedDistance.lean) | The cost of a least expensive timed connection |

#### Sections 4–5. Shared exponent comparisons and Theorem 2.5(1)

| Lean file | Role |
| --- | --- |
| [Exponents.lean](WalkDimensions/Exponents.lean) | Exponent comparisons and dichotomies |
| [GammaComparison.lean](WalkDimensions/GammaComparison.lean) | Monotonicity and upper endpoint for the normalized walk exponent |
| [SupercriticalBesovExponent.lean](WalkDimensions/SupercriticalBesovExponent.lean) | The critical Besov exponent in the positive Morrey range |
| [SupercriticalComparison.lean](WalkDimensions/SupercriticalComparison.lean) | Exponent comparison in the positive Morrey range |
| [WalkExponent.lean](WalkDimensions/WalkExponent.lean) | Identification and basic comparisons of walk exponents |
| [WalkExponentFamily.lean](WalkDimensions/WalkExponentFamily.lean) | Walk-exponent families on a parameter set |

#### Section 6. Upper-endpoint propagation for Theorem 2.5(2)

| Lean file | Role |
| --- | --- |
| [DeficitDetour.lean](WalkDimensions/DeficitDetour.lean) | A positive triangle deficit gives an annular detour |
| [DeficitEnergySplit.lean](WalkDimensions/DeficitEnergySplit.lean) | Energy of the upper branch near series equality |
| [DetourDeficit.lean](WalkDimensions/DetourDeficit.lean) | A detour forces a positive triangle deficit at the endpoint |
| [DetourPotentialBound.lean](WalkDimensions/DetourPotentialBound.lean) | A positive value at the end of a detour |
| [DyadicEndpoint.lean](WalkDimensions/DyadicEndpoint.lean) | Geometric input for dyadic endpoint propagation |
| [DyadicGrowth.lean](WalkDimensions/DyadicGrowth.lean) | A dyadic growth obstruction |
| [EndpointPropagation.lean](WalkDimensions/EndpointPropagation.lean) | Propagation of the upper endpoint in the positive Morrey range |
| [LocalPlateComparison.lean](WalkDimensions/LocalPlateComparison.lean) | Local comparison with a point-to-boundary plate potential |
| [NearMinimizerComparison.lean](WalkDimensions/NearMinimizerComparison.lean) | Comparison for approximate minimizers with point values |
| [PointPropagation.lean](WalkDimensions/PointPropagation.lean) | Propagation of positivity for near-minimizing point potentials |
| [SeriesContinuity.lean](WalkDimensions/SeriesContinuity.lean) | Uniform loss from a small series-energy error |
| [SeriesEnergy.lean](WalkDimensions/SeriesEnergy.lean) | The series energy identity |
| [SeriesStability.lean](WalkDimensions/SeriesStability.lean) | Uniform stability of the series minimum |
| [SeriesTest.lean](WalkDimensions/SeriesTest.lean) | A pair of separated test functions gives a series bound |
| [SmallZeroPlate.lean](WalkDimensions/SmallZeroPlate.lean) | Enlarging a zero plate by a small ball |

#### Sections 6–7. Minimizers and capacitary potentials

| Lean file | Role |
| --- | --- |
| [CorePotentialMeasure.lean](WalkDimensions/CorePotentialMeasure.lean) | Distribution of a minimizing potential |
| [EnergyMinimizer.lean](WalkDimensions/EnergyMinimizer.lean) | Energy minimizers on closed convex sets |
| [PlateMinimizer.lean](WalkDimensions/PlateMinimizer.lean) | Minimization with prescribed plate values |
| [PotentialHarmonic.lean](WalkDimensions/PotentialHarmonic.lean) | The variational equation of a plate minimizer |
| [PotentialHausdorffCutoffs.lean](WalkDimensions/PotentialHausdorffCutoffs.lean) | Cutoffs whose energy measures are bounded by Hausdorff measure |
| [PotentialMeasureBounds.lean](WalkDimensions/PotentialMeasureBounds.lean) | Measure bounds from the capacitary pushforward identity |
| [PotentialPushforward.lean](WalkDimensions/PotentialPushforward.lean) | First variation of the capacitary pushforward |
| [PotentialTruncation.lean](WalkDimensions/PotentialTruncation.lean) | Energy of intervals of a capacitary potential |

#### Section 7. Strict comparison for Theorem 2.5(3)

| Lean file | Role |
| --- | --- |
| [ClippedCutoffPartition.lean](WalkDimensions/ClippedCutoffPartition.lean) | Local energy bounds for a finite cutoff partition |
| [CoreCutoffSums.lean](WalkDimensions/CoreCutoffSums.lean) | Finite sums and truncation of compact-core cutoffs |
| [CutoffDensityBounds.lean](WalkDimensions/CutoffDensityBounds.lean) | Uniform density and energy estimates for a finite covering by cutoffs |
| [FineOscillationMeasure.lean](WalkDimensions/FineOscillationMeasure.lean) | A positive-mass set with Hausdorff lower density |
| [FiniteCutoffCover.lean](WalkDimensions/FiniteCutoffCover.lean) | Packing and overlap for finite cutoff covers |
| [HarmonicCutoffFlow.lean](WalkDimensions/HarmonicCutoffFlow.lean) | Boundary, payoff and cost estimates for the harmonic coupling |
| [HarmonicCutoffPairing.lean](WalkDimensions/HarmonicCutoffPairing.lean) | The finite coupling from harmonic variations |
| [HausdorffDensity.lean](WalkDimensions/HausdorffDensity.lean) | Hausdorff measure bounded by lower densities on fine ball covers |
| [HausdorffDensityTail.lean](WalkDimensions/HausdorffDensityTail.lean) | Density of the complement in a Hausdorff-dominated measure |
| [OscillationDensity.lean](WalkDimensions/OscillationDensity.lean) | Lower densities from positive Besov oscillation at a shared Hölder exponent |
| [PositiveGammaStrictness.lean](WalkDimensions/PositiveGammaStrictness.lean) | A shared positive normalized exponent below one is impossible |
| [PotentialCutoffPartition.lean](WalkDimensions/PotentialCutoffPartition.lean) | Finite cutoff partitions subordinate to minimizing cutoffs |
| [PotentialOscillationDensity.lean](WalkDimensions/PotentialOscillationDensity.lean) | Fine densities for a minimizing potential at a shared exponent |
| [SnowflakeTransport.lean](WalkDimensions/SnowflakeTransport.lean) | Transport bounds for small links in a snowflaked metric |
| [Theorem25.lean](WalkDimensions/Theorem25.lean) | Theorem 2.5 of arXiv:2611.02422v1 |
| [TransportMassBounds.lean](WalkDimensions/TransportMassBounds.lean) | Mass and variation bounds in a rescaled ball |
| [TransportScales.lean](WalkDimensions/TransportScales.lean) | Choosing the approximation and link scales in the transport inequality |
| [TransportVariationScaling.lean](WalkDimensions/TransportVariationScaling.lean) | The local and complement variation estimates after rescaling |

## Citation and license

Cite Meng Yang, *On the dichotomy of p-walk dimensions on metric measure spaces
II*, arXiv:2611.02422v1, Theorems 2.1 and 2.5. Mathlib is fetched separately
under its own license.

The Lean formalization workflow was based on the `lean-workflow` skill from
Scott Armstrong’s [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills).

The Lean source and project documentation are licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
See [LICENSE](LICENSE).
