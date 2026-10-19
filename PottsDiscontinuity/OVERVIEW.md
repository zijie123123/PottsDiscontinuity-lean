# Overview of the proof development

This directory contains the complete proof of Theorems 1.1 and 1.2 of arXiv:1611.09877v2
(873 Lean modules). The entry point `PottsDiscontinuity.lean` imports exactly the three main theorems, and its import closure is exactly this directory together with the vendored Brouwer fixed-point theorem.

## How the proof is organized

```text
Challenge.lean  ── statements (checked by Comparator against) ──  Frozen/
Frozen/Theorem11      ← Provider/Theorem11      ← PottsThm/ (Theorem 1.1 from the RC rate) ← Potts/
Frozen/Theorem12      ← Provider/Theorem12      ← RCMProof/ (assembly of Theorem 1.2)
Frozen/Theorem12Eq13  ← Provider/Theorem12Eq13  ← Analysis/ (Section 4: (1.3) and positivity)

RCMProof/ uses:
  exact value of the rate   Bethe/, BetheAnsatz/, SixVertex/, Analysis/, AnalyticTools/, LinearAlgebra/
  torus bounds (Sec. 3.3)   Torus/, TorusLoops/, TorusRC/, TorusExploration/, TorusTopology/, TorusCrossing/, CorrLength/
  items 1–2 of Theorem 1.2  Duality/, RCInfinite/, Zhang/, FK/
```

Comments in the development sometimes call the declarations of `Frozen/` "frozen": they are
the statement layer, which was fixed before the proofs were written and is mirrored in
`Challenge.lean`.

## Directories

| Directory | Part | Modules | Lines | Contents |
|---|---|---:|---:|---|
| [`Frozen/`](#frozen) | Statement layer | 20 | 582 | The exact statements of the three main theorems (`Theorem11`, `Theorem12`, `Theorem12Eq13`) and, in `Frozen/Defs/`, the 17 definitions they use (square lattice, boxes and boundaries, finite-volume Potts and random-cluster measures, infinite-volume limits along boxes, ergodicity, critical parameters, diagonal site). These declarations are reproduced verbatim in `Challenge.lean`; each theorem is proved by `exact` of its provider. |
| [`Provider/`](#provider) | Statement layer | 3 | 181 | The proofs of the three main theorems, each a short assembly: Theorem 1.1 from the random-cluster rate (`PottsThm/`), Theorem 1.2 items 1–3 from the random-cluster assembly (`RCMProof/`) and the crossing estimate (3.19) (`TorusCrossing/`), and Theorem 1.2 positivity/(1.3) from Section 4 (`Analysis/`). |
| [`PottsThm/`](#pottsthm) | Theorem 1.1 | 20 | 4,270 | Theorem 1.1 deduced from the random-cluster results through the Edwards–Sokal coupling: identification of the Potts box limits, spin formulas with the factor 1 − 1/q, distinctness of the q + 1 measures, ergodicity, and the Potts correlation length. |
| [`Potts/`](#potts) | Theorem 1.1 | 61 | 6,051 | The finite-volume Potts model with the paper's literal boundary term, the Edwards–Sokal coupling in finite volume (ghost-vertex construction), and existence of the Potts box limits with their connection-data description. |
| [`RCMProof/`](#rcmproof) | Theorem 1.2 | 12 | 3,350 | Assembly of Theorem 1.2: equation (1.7) at the critical point, the lower bound on the inverse correlation length, absence of percolation for the critical free measure, the corrected Lemma 3.14, and the final assembly of items 1–3 with (1.2). |
| [`Analysis/`](#analysis) | Section 4 | 6 | 3,630 | Section 4 of the paper: the identity (4.4) behind (1.3), positivity of λ + 2S, the asymptotics as q ↘ 4, partial-fraction and hyperbolic series, and the Fourier/τ integrals used for the correlation length. |
| [`Bethe/`](#bethe) | Section 2 | 115 | 15,997 | Section 2: the functions Θ and k, the discrete Bethe equations, Proposition 2.1 (the densities ρ and τ), Theorem 2.3 (existence of Bethe roots, analytic in Δ), Theorems 2.6 and 2.9 (asymptotics of root densities), and the eigenvalue-ratio limits in both parities. |
| [`BetheAnsatz/`](#betheansatz) | Section 3.1 | 63 | 8,772 | Theorem 3.1, the coordinate Bethe ansatz for the six-vertex transfer matrix in every particle sector, including the zero-root (derivative-corrected) branch. |
| [`SixVertex/`](#sixvertex) | Sections 3.1–3.3 | 51 | 9,020 | The six-vertex model: transfer matrix, block decomposition and trace formulas, Lemma 3.2 (the operator at Δ = −∞ and its simple top eigenvalue), Corollary 3.4 (the analytic Perron–Frobenius eigenvalue family), and the Section 3.3 bounds on partition-function ratios and dominance. |
| [`LinearAlgebra/`](#linearalgebra) | Tools | 4 | 864 | Perron–Frobenius theory for symmetric irreducible matrices and supporting spectral facts. |
| [`AnalyticTools/`](#analytictools) | Tools | 5 | 630 | Real-analytic inverse and implicit function theorems, the identity theorem, and analytic dependence of simple eigenvalues. |
| [`Infra/`](#infra) | Tools | 3 | 194 | Uniqueness of cylinder limits, positivity of random-cluster partition functions, and λ = arcosh(√q / 2). |
| [`FK/`](#fk) | Random-cluster model | 63 | 6,738 | A library for the finite random-cluster (FK) model: laws and boundary conditions, FKG and comparison inequalities, domain Markov property, finite energy, box limits, wired/free comparisons, and bridges to the definitions in `Frozen/Defs/`. |
| [`RCInfinite/`](#rcinfinite) | Random-cluster model | 18 | 2,418 | Infinite-volume random-cluster measures: translation invariance and mixing, ergodicity, the 0–1 law for an infinite cluster, finite energy and comparison, and exhaustion by boxes. (Uniqueness of the infinite cluster is not needed.) |
| [`Duality/`](#duality) | Random-cluster model | 69 | 10,842 | Planar duality: dual configurations, self-duality at p_c in finite and infinite volume, crossing duality, discrete flow/Euler arguments, and the consequences of a positive rate (items 1–2 of Theorem 1.2). |
| [`CorrLength/`](#corrlength) | Section 3.3 | 6 | 1,265 | The correlation length (3.13): its existence by supermultiplicativity on the rotated lattice and the relevant connection events. |
| [`Zhang/`](#zhang) | Section 3.3 | 1 | 126 | Boundary-connection limits in rotated boxes, used for absence of percolation of the critical free measure. |
| [`Torus/`](#torus) | Section 3.3 | 67 | 6,961 | The random-cluster / loop / six-vertex correspondence on the torus: Lemmas 3.9–3.12 and Corollary 3.13. |
| [`TorusLoops/`](#torusloops) | Section 3.3 | 37 | 7,720 | The loop representation on the torus: loop densities, winding loops, tail probabilities and exploration fibres used for Lemma 3.14. |
| [`TorusRC/`](#torusrc) | Section 3.3 | 65 | 7,003 | Random-cluster measures on the torus and Lemma 3.15: equations (3.15) and (3.16), cylinder and barrier events, and the limits relating torus and planar quantities. |
| [`TorusExploration/`](#torusexploration) | Section 3.3 | 39 | 2,988 | Cluster exploration on the torus and equation (3.16): cylinder measures dominated by free measures. |
| [`TorusTopology/`](#torustopology) | Section 3.3 | 114 | 13,757 | Discrete topology on the torus and the planar lattice: winding numbers, turning classifications of loops, the structure of configurations with U = 1, and planar cover graphs. |
| [`TorusCrossing/`](#toruscrossing) | Section 3.3 | 31 | 6,540 | The crossing estimate (3.19): crossing probabilities of mixed-boundary squares are at least 1/(1 + q), via duality on the rotated lattice. |

## File index

One line per module, taken from the module documentation (or, where a module has none, its first declarations).

### Frozen

| Module | Summary |
|---|---|
| [`Theorem11`](Frozen/Theorem11.lean) | Theorem statement `potts_theorem_1_1` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Theorem12`](Frozen/Theorem12.lean) | Theorem statement `rc_theorem_1_2` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Theorem12Eq13`](Frozen/Theorem12Eq13.lean) | Theorem statement `rc_theorem_1_2_positivity_eq_1_3` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/Box`](Frozen/Defs/Box.lean) | Definition `box` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/DiagonalSite`](Frozen/Defs/DiagonalSite.lean) | Definition `diagonalSite` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/IsPottsInfiniteVolumeLimit`](Frozen/Defs/IsPottsInfiniteVolumeLimit.lean) | Definition `IsPottsInfiniteVolumeLimit` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/IsRCInfiniteVolumeLimit`](Frozen/Defs/IsRCInfiniteVolumeLimit.lean) | Definition `IsRCInfiniteVolumeLimit` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/IsTranslationErgodic`](Frozen/Defs/IsTranslationErgodic.lean) | Definition `IsTranslationErgodic` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/PottsCriticalBeta`](Frozen/Defs/PottsCriticalBeta.lean) | Definition `pottsCriticalBeta` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/PottsHamiltonian`](Frozen/Defs/PottsHamiltonian.lean) | Definition `pottsHamiltonian` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/PottsProb`](Frozen/Defs/PottsProb.lean) | Definition `pottsProb` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/RCCriticalParameter`](Frozen/Defs/RCCriticalParameter.lean) | Definition `rcCriticalParameter` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/RCFreeClusterCount`](Frozen/Defs/RCFreeClusterCount.lean) | Definition `rcFreeClusterCount` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/RCInfiniteOpenGraph`](Frozen/Defs/RCInfiniteOpenGraph.lean) | Definition `rcInfiniteOpenGraph` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/RCOpenGraph`](Frozen/Defs/RCOpenGraph.lean) | Definition `rcOpenGraph` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/RCProb`](Frozen/Defs/RCProb.lean) | Definition `rcProb` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/RCWeight`](Frozen/Defs/RCWeight.lean) | Definition `rcWeight` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/RCWiredClusterCount`](Frozen/Defs/RCWiredClusterCount.lean) | Definition `rcWiredClusterCount` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/SquareLattice`](Frozen/Defs/SquareLattice.lean) | Definition `squareLattice` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |
| [`Defs/VertexBoundary`](Frozen/Defs/VertexBoundary.lean) | Definition `vertexBoundary` (arXiv:1611.09877v2) This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two agree. |

### Provider

| Module | Summary |
|---|---|
| [`Theorem11`](Provider/Theorem11.lean) | Proof of Theorem 1.1 (`potts_theorem_1_1`) This module proves the exact statement of Theorem 1.1. |
| [`Theorem12`](Provider/Theorem12.lean) | Proof of Theorem 1.2, items 1–3 and (1.2) (`rc_theorem_1_2`) This module proves the exact statement of Theorem 1.2, items 1–3 including (1.2). |
| [`Theorem12Eq13`](Provider/Theorem12Eq13.lean) | Proof of Theorem 1.2, positivity and (1.3) (`rc_theorem_1_2_positivity_eq_1_3`) This module proves the exact statement of the final assertions of Theorem 1.2: positivity of the right side of (1.2) and the asymptotics (1.… |

### PottsThm

| Module | Summary |
|---|---|
| [`ColorNoiseMixing`](PottsThm/ColorNoiseMixing.lean) | Declarations: `DependsOnIndices`, `DependsOnIndices.mono`, `DependsOnIndices.compl`, `DependsOnIndices.union`, … |
| [`ColoringCylinderLaw`](PottsThm/ColoringCylinderLaw.lean) | Declarations: `iidFieldMeasure_injective_cylinder`, `iidFieldMeasure_quotient_cylinder`, `iidFieldMeasure_observedColoring_of_compatible`, `iidFieldMeasure_observedColoring_of_incompatible`, … |
| [`ColoringErgodicity`](PottsThm/ColoringErgodicity.lean) | Declarations: `mixingProduct_factor_translationErgodic` |
| [`ColoringFactor`](PottsThm/ColoringFactor.lean) | Declarations: `Vertex`, `vertexLex`, `vertexLex_translate_le_iff`, `clusterRepresentative`, … |
| [`ColoringPushforward`](PottsThm/ColoringPushforward.lean) | Declarations: `freeColoringMap_isFreeESC`, `wiredColoringMap_isWiredESC` |
| [`CriticalLimits`](PottsThm/CriticalLimits.lean) | Declarations: `exists_critical_coloured_limits` |
| [`CriticalParameters`](PottsThm/CriticalParameters.lean) | Declarations: `pottsCriticalBeta_pos`, `criticalFKParameters`, `fkCritical_toP_toQ` |
| [`DiscontinuityConsequences`](PottsThm/DiscontinuityConsequences.lean) | Declarations: `free_no_infinite_clusters`, `rc_discontinuity_of_positive_rate` |
| [`Distinctness`](PottsThm/Distinctness.lean) | Declarations: `critical_potts_limits_pairwise_distinct` |
| [`FreeCorrelationLimit`](PottsThm/FreeCorrelationLimit.lean) | Declarations: `rc_diagonal_connection_tendsto_zero_of_pos_rate`, `free_spin_correlation_tendsto_uniform` |
| [`LatticeColorNoise`](PottsThm/LatticeColorNoise.lean) | Declarations: `LatticeVertex`, `latticeShiftEquiv`, `eventually_latticeShift_disjoint` |
| [`MixtureSeparation`](PottsThm/MixtureSeparation.lean) | Declarations: `criticalFreeBoxLimit`, `criticalWiredBoxLimit`, `criticalInfiniteAt_translate`, `critical_potts_free_measure_ne_wired_average` |
| [`OneSite`](PottsThm/OneSite.lean) | Declarations: `optionUnit_setoid_top`, `optionUnit_setoid_bot`, `card_optionUnit_quotient_bot`, `wired_one_point_kernel_off_pin`, … |
| [`PottsColoringErgodicity`](PottsThm/PottsColoringErgodicity.lean) | Declarations: `clusterColoring_map_ergodic_of_RCmixing` |
| [`PottsTheorem11`](PottsThm/PottsTheorem11.lean) | Declarations: `probabilityMeasure_eq_of_spinCylinder_real`, `potts_theorem_1_1_of_rc_rate` |
| [`ProductErgodicity`](PottsThm/ProductErgodicity.lean) | Declarations: `measurableRectangles`, `measurableRectangles_isSetSemiring`, `measurableRectangles_generateFrom`, `measurableRectangleRing_generateFrom`, … |
| [`RateTransfer`](PottsThm/RateTransfer.lean) | Declarations: `free_spin_rate_of_rc_rate` |
| [`WiredAssociation`](PottsThm/WiredAssociation.lean) | Declarations: `wiredBoxConfiguration_mono`, `wiredBoxProbabilityMeasure_apply_preimage`, `wiredBoxProbabilityMeasure_finite_positive_association`, `wired_clopen_positive_association` |
| [`WiredCorrelation`](PottsThm/WiredCorrelation.lean) | Declarations: `pairClassLabel`, `falsePinClassLabel`, `truePinClassLabel`, `pairClassRel`, … |
| [`WiredInfiniteAssociation`](PottsThm/WiredInfiniteAssociation.lean) | Declarations: `wiredEscapeApprox`, `rcInfiniteOpenGraph_mono`, `wiredEscapeApprox_upper`, `wiredEscapeApprox_iInter`, … |

### Potts

| Module | Summary |
|---|---|
| [`BoolMeasureBridge`](Potts/BoolMeasureBridge.lean) | Declarations: `fk_measureReal_eq_bool_sum`, `finite_pmf_measureReal_sum` |
| [`BooleanDataLimits`](Potts/BooleanDataLimits.lean) | Positive connection moments determine every finite connection pattern. |
| [`BoxObservation`](Potts/BoxObservation.lean) | Local finite edge observations and their probabilities under box limits. |
| [`ClusterColoring`](Potts/ClusterColoring.lean) | Counting cluster colourings Colourings are functions constant on the classes of an explicit equivalence relation. |
| [`ColourKernelPartitions`](Potts/ColourKernelPartitions.lean) | Edwards–Sokal cylinder kernels as functions of finite observed partitions. |
| [`ConditionedComparison`](Potts/ConditionedComparison.lean) | Conditional comparisons for the literal boundary correction. |
| [`ConditionedConnectionLimit`](Potts/ConditionedConnectionLimit.lean) | Merged connection-data limits survive the literal corner correction. |
| [`ConditionedEventLimits`](Potts/ConditionedEventLimits.lean) | Transfer of connection-data limits through uniformly positive conditioning. |
| [`ConditionedOuterLaw`](Potts/ConditionedOuterLaw.lean) | The full conditioned outer law, including its boundary connection data. |
| [`CylinderColoring`](Potts/CylinderColoring.lean) | Cylinder probabilities of independent component colourings The probability of a prescribed finite spin pattern depends only on the connection partition of its observed vertices. |
| [`ESCylinderLaw`](Potts/ESCylinderLaw.lean) | Edwards–Sokal infinite-colouring laws characterized on every finite cylinder. |
| [`FiniteConditioning`](Potts/FiniteConditioning.lean) | Finite conditional probabilities and exterior-event decomposition. |
| [`FiniteEnergyBounds`](Potts/FiniteEnergyBounds.lean) | Finite-energy lower bounds for closed edge sets The FK single-edge finite-energy estimate iterates to a uniform lower bound for every prescribed finite set of edges to be closed. |
| [`FiniteExpansion`](Potts/FiniteExpansion.lean) | Finite Edwards–Sokal weight expansion This finite algebra applies to any list of spin agreement constraints. |
| [`FinitePartitionLimits`](Potts/FinitePartitionLimits.lean) | Finite connection partitions and expectations of their colouring kernels. |
| [`FreeBoundary`](Potts/FreeBoundary.lean) | Free Edwards–Sokal coupling for the frozen finite Potts law Boundary index zero makes every literal boundary field vanish, because the spin palette is `{1,...,q}`. |
| [`FreeBoxObservation`](Potts/FreeBoxObservation.lean) | Free finite-volume observations and their infinite-volume domination. |
| [`FreeConnectionEvents`](Potts/FreeConnectionEvents.lean) | Increasing finite-path events for free connection data. |
| [`FreeConnectionLimit`](Potts/FreeConnectionLimit.lean) | Free connection-data limits use actual connections, without merging. |
| [`FreeCylinderPartition`](Potts/FreeCylinderPartition.lean) | The exact finite free Potts cylinder is a function of the observed FK partition. |
| [`FreePottsLimit`](Potts/FreePottsLimit.lean) | Free Potts box limits and their Edwards–Sokal colouring identification. |
| [`FreeSpinFormula`](Potts/FreeSpinFormula.lean) | Corrected consequence 3: the free spin correlation and actual RC connectivity. |
| [`FreeSpinObservations`](Potts/FreeSpinObservations.lean) | General finite observations of any free Potts box limit. |
| [`GhostBoundary`](Potts/GhostBoundary.lean) | The literal boundary model as a pinned ghost colouring The vertex `none` is the ghost. |
| [`GhostBoxConditional`](Potts/GhostBoxConditional.lean) | Exact conditional cylinder probabilities for the literal ghost boundary. |
| [`GhostBoxContraction`](Potts/GhostBoxContraction.lean) | Contraction of the wired outer shell, including its exact component partition. |
| [`GhostBoxCorners`](Potts/GhostBoxCorners.lean) | The four corner edges omitted by the literal boundary term. |
| [`GhostBoxCylinders`](Potts/GhostBoxCylinders.lean) | Whole-lattice extensions and cylinders for the literal ghost law. |
| [`GhostBoxEdgeSplit`](Potts/GhostBoxEdgeSplit.lean) | Classification of the outer-box edges into literal bonds, cuts, and shell edges. |
| [`GhostBoxGeometry`](Potts/GhostBoxGeometry.lean) | Exact geometry of one ghost bond per boundary vertex of a square box. |
| [`GhostBoxLaw`](Potts/GhostBoxLaw.lean) | Exact ghost law as a marginal of the conditioned outer wired FK law. |
| [`GhostBoxLimit`](Potts/GhostBoxLimit.lean) | The literal ghost edge law converges to the wired FK box limit. |
| [`GhostConnectionLaw`](Potts/GhostConnectionLaw.lean) | The conditioned outer law preserves the full marked ghost connection data. |
| [`GhostCylinder`](Potts/GhostCylinder.lean) | Exact ghost cylinder formula for the frozen Potts law The spin carrier remains the original finite vertex set. |
| [`GhostCylinderPartition`](Potts/GhostCylinderPartition.lean) | Exact literal Potts cylinders as expectations of marked connection partitions. |
| [`GhostPartitionExpectation`](Potts/GhostPartitionExpectation.lean) | Exact expectations of marked partitions under the literal ghost representation. |
| [`GraphCoupling`](Potts/GraphCoupling.lean) | Finite free Edwards–Sokal coupling Open bonds enforce agreement of their endpoint colours. |
| [`InfinitePartitionMeasurability`](Potts/InfinitePartitionMeasurability.lean) | Declarations: `infiniteFreePartition_measurableSet`, `infiniteWiredPartition_measurableSet` |
| [`LimitCompactness`](Potts/LimitCompactness.lean) | Compactness from convergence of spin cylinder probabilities On the compact spin configuration space, convergence of every finite cylinder probability determines the weak limit of a sequence of probability measures. |
| [`LiteralBoundary`](Potts/LiteralBoundary.lean) | Joint spin-bond law for the literal Potts boundary term The bond index consists of the induced lattice edges and exactly one additional bond for each boundary vertex. |
| [`LocalFreeConnections`](Potts/LocalFreeConnections.lean) | Actual free connection data is the increasing limit of finite open paths. |
| [`LocalWiredConnections`](Potts/LocalWiredConnections.lean) | Finite wired connection graphs bracket the merged infinite relation. |
| [`MergedConnectionData`](Potts/MergedConnectionData.lean) | Infinite connection data with all infinite clusters in one marked class. |
| [`MonotoneEventLimits`](Potts/MonotoneEventLimits.lean) | Diagonal limits of increasing and decreasing connection approximations. |
| [`NestedBoxComparison`](Potts/NestedBoxComparison.lean) | The domain comparison for the actual frozen boxes and corner correction. |
| [`ObservedPartitionLimits`](Potts/ObservedPartitionLimits.lean) | Distributions and expectations of finite observed connection partitions. |
| [`OutsideComparison`](Potts/OutsideComparison.lean) | Domain-Markov comparison retaining an arbitrary event on exterior edges. |
| [`Parameters`](Potts/Parameters.lean) | Edwards–Sokal parameters The bond probability is `1 - exp (-β)`. |
| [`PartitionExpectationAlgebra`](Potts/PartitionExpectationAlgebra.lean) | Expectations of the affine connection indicators in the spin identities. |
| [`PottsBoxLaws`](Potts/PottsBoxLaws.lean) | Actual Potts box laws on a common spin configuration space. |
| [`PottsLimitConstruction`](Potts/PottsLimitConstruction.lean) | Assemble actual frozen Potts limits from proved real cylinder limits. |
| [`PottsWeakLimit`](Potts/PottsWeakLimit.lean) | The frozen cylinder-limit predicate determines weak convergence of the box laws. |
| [`SpinEventDecomposition`](Potts/SpinEventDecomposition.lean) | Declarations: `measureReal_same_colour_sum` |
| [`SpinKernels`](Potts/SpinKernels.lean) | One-point pinned and two-point free colouring kernels, with the corrected factors. |
| [`SpinObservation`](Potts/SpinObservation.lean) | Finite observations of the actual Potts box measures. |
| [`WiredConnectionEvents`](Potts/WiredConnectionEvents.lean) | Increasing clopen events encoding finite wired connection data. |
| [`WiredConnectionLimit`](Potts/WiredConnectionLimit.lean) | Convergence of wired connection data with every infinite cluster merged. |
| [`WiredGhostRelation`](Potts/WiredGhostRelation.lean) | Exact marked-component relation in the conditioned outer ghost representation. |
| [`WiredPottsLimit`](Potts/WiredPottsLimit.lean) | Literal positive-boundary Potts limits and merged Edwards–Sokal colouring. |
| [`WiredSpinFormula`](Potts/WiredSpinFormula.lean) | Corrected consequence 2: the boundary-colour probability and wired percolation. |
| [`WiredSpinObservations`](Potts/WiredSpinObservations.lean) | General finite marked observations of any literal positive-boundary Potts limit. |

### RCMProof

| Module | Summary |
|---|---|
| [`BetheAssembly`](RCMProof/BetheAssembly.lean) | Theorem 1.3 ratio limit at the critical six-vertex parameter The assembly uses Theorem 2.3 to select the two symmetric Bethe families, the Fourier eigenvalue-ratio limit for both parities (`Bethe/Ratio*`), and the proved… |
| [`Contracts`](RCMProof/Contracts.lean) | Source-level provider interfaces for the Theorem 1.2 assembly This file records, as propositions, the lower-level statements consumed by the Theorem 1.2 assembly: Corollary 3.13(i)–(iii), equations (3.15), (3.16) and (3.… |
| [`Cor313Adapters`](RCMProof/Cor313Adapters.lean) | Declarations: `weightedMass_eq_correctedWeight`, `correspondenceScale_eq_normalization`, `contract_cor313_i_proved`, `contract_cor313_ii_proved`, … |
| [`DominanceAssembly`](RCMProof/DominanceAssembly.lean) | Declarations: `upperLoopFactor`, `upperLoopFactor_eq_densityWeight`, `upperLoopFactor_le_one`, `upperTailRateE`, … |
| [`ExactOneWitness`](RCMProof/ExactOneWitness.lean) | A finite configuration witnessing the exact-one vertical-winding event on large widths divisible by eight. |
| [`FinalAssembly`](RCMProof/FinalAssembly.lean) | Theorem 1.2 final assembly from its item-3 input This module proves the box-limit and discontinuity assembly after the analytic item-3 rate statement has been established for every free limit. |
| [`Item3`](RCMProof/Item3.lean) | Declarations: `rcItem3ForEveryFreeLimit_proved` |
| [`Lemma314Adapters`](RCMProof/Lemma314Adapters.lean) | Declarations: `corrected_lemma314_proved`, `lemma314_square_boundary_decay_of_nonpercolation`, `windingLoopDensityLogRate_abs_bounded`, `lemma314_limsup_and_one_arm_cutoff` |
| [`RouteB`](RCMProof/RouteB.lean) | Declarations: `routeBRotatedBoundaryEvent`, `routeBSquareBoundaryEvent`, `routeBSquareBoundaryTail`, `routeBSquareBoundaryEvent_measurable`, … |
| [`Theorem12Assembly`](RCMProof/Theorem12Assembly.lean) | Declarations: `rc_theorem_1_2_assembled` |
| [`TorusRCAdapters`](RCMProof/TorusRCAdapters.lean) | Declarations: `contract_eq315_proved` |
| [`XiLower`](RCMProof/XiLower.lean) | The lower bound on the inverse correlation length The first lemma converts the exact-one-winding probability into a six-vertex sector ratio. |

### Analysis

| Module | Summary |
|---|---|
| [`Asymptotic13`](Analysis/Asymptotic13.lean) | The asymptotics (1.3) of the hyperbolic series For `lam(q) = arcosh (√q / 2)` and `T(lam) = ∑_{k ≥ 0} 4 / ((2k+1) sinh (π² (2k+1) / (2 lam)))` we prove `T(lam(q)) ~ 8 exp (-(π² / √(q - 4)))` as `q → 4⁺` (`asymptotic13`). |
| [`HyperbolicSeries`](Analysis/HyperbolicSeries.lean) | Partial-fraction series for `coth`, `tanh` and `1 / sinh` All identities are derived from Mathlib's Mittag-Leffler expansion of the cotangent (`cot_series_rep'`). |
| [`Identity44`](Analysis/Identity44.lean) | The identity (4.4): convergence, positivity and the value of the alternating tanh series For every `lam > 0`, the partial sums `∑_{k=1}^N (-1)^k / k * tanh (k lam)` converge to a limit `S`, the series `∑_{k ≥ 0} 4 / ((2k… |
| [`Section4Series`](Analysis/Section4Series.lean) | Section 4 logarithmic series and identity (4.3) This module proves the ordered partial-sum expansion of `log (cosh λ)` and then derives equation (4.3) using the previously proved `identity44`. |
| [`Section4SourceIntegral`](Analysis/Section4SourceIntegral.lean) | The source-coordinate logarithmic derivative integral This file transports the Abel-summed Fourier computation from the `α` coordinate to the source coordinate `x = k(α)`. |
| [`Section4TauIntegral`](Analysis/Section4TauIntegral.lean) | The explicit τ integral in Section 4 The literal τ series is interpreted by its ordered partial sums. |

### Bethe

| Module | Summary |
|---|---|
| [`Asymptotic26`](Bethe/Asymptotic26.lean) | Theorem 2.6: convergence of the empirical integrals The positive root count is written `k i + 1`; the count identity `N i = 2 * (k i + 1 + r)` is precisely `n=N/2-r`. |
| [`Asymptotic26Cast`](Bethe/Asymptotic26Cast.lean) | Theorem 2.6 with an arbitrary positive root count |
| [`Asymptotic29`](Bethe/Asymptotic29.lean) | Theorem 2.9 for `N ∈ 4ℕ` The families are indexed by a sequence of sizes tending to infinity. |
| [`Asymptotic29Control`](Bethe/Asymptotic29Control.lean) | The linear bound in Theorem 2.9 |
| [`AsymptoticAlignment`](Bethe/AsymptoticAlignment.lean) | Alignment estimates before the offset Taylor expansion |
| [`AsymptoticBoundary`](Bethe/AsymptoticBoundary.lean) | Exact boundary and bulk decomposition for both offset parities |
| [`AsymptoticBoundaryLimit`](Bethe/AsymptoticBoundaryLimit.lean) | Limit of the finite missing-root contribution |
| [`AsymptoticCompactness`](Bethe/AsymptoticCompactness.lean) | Arzelà--Ascoli applied to continuous offset envelopes |
| [`AsymptoticDefs`](Bethe/AsymptoticDefs.lean) | Definitions for the asymptotics of discrete Bethe roots This module records the objects in (2.3), (2.5), and (2.13) of arXiv:1611.09877v2. |
| [`AsymptoticDiscreteExpansion`](Bethe/AsymptoticDiscreteExpansion.lean) | The discrete offset equation with a uniform Taylor error |
| [`AsymptoticEndpoint`](Bethe/AsymptoticEndpoint.lean) | Fixed-rank roots approach the endpoints |
| [`AsymptoticGeometry`](Bethe/AsymptoticGeometry.lean) | Geometric estimates derived from the source density rate |
| [`AsymptoticGronwall`](Bethe/AsymptoticGronwall.lean) | A centered discrete Gronwall estimate |
| [`AsymptoticInterpolation`](Bethe/AsymptoticInterpolation.lean) | Canonical continuous extensions of the root offsets The finite McShane envelope is a total, explicitly defined function. |
| [`AsymptoticLimitEquation`](Bethe/AsymptoticLimitEquation.lean) | Identification of the limiting offset equation |
| [`AsymptoticLimitTools`](Bethe/AsymptoticLimitTools.lean) | Moving continuous tests for empirical sums |
| [`AsymptoticMeanTaylor`](Bethe/AsymptoticMeanTaylor.lean) | The averaged Taylor expansion, uniform in both offset parities |
| [`AsymptoticNearRoots`](Bethe/AsymptoticNearRoots.lean) | From mean alignment to alignment of both shifted roots |
| [`AsymptoticNorm`](Bethe/AsymptoticNorm.lean) | Pointwise estimates from the weighted density norm The estimates here use convergence to zero, without imposing a rate. |
| [`AsymptoticOffset`](Bethe/AsymptoticOffset.lean) | Symmetry and aligned roots for the offset displacement |
| [`AsymptoticOffsetControl`](Bethe/AsymptoticOffsetControl.lean) | Spatial control of the offset step function |
| [`AsymptoticPartition`](Bethe/AsymptoticPartition.lean) | Cyclic root cells and their gap estimates |
| [`AsymptoticProducts`](Bethe/AsymptoticProducts.lean) | Root values and products in the uniform limit argument |
| [`AsymptoticQuadrature`](Bethe/AsymptoticQuadrature.lean) | Quadrature on the interior root cells The boundary intervals are estimated separately. |
| [`AsymptoticRegularity`](Bethe/AsymptoticRegularity.lean) | Compact derivative estimates for the offset argument All bounds here are for a fixed `Δ < -1`, which is the parameter scope of Theorem 2.9. |
| [`AsymptoticSpacing`](Bethe/AsymptoticSpacing.lean) | Spacing errors and the non-circular offset recurrence |
| [`AsymptoticSpatial`](Bethe/AsymptoticSpatial.lean) | Linear control and asymptotic equicontinuity of the step offsets |
| [`AsymptoticSubsequenceLimit`](Bethe/AsymptoticSubsequenceLimit.lean) | Every uniform subsequential limit is the offset-equation solution |
| [`AsymptoticSumSplit`](Bethe/AsymptoticSumSplit.lean) | Bulk and boundary sums for the offset expansion |
| [`AsymptoticTaylor`](Bethe/AsymptoticTaylor.lean) | Uniform phase Taylor estimates in the original root coordinates |
| [`AsymptoticUniformConvergence`](Bethe/AsymptoticUniformConvergence.lean) | Compactness and uniqueness imply convergence of the whole family |
| [`AsymptoticUniformOffset`](Bethe/AsymptoticUniformOffset.lean) | Uniform offset bounds from density errors |
| [`DiscreteAnalysis`](Bethe/DiscreteAnalysis.lean) | Discrete Bethe matrix estimates independent of `ρ` This file isolates the sign and calculus estimates for the phase difference used in the discrete diagonal-dominance argument. |
| [`DiscreteBase`](Bethe/DiscreteBase.lean) | The discrete Bethe equations at `Δ = -∞` At the inverse parameter `ε=0`, the phase is `Θ(x,y)=y-x`. |
| [`DiscreteCore`](Bethe/DiscreteCore.lean) | Discrete Bethe map and its symmetric domain This file formalizes the finite dimensional definitions in Section 2.2 of arXiv:1611.09877v2. |
| [`DiscreteJacobian`](Bethe/DiscreteJacobian.lean) | Finite matrices in the discrete Bethe argument The entries below are the source's displayed symmetric-coordinate matrix and its gap rescaling. |
| [`FourierPoisson`](Bethe/FourierPoisson.lean) | Fourier analysis of the Poisson kernel `Ξ_μ` on `[-π, π]` Source: arXiv:1611.09877v2, §2.1 (proof of Proposition 2.1) and §4 (Fourier computations). |
| [`FourierSaw`](Bethe/FourierSaw.lean) | The sawtooth series and the closed form of `Ψ` * `integral_id_mul_sin`: `∫_{-π}^{π} β sin(mβ) dβ = -2π (-1)^m/m`; * `sawS μ α = ∑_{m ≥ 1} 2 (-1)^m e^{-μ m} sin(mα)/m` and `xiConv_neg_id`: the Poisson convolution of the s… |
| [`FourierSawtooth`](Bethe/FourierSawtooth.lean) | The sawtooth series `∑ (-1)^m sin(mα)/m = -α/2` for `\|α\| < π` The series is only conditionally convergent. |
| [`FourierSech`](Bethe/FourierSech.lean) | The hyperbolic secant: Fourier transform and Poisson summation Source: arXiv:1611.09877v2, §4 (Fourier computations), the identity `1 / cosh(λ m) = (1 / (2 λ)) ∫_ℝ e^{-i m α} / cosh(π α / (2 λ)) dα` and the periodisation… |
| [`FourierTrig`](Bethe/FourierTrig.lean) | Absolutely convergent trigonometric series and the Poisson convolution For absolutely summable coefficient sequences `a, b`, the series `trigSeries a₀ a b α = a₀ + ∑_{n ≥ 0} (a n cos((n+1)α) + b n sin((n+1)α))` is contin… |
| [`KMap`](Bethe/KMap.lean) | The map `k` of arXiv:1611.09877v2, §2.1 (change of variable `x = k(α)`) For `Δ < -1` let `λ > 0` with `cosh λ = -Δ`. |
| [`Prop21Coeff`](Bethe/Prop21Coeff.lean) | Complex Fourier coefficients of §4 for Proposition 2.1 `hatCoef f m = (1/2π) ∫_{-π}^{π} e^{-imα} f(α) dα` is the Fourier coefficient of the source. |
| [`Prop21Defs`](Bethe/Prop21Defs.lean) | Proposition 2.1: the equations (cBE_Δ), (cOE_Δ) and the change of variables `x = k(α)` Source: arXiv:1611.09877v2, §2.1 (equations (cBE_Δ), (cOE_Δ) and the proof of Proposition 2.1). |
| [`Prop21Positivity`](Bethe/Prop21Positivity.lean) | Proposition 2.1: positivity of `ρ` and the uniform lower bound `m_ρ` * `rho_pos`: `ρ_Δ(x) > 0` for every `Δ < -1` and every `x` (all terms of the sum in (2.1) are positive and `k' = Ξ_λ > 0`); * `rho_uniform_lower_bound`… |
| [`Prop21Regularity`](Bethe/Prop21Regularity.lean) | Proposition 2.1: regularity of `ρ` * `continuous_rho` (in `Prop21Rho`): `x ↦ ρ_Δ(x)` is continuous; * `analyticAt_rho`: for fixed `Δ < -1`, `x ↦ ρ_Δ(x)` is real analytic. |
| [`Prop21Rho`](Bethe/Prop21Rho.lean) | Proposition 2.1 for `ρ`: the explicit solution of (cBE_Δ) and its uniqueness Source: arXiv:1611.09877v2, Proposition 2.1 and its proof (§2.1), with the Fourier computations of §4 (`R̂(m) = 1/(2 cosh(λ m))`). |
| [`Prop21Tau`](Bethe/Prop21Tau.lean) | Proposition 2.1 for `τ`: the explicit solution of (cOE_Δ) and its uniqueness Source: arXiv:1611.09877v2, Proposition 2.1 and its proof (§2.1), with the Fourier computations of §4 (`T̂(m) = ((-1)^m/(i m)) tanh(λ\|m\|)`, `Ψ̂… |
| [`RatioAnySign`](Bethe/RatioAnySign.lean) | Sign-invariant formulation for the parameter `c` |
| [`RatioBoundary`](Bethe/RatioBoundary.lean) | Endpoint factors in the eigenvalue ratio Fixed-rank roots converge to `-π`. |
| [`RatioBulk29`](Bethe/RatioBulk29.lean) | The source bulk log-product limit under the exact Theorem 2.9 premises |
| [`RatioBulkBounds`](Bethe/RatioBulkBounds.lean) | Uniform domination of the actual logarithmic quadrature tests |
| [`RatioBulkLimit`](Bethe/RatioBulkLimit.lean) | Dominated convergence for the singular logarithmic root sum This module assembles the general analytic moving-test argument. |
| [`RatioBulkPointwise`](Bethe/RatioBulkPointwise.lean) | Pointwise convergence of the logarithmic quadrature tests This general calculus lemma takes a root-density limit and a scaled displacement limit. |
| [`RatioCentralGeometry`](Bethe/RatioCentralGeometry.lean) | Central symmetry and separation of the positive roots |
| [`RatioCentralScaling`](Bethe/RatioCentralScaling.lean) | Fixed positive ranks at the central scale Only density norm convergence and a vanishing mesh are needed for the fixed-rank limits. |
| [`RatioDensityLimits`](Bethe/RatioDensityLimits.lean) | Density consequences used in the source-family specialization |
| [`RatioDensityMoving`](Bethe/RatioDensityMoving.lean) | Moving-point density limits and central root gaps |
| [`RatioEvenAlgebra`](Bethe/RatioEvenAlgebra.lean) | The exact finite even-ratio factorization (3.7) |
| [`RatioEvenLimit`](Bethe/RatioEvenLimit.lean) | The complete even-deficit eigenvalue ratio limit |
| [`RatioFourierLimit`](Bethe/RatioFourierLimit.lean) | Section 4 Fourier composition for the even eigenvalue-ratio limit |
| [`RatioInteriorQuadrature`](Bethe/RatioInteriorQuadrature.lean) | Interior-cell quadrature for varying root tests Unlike Theorem 2.6's continuous fixed tests, the values attached to the roots here may vary arbitrarily. |
| [`RatioLogDifference`](Bethe/RatioLogDifference.lean) | Mean-value control of the singular logarithmic differences |
| [`RatioMidpointBounds`](Bethe/RatioMidpointBounds.lean) | Summable bounds for the logarithms of odd midpoint factors |
| [`RatioMidpointLimit`](Bethe/RatioMidpointLimit.lean) | The source odd midpoint product tends to 2/π The zero midpoint is omitted. |
| [`RatioMidpointPointwise`](Bethe/RatioMidpointPointwise.lean) | Half-integer root scales give the logarithmic Wallis factors |
| [`RatioOddCoefficient`](Bethe/RatioOddCoefficient.lean) | The zero-root prefactor: positivity and its leading asymptotic Source: Section 3.2 of arXiv:1611.09877v2, proof of (1.7) for odd `r`: the prefactor (A) of `Λ_r(N) / Λ₀(N)` and its asymptotic `(A) = (c²/2) · 2πρ(0) N + o(… |
| [`RatioOddLimit`](Bethe/RatioOddLimit.lean) | The complete odd-deficit eigenvalue ratio limit |
| [`RatioOddLogCorrection`](Bethe/RatioOddLogCorrection.lean) | Exact logarithmic bookkeeping for the odd aligned-root quotient |
| [`RatioOddQuotient`](Bethe/RatioOddQuotient.lean) | Exact five-factor expression for the odd eigenvalue quotient |
| [`RatioOddSums`](Bethe/RatioOddSums.lean) | Finite reflection and telescoping identities for the odd quotient |
| [`RatioOffsetProjection`](Bethe/RatioOffsetProjection.lean) | The canonical root projection recovers the source offset function |
| [`RatioPole`](Bethe/RatioPole.lean) | The central simple pole of the spectral factor The regular part is given by an explicit sinc formula. |
| [`RatioPositiveRoots`](Bethe/RatioPositiveRoots.lean) | The positive half of the source full-root family |
| [`RatioPredecessor`](Bethe/RatioPredecessor.lean) | Canonical left-root projection for the interior quadrature The projection chooses the last root at or to the left of x. |
| [`RatioProducts`](Bethe/RatioProducts.lean) | Symmetric products in the two Bethe eigenvalue formulas Source: Section 3.2 of arXiv:1611.09877v2 (proof of Theorem 1.3): the formula `Λ₀(N) = 2 ∏ \|M(e^{i p_j})\|` in the proof of (1.6), and the factorization of `Λ_r(N) /… |
| [`RatioProfile`](Bethe/RatioProfile.lean) | The logarithmic spectral profile and its singular derivative The value at zero is the total Lean value of the original spectral formula; all differential assertions are on the punctured fundamental interval. |
| [`RatioScaledIncrement`](Bethe/RatioScaledIncrement.lean) | Moving pairs of roots and scaled logarithmic increments |
| [`RatioSecondDerivative`](Bethe/RatioSecondDerivative.lean) | Second derivative control for the odd midpoint correction |
| [`RatioTruncation`](Bethe/RatioTruncation.lean) | Quantitative truncation at the logarithmic singularity Root-spacing and root-offset estimates are kept separate from the spectral profile: this finite estimate applies to every derivative with `\|x l'(x)\|` bounded. |
| [`RatioWallis`](Bethe/RatioWallis.lean) | Tannery's theorem and the Wallis constant in the odd correction |
| [`Theorem23`](Bethe/Theorem23.lean) | Theorem 2.3 in the even-size formulation of the source |
| [`Theorem23Admissible`](Bethe/Theorem23Admissible.lean) | Compact regions of separated symmetric configurations |
| [`Theorem23Base`](Bethe/Theorem23Base.lean) | The unique base fiber and its cyclic gap estimates |
| [`Theorem23Bootstrap`](Bethe/Theorem23Bootstrap.lean) | Mesh bootstrap for compact continuation |
| [`Theorem23CompactIFT`](Bethe/Theorem23CompactIFT.lean) | Compact continuation of analytic implicit roots |
| [`Theorem23Comparison`](Bethe/Theorem23Comparison.lean) | Comparing the step density with the derivative of the counting function |
| [`Theorem23Continuation`](Bethe/Theorem23Continuation.lean) | Compact continuation of locally unique roots This topological lemma isolates the compactness step in continuation. |
| [`Theorem23ContinuousEstimate`](Bethe/Theorem23ContinuousEstimate.lean) | Continuous contraction applied to the discrete density |
| [`Theorem23Contraction`](Bethe/Theorem23Contraction.lean) | Poisson contraction with an explicit mass defect |
| [`Theorem23Coordinates`](Bethe/Theorem23Coordinates.lean) | Explicit coordinates on the symmetric root subspace |
| [`Theorem23Counting`](Bethe/Theorem23Counting.lean) | The smooth counting function in the proof of Lemma 2.4 |
| [`Theorem23Density`](Bethe/Theorem23Density.lean) | Basic consequences of the Bethe density norm This module reuses the definitions of (2.3) and (2.5) from `AsymptoticDefs.lean`. |
| [`Theorem23Derivative`](Bethe/Theorem23Derivative.lean) | The coordinate residual and its Frechet derivative |
| [`Theorem23Diagonal`](Bethe/Theorem23Diagonal.lean) | Diagonal estimates for the rescaled Bethe Jacobian |
| [`Theorem23Dominance`](Bethe/Theorem23Dominance.lean) | Actual diagonal dominance from a uniform mesh |
| [`Theorem23Family`](Bethe/Theorem23Family.lean) | The analytic family of Bethe roots |
| [`Theorem23FiniteQuadrature`](Bethe/Theorem23FiniteQuadrature.lean) | A finite left Riemann estimate from a derivative modulus |
| [`Theorem23GKernel`](Bethe/Theorem23GKernel.lean) | Uniform bounds for the kernel in the Jacobian row sums |
| [`Theorem23GapInterior`](Bethe/Theorem23GapInterior.lean) | Interior of the separated gap region |
| [`Theorem23HalfPartition`](Bethe/Theorem23HalfPartition.lean) | The half-root partition and its endpoints |
| [`Theorem23Inverse`](Bethe/Theorem23Inverse.lean) | Coordinate residual at the compactified parameter |
| [`Theorem23Kernel`](Bethe/Theorem23Kernel.lean) | Uniform bounds for the Bethe derivative kernel The explicit formula `thetaInv` is analytic on `\|ε\| < 1`. |
| [`Theorem23Local`](Bethe/Theorem23Local.lean) | Local analytic Bethe branches at regular solutions |
| [`Theorem23LocalSection`](Bethe/Theorem23LocalSection.lean) | Local sections in an admissible state region |
| [`Theorem23Mass`](Bethe/Theorem23Mass.lean) | Exact physical masses of the discrete and continuous densities |
| [`Theorem23MeanValue`](Bethe/Theorem23MeanValue.lean) | Exact counting increments and cell mean values for Bethe solutions |
| [`Theorem23Quadrature`](Bethe/Theorem23Quadrature.lean) | Quantitative quadrature against the root step density |
| [`Theorem23RegularRegion`](Bethe/Theorem23RegularRegion.lean) | All zeros in the compact Bethe region are interior and regular |
| [`Theorem23Rows`](Bethe/Theorem23Rows.lean) | Uniform approximation of the off-diagonal row sums |
| [`Theorem23Spacing`](Bethe/Theorem23Spacing.lean) | Density control of cyclic root gaps These are consequences of a weighted density error bound. |
| [`Theorem23StabilityEstimate`](Bethe/Theorem23StabilityEstimate.lean) | The counting-function contraction estimate (2.10) |
| [`Theorem23StrictGaps`](Bethe/Theorem23StrictGaps.lean) | Strict quantitative gap improvement at Bethe solutions |
| [`Theta`](Bethe/Theta.lean) | The Bethe phase `Θ` for `Δ < -1` Source: arXiv:1611.09877v2, equation (1.8) and footnote 2. |
| [`ThetaK`](Bethe/ThetaK.lean) | Footnote 5: `Θ(k(α), k(β))` and the derivative identities For `Δ < -1` and `λ > 0` with `cosh λ = -Δ`, the Bethe phase composed with the change of variable `x = k(α)`, `y = k(β)` is a function of `α - β` only: `Θ_Δ(k_λ(α… |

### BetheAnsatz

| Module | Summary |
|---|---|
| [`Amplitude`](BetheAnsatz/Amplitude.lean) | Adjacent transpositions in the coordinate Bethe amplitudes Companion paper, Lemma `lem:ratios`, equation (8). |
| [`BoundaryLimit`](BetheAnsatz/BoundaryLimit.lean) | The corrected scalar boundary limit in Lemma 3.7 of the companion paper In the proof of Lemma 3.7 (the limit of `T₀(ε)`) of the companion paper [8], arXiv:1611.09909 (The Bethe ansatz for the six-vertex and XXZ models: a… |
| [`Conventions`](BetheAnsatz/Conventions.lean) | Coordinates, nonzero amplitudes, and the full-matrix/block bridge The paper's positions `1,...,N` are our increasing `Fin N` positions plus one. |
| [`Cyclic`](BetheAnsatz/Cyclic.lean) | Cyclic permutation of the coordinate Bethe amplitudes Companion paper, Lemma `lem:ratios`, equation (11). |
| [`Defs`](BetheAnsatz/Defs.lean) | Coordinate Bethe Ansatz: the objects of Theorem 3.1 Main source: arXiv:1611.09877v2, Theorem 3.1. |
| [`GapGeometric`](BetheAnsatz/GapGeometric.lean) | Geometric sums in an integer gap Companion paper, equation `eq:EmptySetCalc`. |
| [`GapGeometry`](BetheAnsatz/GapGeometry.lean) | Finite cyclic gap configurations Companion paper, `cor:expressionRsi` and the domain of the sum `R_σ`. |
| [`GapInclusionExclusion`](BetheAnsatz/GapInclusionExclusion.lean) | Inclusion-exclusion for the finite cyclic gap sum Companion paper, equation `eq:RS`. |
| [`GapReindex`](BetheAnsatz/GapReindex.lean) | Reindexing cyclic gap tuples into the two ordinary orientations The sign of the first coordinate separates the two copies of the diagonal as well. |
| [`GapRestricted`](BetheAnsatz/GapRestricted.lean) | Restricted cyclic gap sums The constraints on a collision set separate coordinate by coordinate. |
| [`GapTransfer`](BetheAnsatz/GapTransfer.lean) | The actual transfer action as the cyclic gap sum Companion paper, Corollary `cor:expressionRsi`. |
| [`GapWeights`](BetheAnsatz/GapWeights.lean) | The gap weight equals the actual transfer weight Each gap coordinate agrees with a row particle modulo N exactly at a gap endpoint. |
| [`InterlacingCoordinates`](BetheAnsatz/InterlacingCoordinates.lean) | Coordinate conditions for the two transfer-action orientations The inequalities here use the unique increasing integer coordinates of the actual states. |
| [`NonconstantWords`](BetheAnsatz/NonconstantWords.lean) | Every nonconstant word cancels The finite line either contains an ordinary ML transition, or its end letters form the boundary ML transition. |
| [`OneParticle`](BetheAnsatz/OneParticle.lean) | The coordinate Bethe Ansatz in the zero- and one-particle sectors These are complete special cases of Theorem 3.1, with the actual transfer matrix and the coordinate wave of `Defs`. |
| [`OrderedPositions`](BetheAnsatz/OrderedPositions.lean) | Finite ordered integer coordinates for row states This is the finite reindexing between an actual n-particle row state and its unique strictly increasing coordinates in `[0,N)`. |
| [`Perturbation`](BetheAnsatz/Perturbation.lean) | Continuity of the finite gap sum under a fixed-amplitude perturbation The amplitudes are held at the original Bethe momenta. |
| [`Regular`](BetheAnsatz/Regular.lean) | The non-degenerate coordinate Bethe Ansatz The full transfer action is the finite gap sum. |
| [`Scattering`](BetheAnsatz/Scattering.lean) | Scalar scattering identities for the coordinate Bethe Ansatz Companion paper arXiv:1611.09909v1, Lemma `lem:ratios`, equation (6), and equation (19). |
| [`Toroidal`](BetheAnsatz/Toroidal.lean) | Toroidal change of variables Companion paper, Proposition `prop:changeOfVariables`. |
| [`TransferAction`](BetheAnsatz/TransferAction.lean) | Splitting the transfer action into the two interlacing orientations Companion paper, equation `eq:V_on_phi`. |
| [`WordCancellation`](BetheAnsatz/WordCancellation.lean) | Cancellation at ordinary ML edges The product form of the coefficient identity avoids dividing by word coefficients. |
| [`WordCoefficients`](BetheAnsatz/WordCoefficients.lean) | Collecting the word coefficients Pair each L coefficient with the preceding M coefficient. |
| [`WordRotation`](BetheAnsatz/WordRotation.lean) | Moving a boundary ML edge to an ordinary edge Rotate both the word and the lifted coordinates. |
| [`WordSwap`](BetheAnsatz/WordSwap.lean) | Swapping the two momenta at an ML edge Only one edge coefficient changes: the two momenta occur nowhere else in rσ(w). |
| [`Words`](BetheAnsatz/Words.lean) | Words in the restricted gap expansion A true letter denotes L and a false letter denotes M. |
| [`ZeroRootAlgebra`](BetheAnsatz/ZeroRootAlgebra.lean) | Bethe products with one zero root The zero-root Bethe equation and equation (19) imply equality of the products of L and M over the remaining roots. |
| [`ZeroRootGapLimit`](BetheAnsatz/ZeroRootGapLimit.lean) | The punctured gap-sum identity at a zero root Away from the singular value, the cyclic gap sum is exactly its finite word expansion. |
| [`ZeroRootPhases`](BetheAnsatz/ZeroRootPhases.lean) | Phase factors in the zero-root perturbation Changing one zero momentum to t multiplies a plane wave by the phase at the coordinate occupied by that root. |
| [`ZeroRootT0`](BetheAnsatz/ZeroRootT0.lean) | The two constant words in the zero-root limit This is the corrected T₀ calculation. |
| [`ZeroRootT0Limit`](BetheAnsatz/ZeroRootT0Limit.lean) | The corrected T₀ limit The singular constant-word factors are first combined. |
| [`ZeroRootT1Aggregate`](BetheAnsatz/ZeroRootT1Aggregate.lean) | The aggregate T₁ contribution after zipper reindexing The output index is equivalent to an output permutation together with an allowed ML-left slot. |
| [`ZeroRootT1Analytic`](BetheAnsatz/ZeroRootT1Analytic.lean) | Local analytic input for the paired T₁ limit The only pole in a paired ML-edge contribution is the moved-root factor `L(e^{it})`. |
| [`ZeroRootT1FinitePairs`](BetheAnsatz/ZeroRootT1FinitePairs.lean) | Finite sums of corrected T₁ pairs This module sums the already checked ordinary-edge and seam-pair limits over a finite type of canonical pair representatives. |
| [`ZeroRootT1Formula`](BetheAnsatz/ZeroRootT1Formula.lean) | Evaluation of the paired zero-root contribution The zipper reindexing separates the nonzero-root phase derivatives from the single cyclic seam indicator. |
| [`ZeroRootT1Ordinary`](BetheAnsatz/ZeroRootT1Ordinary.lean) | Ordinary-edge pairing in the zero-root perturbation With the amplitudes held at the original Bethe roots, an ordinary ML edge still has a pair relation. |
| [`ZeroRootT1OutputEquivalence`](BetheAnsatz/ZeroRootT1OutputEquivalence.lean) | The T₁ output-index equivalence The zipper sends a canonical pair to an output permutation whose zero slot is the unique LM endpoint. |
| [`ZeroRootT1OutputIndex`](BetheAnsatz/ZeroRootT1OutputIndex.lean) | Output indices for the global T₁ reindexing After zipping, the zero label is at the unique LM endpoint. |
| [`ZeroRootT1OutputInverse`](BetheAnsatz/ZeroRootT1OutputInverse.lean) | Reconstructing a canonical T₁ pair from its output index For an output permutation and a choice of ML-left slot, the original word is the cyclic interval from the right endpoint through the output zero slot. |
| [`ZeroRootT1Pairing`](BetheAnsatz/ZeroRootT1Pairing.lean) | Abstract cancellation of a simple pole against a first-order zero The paired T₁ summand has a pole of residue `i ĝ` and a factor vanishing to first order. |
| [`ZeroRootT1Phase`](BetheAnsatz/ZeroRootT1Phase.lean) | First derivative of the corrected T₁ phase For an ordinary ML edge, the paired quotient is `-exp(i(Θ(t,p)-Θ(0,p)))`. |
| [`ZeroRootT1RegularizedResidue`](BetheAnsatz/ZeroRootT1RegularizedResidue.lean) | The T₁ residue is the regularized word coefficient For a word with a unique cyclic ML edge, the pole residue at that edge is the product of the L/M weights with the zero-root slot omitted. |
| [`ZeroRootT1Residue`](BetheAnsatz/ZeroRootT1Residue.lean) | Residue and cancellation for an ordinary T₁ pair At an ordinary ML edge carrying the moved zero root on its L end, exactly one word-coefficient edge factor has a pole. |
| [`ZeroRootT1RunBoundary`](BetheAnsatz/ZeroRootT1RunBoundary.lean) | The unique LM edge of a T₁ word A cyclic binary word has equally many ML and LM edges. |
| [`ZeroRootT1RunPath`](BetheAnsatz/ZeroRootT1RunPath.lean) | A concrete zipper path for a canonical T₁ word In the cyclicly shifted coordinates, the L slots are the initial interval through the unique LM edge. |
| [`ZeroRootT1RunPermutation`](BetheAnsatz/ZeroRootT1RunPermutation.lean) | Permutation carried by a zero-root zipper run The successive adjacent swaps in the zipper run form one explicit permutation. |
| [`ZeroRootT1RunShape`](BetheAnsatz/ZeroRootT1RunShape.lean) | Linear shape of a canonical T₁ word after a cyclic shift Shift the unique ML edge to the end-to-start boundary. |
| [`ZeroRootT1SeamAmplitude`](BetheAnsatz/ZeroRootT1SeamAmplitude.lean) | The seam amplitude transposition Conjugating the seam swap by the cyclic rotation turns it into the ordinary swap of slots 0 and 1. |
| [`ZeroRootT1SeamPair`](BetheAnsatz/ZeroRootT1SeamPair.lean) | The corrected paired-term identity at the cyclic seam The seam pair has the same ordinary scattering increment, together with the additional `N t` phase produced by the wrapped coordinate. |
| [`ZeroRootT1SeamPhase`](BetheAnsatz/ZeroRootT1SeamPhase.lean) | The seam position-phase ratio At the seam, swapping the two momenta changes their positions by exactly `N`. |
| [`ZeroRootT1SeamResidue`](BetheAnsatz/ZeroRootT1SeamResidue.lean) | The seam residue and paired limit At a seam ML edge the unique pole is the cyclic edge from the last slot to slot zero. |
| [`ZeroRootT1ZipperFinalStep`](BetheAnsatz/ZeroRootT1ZipperFinalStep.lean) | Removing the last zero-root letter in the T₁ zipper When the unique zero momentum has reached an `L` slot, the remaining letter can be changed to `M` without a transposition: its singular factor is omitted from the regul… |
| [`ZeroRootT1ZipperRun`](BetheAnsatz/ZeroRootT1ZipperRun.lean) | A finite zero-root zipper run A zipper path is a non-repeating cyclic list of L slots, beginning at the slot carrying the zero root. |
| [`ZeroRootT1ZipperSeamStep`](BetheAnsatz/ZeroRootT1ZipperSeamStep.lean) | The cyclic seam zipper move The ordinary zipper identity also holds across the last-to-first edge. |
| [`ZeroRootT1ZipperStep`](BetheAnsatz/ZeroRootT1ZipperStep.lean) | Regularized zero-root word terms and an ordinary zipper move The corrected move takes an `L` at the zero-root slot across the next `L`, changing that letter to `M` and transposing the two momentum slots. |
| [`ZeroRootTheorem`](BetheAnsatz/ZeroRootTheorem.lean) | The degenerate zero-momentum Bethe Ansatz branch The coordinate identity is lifted to the full transfer matrix using the exact gap-sum representation on the particle block and support of the zero-extended vector away fro… |
| [`ZeroRootWordCancellation`](BetheAnsatz/ZeroRootWordCancellation.lean) | Cancellation away from the perturbed zero root The amplitudes remain at the original Bethe roots while word coefficients and phases use the perturbed tuple. |
| [`ZeroRootWordCancellationSum`](BetheAnsatz/ZeroRootWordCancellationSum.lean) | Cancellation on a fixed zero-root slot For a fixed word and a fixed slot occupied by the perturbed root, every ML edge disjoint from that slot pairs the constrained permutation sum with its negative. |
| [`ZeroRootWordFiniteSum`](BetheAnsatz/ZeroRootWordFiniteSum.lean) | Reindexing the fixed-amplitude word sum into root-slot fibers Every permutation occurs in exactly one fiber, determined by the slot carrying the distinguished label. |
| [`ZeroRootWordGoodFiber`](BetheAnsatz/ZeroRootWordGoodFiber.lean) | Root-incident fibers as the canonical T₁ index The condition that every ML edge of a nonconstant word touches the root slot is exactly the good fiber represented by one root-incident term index. |
| [`ZeroRootWordGoodFiberSum`](BetheAnsatz/ZeroRootWordGoodFiberSum.lean) | Finite indices for the surviving zero-root word terms The complete word expansion is indexed by a root slot, a word, and a constrained permutation. |
| [`ZeroRootWordLimit`](BetheAnsatz/ZeroRootWordLimit.lean) | The fixed-amplitude zero-root word-sum bridge The word expansion at a punctured perturbation is split into its constant, root-incident, and canceling fibers. |
| [`ZeroRootWordPartition`](BetheAnsatz/ZeroRootWordPartition.lean) | The finite index set of the zero-root T₁ residues A surviving word has a unique ML edge, and the perturbed root occupies one of its two endpoints. |

### SixVertex

| Module | Summary |
|---|---|
| [`BlockPerronFrobenius`](SixVertex/BlockPerronFrobenius.lean) | Perron–Frobenius eigenvalue of the blocks `V^{[n]}` and the rate of `Z^{(r)}_{6V}` For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` is symmetric, primitive and has a simple positive Perron–Frobenius eigenvalue with a stri… |
| [`Cor34Analytic`](SixVertex/Cor34Analytic.lean) | Corollary 3.4: analytic spectral tools This file formalizes the local uniqueness argument for an eigenvalue converging to a simple top root, the positive-vector pairing criterion, and the real-analytic identity principle… |
| [`Cor34BetheBase`](SixVertex/Cor34BetheBase.lean) | Corollary 3.4: Bethe wave and eigenvalue at infinity This module specializes the continuous regularizations to the discrete base momentum family. |
| [`Cor34BetheEigenvalue`](SixVertex/Cor34BetheEigenvalue.lean) | Corollary 3.4: normalized Bethe eigenvalue The inverse parameter is `ε = 1/Δ`. |
| [`Cor34BetheLimits`](SixVertex/Cor34BetheLimits.lean) | Corollary 3.4: specialize the Bethe eigenvalue limit at the discrete base This module identifies the generic continuous-family eigenvalue limits with the centered cyclotomic products in (3.5), then evaluates them for the… |
| [`Cor34BethePF`](SixVertex/Cor34BethePF.lean) | Corollary 3.4: conditional identification with the Perron root The eigenvector equation is an explicit premise corresponding to the Bethe ansatz theorem. |
| [`Cor34BetheWave`](SixVertex/Cor34BetheWave.lean) | Corollary 3.4: regularized Bethe wave at infinite anisotropy The parameter is `ε = 1/Δ`, and `-ε/2 = (-2Δ)⁻¹`. |
| [`Cor34Cyclotomic`](SixVertex/Cor34Cyclotomic.lean) | Corollary 3.4: cyclotomic determinant calculation The Vandermonde factor occurring in the cyclotomic calculation is nonzero whenever the primitive root has order strictly greater than the number of rows. |
| [`Cor34Final`](SixVertex/Cor34Final.lean) | Corollary 3.4: identify the Theorem 2.3 family with the Perron root |
| [`Cor34FinalAnalytic`](SixVertex/Cor34FinalAnalytic.lean) | Corollary 3.4: analytic Bethe branches near the endpoint |
| [`Cor34FinalEigen`](SixVertex/Cor34FinalEigen.lean) | Corollary 3.4: apply the coordinate Bethe Ansatz on the block |
| [`Cor34FinalEquations`](SixVertex/Cor34FinalEquations.lean) | Corollary 3.4: transfer the discrete Bethe data to Theorem 3.1 |
| [`Cor34FinalExistence`](SixVertex/Cor34FinalExistence.lean) | Endpoint and existence forms of Corollary 3.4 |
| [`Cor34FinalFamily`](SixVertex/Cor34FinalFamily.lean) | Corollary 3.4: discharge the conditional Bethe branch premise |
| [`Cor34FinalNormalization`](SixVertex/Cor34FinalNormalization.lean) | Corollary 3.4: normalize Theorem 3.1 for the infinite-anisotropy branch |
| [`Cor34FinalWave`](SixVertex/Cor34FinalWave.lean) | Corollary 3.4: nonvanishing of the normalized block wave |
| [`Cor34Spectral`](SixVertex/Cor34Spectral.lean) | Corollary 3.4: analytic spectral family This file proves the analyticity of the concrete Perron root on the finite-anisotropy range and records the normalized matrix family at infinite anisotropy. |
| [`Defs`](SixVertex/Defs.lean) | The six-vertex model on the torus and its transfer matrix: definitions Sources: arXiv:1611.09877v2, (1.4) (`eq:w_6V`), (1.5) (`eq:V`) and §3.3 (definition of `\|ω\|`, `Z_6V(N,M)` and `Z^{(r)}_{6V}(N,M)`); companion paper a… |
| [`InfinityChoices`](SixVertex/InfinityChoices.lean) | Admissible labelled defect choices and their upper row |
| [`InfinityCover`](SixVertex/InfinityCover.lean) | Positive eigenvectors and finite matrix covers The row-fiber identity is the precise weighted version of the covering condition. |
| [`InfinityCyclic`](SixVertex/InfinityCyclic.lean) | Cyclic relabelling of the real sine product |
| [`InfinityDefectMotion`](SixVertex/InfinityDefectMotion.lean) | Exact local motion of defects through a transfer row Horizontal arrows give a canonical labelled motion of every defect. |
| [`InfinityDescent`](SixVertex/InfinityDescent.lean) | Finite descent for independent row states |
| [`InfinityEigenvector`](SixVertex/InfinityEigenvector.lean) | The finite sine-product eigenvector equation |
| [`InfinityEndpointOrder`](SixVertex/InfinityEndpointOrder.lean) | Integer endpoint lifts of admissible defect choices |
| [`InfinityGround`](SixVertex/InfinityGround.lean) | The positive sine-product candidate on the original defect carrier The shifted coordinates are `X_j + j` and their circumference is `N + card(defects x)`. |
| [`InfinityHalfSpectrum`](SixVertex/InfinityHalfSpectrum.lean) | Half filling: largest eigenvalue and simplicity |
| [`InfinityIrreducible`](SixVertex/InfinityIrreducible.lean) | Irreducibility on independent row states A connected component has a minimum of the sum of occupied positions. |
| [`InfinityLiftedChoices`](SixVertex/InfinityLiftedChoices.lean) | Indexed choices and collision cancellation on shifted lifts |
| [`InfinityLimit`](SixVertex/InfinityLimit.lean) | The entrywise infinite-anisotropy limit Lemma 3.2 of arXiv:1611.09877v2 and its proof (the normalized limit `V^{[n]}_∞`). |
| [`InfinityMomentum`](SixVertex/InfinityMomentum.lean) | Evaluation of the centered momentum product |
| [`InfinityMoves`](SixVertex/InfinityMoves.lean) | Moves on independent row states Rotation is a genuine positive edge of the limiting matrix. |
| [`InfinityPerron`](SixVertex/InfinityPerron.lean) | Perron eigenvalue of the restriction and the full limiting block |
| [`InfinityPhase`](SixVertex/InfinityPhase.lean) | Exact phase of the centered Slater determinant |
| [`InfinitySlater`](SixVertex/InfinitySlater.lean) | The local free-fermion identity Slater determinants diagonalize simultaneous independent left/right moves on integer lifts. |
| [`InfinitySorting`](SixVertex/InfinitySorting.lean) | Canonical ordering of moved cyclic defect lifts |
| [`InfinitySupport`](SixVertex/InfinitySupport.lean) | Support of the infinite-anisotropy block The no-consecutive-up-arrow reduction in Lemma 3.2, including the cyclic seam. |
| [`InfinityValue`](SixVertex/InfinityValue.lean) | The exact largest eigenvalue at negative infinity (Lemma 3.2) |
| [`InfinityWeightComparison`](SixVertex/InfinityWeightComparison.lean) | The finite canonical weight equals the labelled lifted weight |
| [`Interlace`](SixVertex/Interlace.lean) | Interlacing via counting functions The interlacing relation `x_1 ≤ y_1 ≤ x_2 ≤ ⋯ ≤ x_n ≤ y_n` of (1.5) is equivalent to the pointwise inequalities `cnt y t ≤ cnt x t ≤ cnt y t + 1` between the counting functions `cnt x t… |
| [`Irreducible`](SixVertex/Irreducible.lean) | Irreducibility and primitivity of the blocks `V^{[n]}` For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` of the transfer matrix is irreducible and primitive (some power has all entries positive); this is the statement "eac… |
| [`LocalWeight`](SixVertex/LocalWeight.lean) | The weight `w(ω)` as a product of local vertex weights For an arrow configuration `ω`, `w(ω) = ∏_v localWeight(v)` where the local weight of a vertex is `a`, `b`, `c` according to its type and `0` if the vertex violates … |
| [`PathSum`](SixVertex/PathSum.lean) | Trace of a matrix power as a sum over closed chains For a square matrix `A` indexed by a finite type `S` and `m ≥ 1`, `tr (A ^ m) = ∑_{x : Fin m → S} ∏_{j : Fin m} A (x j) (x (j + 1 mod m))`. |
| [`RowTransfer`](SixVertex/RowTransfer.lean) | One row of the torus: the transfer matrix `Ṽ` equals `V` Companion paper arXiv:1611.09909v1, §4 (Lemma `lem:Interlacement` and Corollary `cor:MatrixEquality`). |
| [`Sec33Dominance`](SixVertex/Sec33Dominance.lean) | Abstract assembly of the six-vertex dominance gap The repaired large-width argument for the six-vertex dominance gap (Section 3.3) has external Potts-model inputs. |
| [`Sec33Partition`](SixVertex/Sec33Partition.lean) | Six-vertex sector maxima and trace bounds This file packages the finite-sector maximum of the block Perron roots and the trace estimates used in §3.3. |
| [`Sec33Ratios`](SixVertex/Sec33Ratios.lean) | Growth rates of six-vertex sector ratios The full partition function grows at the largest block Perron root. |
| [`Sec33RealAnalysis`](SixVertex/Sec33RealAnalysis.lean) | Exponential-growth comparison for the dominance repair This real-analysis lemma isolates the inequality behind the large-`N` repair. |
| [`Sec33Symmetry`](SixVertex/Sec33Symmetry.lean) | Arrow-flip symmetry of the six-vertex blocks The global arrow flip sends a row state to its complement. |
| [`TraceFormula`](SixVertex/TraceFormula.lean) | The trace formulas `Z_6V(N,M) = tr (V^M)` and `Z^{(r)}_{6V}(N,M) = tr ((V^{[N/2-r]})^M)` Companion paper [8], arXiv:1611.09909v1, Proposition 2.1 (proof in §4), and the main paper arXiv:1611.09877v2, §3.3 (the trace form… |
| [`TransferMatrix`](SixVertex/TransferMatrix.lean) | Elementary properties of the transfer matrix `V` and its blocks `V^{[n]}` * `V` is symmetric (`transferMatrix_transpose`), has nonnegative entries for `c ≥ 0`, and is block diagonal with respect to the number of up arrow… |

### LinearAlgebra

| Module | Summary |
|---|---|
| [`PerronFrobenius`](LinearAlgebra/PerronFrobenius.lean) | Perron-Frobenius theorems for real symmetric nonnegative matrices Public statements, for a finite nonempty index type `ι` and a real symmetric matrix `A : Matrix ι ι ℝ` (`hA : A.IsHermitian`, equivalent to `Aᵀ = A` by `M… |
| [`PerronFrobeniusGrowth`](LinearAlgebra/PerronFrobeniusGrowth.lean) | Perron-Frobenius growth: `(1/M) log tr (A ^ M) → log ρ` For a primitive symmetric nonnegative matrix `A` with largest eigenvalue `ρ = pfRoot A`: * `tendsto_log_trace_pow_primitive`: `(1/M) * log (trace (A ^ M)) → log ρ`;… |
| [`PerronFrobeniusIrreducible`](LinearAlgebra/PerronFrobeniusIrreducible.lean) | Perron-Frobenius for symmetric nonnegative matrices: the irreducible case Let `A : Matrix ι ι ℝ` be symmetric (`Matrix.IsHermitian`) with nonnegative entries over a finite nonempty index type, and write `ρ = pfRoot A` fo… |
| [`SymmetricSpectral`](LinearAlgebra/SymmetricSpectral.lean) | Spectral expansions for real symmetric matrices Helper layer for the Perron-Frobenius theorems of this directory. |

### AnalyticTools

| Module | Summary |
|---|---|
| [`Continuity`](AnalyticTools/Continuity.lean) | Continuity and analyticity of the largest eigenvalue The quantity `sSup (spectrum ℝ A)` is the largest eigenvalue for a real symmetric matrix. |
| [`EigenBranch`](AnalyticTools/EigenBranch.lean) | Analytic branches of simple characteristic roots The analytic implicit function theorem gives a local analytic branch from a jointly analytic characteristic-polynomial evaluation and an invertible derivative in the spect… |
| [`Identity`](AnalyticTools/Identity.lean) | Identity theorem for real analytic functions Two real analytic functions on a preconnected set agree everywhere if they agree on a nonempty open subset. |
| [`Implicit`](AnalyticTools/Implicit.lean) | Real analytic implicit functions in finite dimension For an equation `F (t, x) = 0`, the map `(t, x) ↦ (t, F (t, x))` has an invertible derivative whenever the derivative of `F` in `x` is invertible. |
| [`Inverse`](AnalyticTools/Inverse.lean) | Analytic inverse function theorem This module records the local analytic inverse theorem in the form needed by the Bethe equation argument. |

### Infra

| Module | Summary |
|---|---|
| [`CylinderUniqueness`](Infra/CylinderUniqueness.lean) | Uniqueness of cylinder limits A finite measure on a product of countable discrete spaces is determined by its values on the cylinder atoms `{σ \| ∀ x ∈ A, σ x = ξ x}`. |
| [`Lambda`](Infra/Lambda.lean) | The parameter `λ = arcosh(√q / 2)` For `q > 4`, `λ = arcosh(√q/2)` is the unique `λ > 0` with `cosh λ = √q / 2`. |
| [`RCWeightBasic`](Infra/RCWeightBasic.lean) | Basic facts about the finite-volume random-cluster weights On the source parameter range `p ∈ [0, 1]`, `q > 0`, every weight is nonnegative and the partition function is positive. |

### FK

| Module | Summary |
|---|---|
| [`AntitoneCylinderConvergence`](FK/AntitoneCylinderConvergence.lean) | Declarations: `probabilityMeasures_tendsto_of_antitone_allOpen` |
| [`BoundaryComparison`](FK/BoundaryComparison.lean) | Comparison under coarser boundary wiring The cross lattice condition is proved from the same actual component-merging calculation for two boundary partitions. |
| [`BoundaryPartitionLaw`](FK/BoundaryPartitionLaw.lean) | Declarations: `law_eq_of_boundary_partition_eq` |
| [`BoxCompactness`](FK/BoxCompactness.lean) | Subsequence compactness for the actual finite-box configuration laws The whole-lattice edge-state space is a countable product of the discrete finite space Bool. |
| [`BoxComparison`](FK/BoxComparison.lean) | Monotonicity of free box all-open cylinder probabilities The comparison is on the actual induced graphs. |
| [`BoxCylinders`](FK/BoxCylinders.lean) | Actual finite all-open cylinders The events refer to finitely many original whole-lattice edges. |
| [`BoxExhaustion`](FK/BoxExhaustion.lean) | Cofinality of increasing lattice boxes Nested exhaustive sequences of finite lattice boxes eventually contain each fixed finite lattice box. |
| [`BoxLaw`](FK/BoxLaw.lean) | The actual finite-box FK laws on the whole-lattice configuration carrier Every finite box is its genuine induced square-lattice graph. |
| [`BoxLimits`](FK/BoxLimits.lean) | Declarations: `latticeBox_origin_eq_box`, `frozenExtendedProbabilityMeasure_free`, `frozenExtendedProbabilityMeasure_wired`, `isRCInfiniteVolumeLimit_of_freeBox_tendsto`, … |
| [`BoxTranslation`](FK/BoxTranslation.lean) | Declarations: `boxVertexTranslationIso`, `latticeConfigurationTranslationHomeomorph`, `latticeConfigurationTranslate`, `latticeConfigurationTranslate_measurable`, … |
| [`ComponentBoundarySupport`](FK/ComponentBoundarySupport.lean) | Declarations: `componentSetoid_le_wired_union_of_edge_endpoints` |
| [`ComponentMerge`](FK/ComponentMerge.lean) | Opening an edge between distinct wired components The new quotient is explicitly identified with the old component quotient with one class removed. |
| [`ComponentSupermodular`](FK/ComponentSupermodular.lean) | Supermodularity of the actual wired component count Opening one edge merges two components precisely when its endpoints are not already identified. |
| [`ConditionalEmbeddedBoundaryUpper`](FK/ConditionalEmbeddedBoundaryUpper.lean) | Declarations: `filteredConditionalEmbeddedEvent_measure_le_boundary` |
| [`ConditionalEmbeddedLaw`](FK/ConditionalEmbeddedLaw.lean) | Declarations: `law_filter_frozen_map_embeddedRestriction` |
| [`ConditionalLaw`](FK/ConditionalLaw.lean) | The spatial Markov identity as actual PMF conditioning The existing finite FK law is filtered on the event fixing every edge in R. |
| [`ConfigurationBridge`](FK/ConfigurationBridge.lean) | Boolean configurations and finite open-edge sets These equivalences preserve the actual open graph and both edge counts. |
| [`CylinderConvergence`](FK/CylinderConvergence.lean) | Weak convergence from monotone finite cylinders On the compact whole-lattice configuration space, monotonicity of every finite all-open cylinder probability forces weak convergence of the probability laws. |
| [`CylinderDetermination`](FK/CylinderDetermination.lean) | Determination by finite all-open cylinders On the natural product measurable space of whole-lattice edge states, the probability of every finite all-open cylinder determines the probability law. |
| [`Disintegration`](FK/Disintegration.lean) | Exact decomposition over frozen edge states The marginal of the original frozen edges and the induced conditional FK law reconstruct the whole remaining-edge marginal. |
| [`DomainMarkov`](FK/DomainMarkov.lean) | Wiring induced by a frozen subset of original edges The induced partition is exactly original wiring joined with connectivity in the actually open frozen edges. |
| [`EdgeConditional`](FK/EdgeConditional.lean) | The exact law of an edge within a wired component Fix all edges except one original graph edge, whose endpoints are already in the same wired component. |
| [`EdgeRestriction`](FK/EdgeRestriction.lean) | The same-vertex graph obtained by deleting the nonsampled edges Deleting edges retains the entire original vertex type. |
| [`EmbeddedBoundaryUpper`](FK/EmbeddedBoundaryUpper.lean) | Declarations: `fkLaw_measure_toReal_eq_expectation`, `embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition` |
| [`EmbeddedClosedInteriorOuterBoundary`](FK/EmbeddedClosedInteriorOuterBoundary.lean) | Declarations: `removedEdge_endpoint_not_image_compl_general`, `isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior` |
| [`EmbeddedClosedInteriorOuterComparison`](FK/EmbeddedClosedInteriorOuterComparison.lean) | Declarations: `embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior` |
| [`EmbeddedMarginalLaw`](FK/EmbeddedMarginalLaw.lean) | Declarations: `embeddedConfigurationRestriction_union_subgraphRemoved`, `remainingLaw_map_embeddedRestriction`, `law_embeddedConfigurationRestriction_eq_bind_frozenMarginal` |
| [`EndpointLimits`](FK/EndpointLimits.lean) | The random-cluster limits at the two edge-parameter endpoints For every positive cluster weight and either boundary condition, the frozen finite-volume laws at `p = 0` and `p = 1` concentrate on the constant configuratio… |
| [`Events`](FK/Events.lean) | Finite FK events and actual open connectivity Every configuration has positive mass. |
| [`Expectation`](FK/Expectation.lean) | Real expectations of finite probability mass functions These are the literal finite weighted sums. |
| [`FiniteEnergy`](FK/FiniteEnergy.lean) | Declarations: `edgeRemovedBoolEquiv`, `configurationEdgeStateEquiv`, `configurationEdgeStateEquiv_symm_apply_false`, `configurationEdgeStateEquiv_symm_apply_true`, … |
| [`FreeBoxLimit`](FK/FreeBoxLimit.lean) | Declarations: `allOpen_mono_nnreal`, `freeBoxLimit_existsUnique` |
| [`FreeBoxLimitV1`](FK/FreeBoxLimitV1.lean) | Declarations: `freeBoxLimit_existsUnique` |
| [`FreeBoxPositiveAssociation`](FK/FreeBoxPositiveAssociation.lean) | Declarations: `boxConfiguration_mono`, `boxProbabilityMeasure_apply_preimage`, `boxProbabilityMeasure_finite_positive_association`, `freeBoxLimit_clopen_positive_association` |
| [`FreeBoxTranslation`](FK/FreeBoxTranslation.lean) | Declarations: `freeBoxLimit_translation_invariant` |
| [`FrozenBridge`](FK/FrozenBridge.lean) | Exact finite-volume bridge to the frozen random-cluster probabilities The graph is the frozen induced graph. |
| [`FrozenLimitBridge`](FK/FrozenLimitBridge.lean) | Declarations: `frozenEdgeEmbedding`, `patternCylinder`, `patternCylinder_isClopen`, `frozenExtendedProbabilityMeasure`, … |
| [`Graph`](FK/Graph.lean) | Finite FK graphs, actual paths, and boundary identifications The components in equation (1.2) of the source paper are classes of **all** vertices under the equivalence relation generated by open paths and the boundary pa… |
| [`IncreasingEvents`](FK/IncreasingEvents.lean) | FKG and wiring comparison for actual increasing events The finite sums are identified with the real-valued probabilities of the existing full power-set FK measure. |
| [`IsolatedBoundaryComponents`](FK/IsolatedBoundaryComponents.lean) | Declarations: `isolatedExtensionPullbackBoundary`, `isolatedExtensionExteriorBoundaryClasses`, `isolatedBoundaryComponentLabel`, `isolatedBoundaryLabel_of_hit`, … |
| [`IsolatedBoundaryLaw`](FK/IsolatedBoundaryLaw.lean) | Declarations: `weight_isolatedExtension_boundary_pullback`, `partitionFunction_isolatedExtension_boundary_pullback`, `configurationProbability_isolatedExtension_boundary_pullback`, `law_isolatedExtension_map_boundary_pullback` |
| [`IsolatedExtension`](FK/IsolatedExtension.lean) | Extending a finite free FK graph by isolated vertices An injective vertex map transports every original edge and adds no edges at the other vertices. |
| [`Isomorphism`](FK/Isomorphism.lean) | Declarations: `boundaryConditionIso`, `configurationIsoEdgeEquiv`, `configurationIso`, `configurationIso_val`, … |
| [`Lattice`](FK/Lattice.lean) | The square lattice and its finite closed boxes. |
| [`LimitTranslation`](FK/LimitTranslation.lean) | Translation invariance on the exact frozen carrier Uniqueness of the frozen cylinder characterization transfers the invariance of the canonical free and wired limits to every measure satisfying that characterization. |
| [`Marginal`](FK/Marginal.lean) | The exact marginal after removing prewired edges This proves the sampling equivalence on page 5 of the paper. |
| [`Model`](FK/Model.lean) | The finite random-cluster probability law Equation (1.2) of the source paper, including every isolated vertex in the boundary-wired component count. |
| [`Parameters`](FK/Parameters.lean) | Independent finite random-cluster parameters. |
| [`PositiveAssociation`](FK/PositiveAssociation.lean) | Positive association of the actual finite FK law The component count is the original wired quotient count, including isolated vertices. |
| [`Probability`](FK/Probability.lean) | Normalizing strictly positive weights on a finite configuration space This module supplies the elementary normalization used in equation (1.2) of the source paper. |
| [`ProbabilityProduct`](FK/ProbabilityProduct.lean) | Products and changes of carrier for finite normalized weights The product PMF is constructed by independently sampling the two given PMFs using mathlib's `bind` and `map`. |
| [`RemainingComparison`](FK/RemainingComparison.lean) | FKG and boundary comparison for the actual remaining-edge law The exact configuration order isomorphism transports the complete finite FK inequalities from the same-vertex deleted graph. |
| [`SingleEdgeLaw`](FK/SingleEdgeLaw.lean) | Exact one-edge FK conditional probabilities With every other edge fixed, the open probability is p if the endpoints are already connected after wiring and p/(p+(1-p)q) otherwise. |
| [`SubgraphComparison`](FK/SubgraphComparison.lean) | Free FK comparison under actual finite graph inclusions Configurations are transported along injective maps of original unordered edges. |
| [`VolumeComparison`](FK/VolumeComparison.lean) | Comparison of the original FK marginal with a graph with edges deleted Conditioning on the deleted edges induces a coarser partition than the original one. |
| [`WiredBoxComparison`](FK/WiredBoxComparison.lean) | Wired box laws decrease on increasing cylinder events as the domain grows. |
| [`WiredBoxLaw`](FK/WiredBoxLaw.lean) | Wired finite-box FK laws on the common whole-lattice carrier. |
| [`WiredBoxLimits`](FK/WiredBoxLimits.lean) | A common weak limit of wired FK laws along every nested exhaustive box sequence. |
| [`WiredBoxTranslation`](FK/WiredBoxTranslation.lean) | Declarations: `mem_vertexBoundary_latticeBox_translate_iff`, `boundaryConditionIso_wired_box_partition`, `wiredBoxConfiguration_translation_commute`, `pmf_map_commute`, … |
| [`WiredComponentBridge`](FK/WiredComponentBridge.lean) | Counting components after wiring a vertex boundary The quotient definition of finite FK components agrees with the description that counts every component disjoint from the boundary separately and all components meeting … |
| [`WiredLimitTranslation`](FK/WiredLimitTranslation.lean) | Declarations: `wiredBoxLimit_translation_invariant` |
| [`WiredRemoval`](FK/WiredRemoval.lean) | Removing finitely many prewired edges For a finite set `R` of original graph edges, configurations split uniquely into the open edges outside `R` and those inside `R`. |
| [`Wiring`](FK/Wiring.lean) | Opening edges and boundary wiring Opening additional edges can merge components but cannot split them. |

### RCInfinite

| Module | Summary |
|---|---|
| [`BoxExhaustion`](RCInfinite/BoxExhaustion.lean) | Declarations: `free_box_exhaustion`, `wired_box_exhaustion`, `translation_invariant` |
| [`ClusterEvents`](RCInfinite/ClusterEvents.lean) | Declarations: `cluster`, `infiniteAt`, `infiniteClusterEvent`, `atMostOneInfiniteCluster`, … |
| [`CylinderApproximation`](RCInfinite/CylinderApproximation.lean) | Declarations: `SupportedCylinder`, `SupportedCylinder.isCylinder`, `SupportedCylinder.dependsOn`, `SupportedCylinder.compl`, … |
| [`Cylinders`](RCInfinite/Cylinders.lean) | Declarations: `Edge`, `DependsOn`, `IsCylinder`, `DependsOn.mono`, … |
| [`EdgeErgodicity`](RCInfinite/EdgeErgodicity.lean) | Declarations: `edgeTranslate`, `edgeTranslate_measurable`, `edgeTranslate_zero`, `edgeTranslate_add`, … |
| [`ErgodicLimits`](RCInfinite/ErgodicLimits.lean) | Declarations: `invariant_allOpen_independent`, `invariant_restrict_eq_smul`, `isRCInfiniteVolumeLimit_interior_edge_ergodic`, `dirac_constant_edge_ergodic`, … |
| [`FiniteConditioning`](RCInfinite/FiniteConditioning.lean) | Declarations: `pmf_eq_bind_fiber_filter`, `pmf_measureReal_eq_expectation`, `pmf_joint_fiber_sum`, `pmf_joint_le_of_fiber_le`, … |
| [`FiniteEnergy`](RCInfinite/FiniteEnergy.lean) | Declarations: `openEnergy`, `openEnergy_pos`, `energyBound`, `energyBound_pos`, … |
| [`FiniteModification`](RCInfinite/FiniteModification.lean) | Declarations: `setEdge`, `setEdge_self`, `setEdge_setEdge`, `setEdge_eq_self`, … |
| [`GeneratorMixing`](RCInfinite/GeneratorMixing.lean) | Declarations: `covariance`, `covariance_change_right`, `allOpen_cylinder_covariance_tendsto_zero`, `allOpen_measurable_covariance_tendsto_zero`, … |
| [`GraphModification`](RCInfinite/GraphModification.lean) | Declarations: `infinite_component_contains_old`, `edgeEndpoints`, `opening_new_edge_endpoints`, `opening_infinite_component_contains_old` |
| [`LimitComparison`](RCInfinite/LimitComparison.lean) | Declarations: `wired_limit_joint_le`, `free_limit_joint_ge`, `abs_covariance_le_of_upper`, `abs_covariance_le_of_lower`, … |
| [`MeasurableBounds`](RCInfinite/MeasurableBounds.lean) | Declarations: `exists_supportedCylinder_real_approx`, `abs_inter_measureReal_sub_le`, `supported_lower_bound_extend`, `openEnergy_le_one`, … |
| [`Mixing`](RCInfinite/Mixing.lean) | Declarations: `translatedEdge_not_mem_box_of_far`, `eventually_cylinder_translate_outside_cofinite`, `allOpen_cylinder_covariance_cofinite`, `allOpen_measurable_covariance_cofinite`, … |
| [`OpeningPaths`](RCInfinite/OpeningPaths.lean) | Declarations: `lattice_horizontal_reachable`, `lattice_vertical_reachable`, `squareLattice_reachable`, `rcInfiniteOpenGraph_edgeSet`, … |
| [`PercolationZeroOne`](RCInfinite/PercolationZeroOne.lean) | Declarations: `infiniteAt_measure_eq_origin`, `infiniteCluster_pos_iff_origin_pos`, `infiniteCluster_zero_one`, `infiniteCluster_eq_one_iff_origin_pos` |
| [`SpatialComparison`](RCInfinite/SpatialComparison.lean) | Declarations: `boxEdges`, `boxRestriction`, `boxRemovedEdges`, `boxOutsideState`, … |
| [`TranslationSupport`](RCInfinite/TranslationSupport.lean) | Declarations: `translatedEdge`, `mem_boxEdges_iff`, `eventually_finset_in_box`, `translatedEdge_not_mem_box`, … |

### Duality

| Module | Summary |
|---|---|
| [`BondStates`](Duality/BondStates.lean) | Declarations: `latticeBondEdge`, `latticeConfigurationBondState`, `latticeConfigurationBondState_eq`, `wholePlaneOpenPrimalGraph`, … |
| [`BoxDihedral`](Duality/BoxDihedral.lean) | Declarations: `latticeQuarterTurn`, `latticeQuarterTurnInv`, `latticeReflection`, `latticeQuarterTurnInv_quarterTurn`, … |
| [`CircuitEnclosure`](Duality/CircuitEnclosure.lean) | Discrete enclosure of the marked vertex by a genuine closed dual simple circuit. |
| [`ConnectionEvents`](Duality/ConnectionEvents.lean) | Finite actual-path witnesses for whole-plane connectivity. |
| [`ConnectionSymmetry`](Duality/ConnectionSymmetry.lean) | Isometry and translation covariance of the actual free two-point function. |
| [`CrossingDuality`](Duality/CrossingDuality.lean) | Declarations: `rectangleDualBottomTopCrossingEvent`, `rectangleHorizontalNoncrossing_subset_dualBottomTopCrossing_preimage`, `rectangleHorizontalComplement_eq_dualBottomTop_preimage`, `rectangle_crossing_duality` |
| [`Decay`](Duality/Decay.lean) | Exponential two-point decay excludes an infinite origin cluster The hypothesis below uses the integer lattice's ℓ¹ distance, explicitly `\|x₁\| + \|x₂\|`. |
| [`DiagonalComparison`](Duality/DiagonalComparison.lean) | FKG and the actual free-limit symmetries compare every direction with the exact frozen diagonal sequence. |
| [`DiagonalRate`](Duality/DiagonalRate.lean) | A positive logarithmic rate gives a diagonal exponential bound The index here is exactly the frozen index: `diagonalSite n = (⌊n/2⌋,⌊n/2⌋)`. |
| [`Discontinuity`](Duality/Discontinuity.lean) | The discontinuity consequences of positive diagonal decay, including the exact parameter/event form consumed by Theorem 1.2 items 1–2. |
| [`DistinctMeasures`](Duality/DistinctMeasures.lean) | Exponential free decay distinguishes the critical free and wired measures. |
| [`DualConfigurationBridge`](Duality/DualConfigurationBridge.lean) | Edge-by-edge bridge between finite complementary duality and the actual whole-plane configuration homeomorphism. |
| [`DualCylinderLaw`](Duality/DualCylinderLaw.lean) | Exact duality on cylinders supported on true finite dual edges. |
| [`FiniteClusterBoundary`](Duality/FiniteClusterBoundary.lean) | Actual finite-cluster dual boundary and simple cycles. |
| [`FiniteDuality`](Duality/FiniteDuality.lean) | Declarations: `partition_mul_left`, `pmf_map_equiv_of_common_factor`, `rectangleCarrierConfigurationEquiv`, `rectanglePrimalDualConfigurationEquiv`, … |
| [`FiniteEvenEdgeCycle`](Duality/FiniteEvenEdgeCycle.lean) | Declarations: `edge_mem_some_isCycle_of_even_degree` |
| [`FiniteGraphBoundaryParity`](Duality/FiniteGraphBoundaryParity.lean) | Declarations: `exists_reachable_between_of_odd_degree_sum` |
| [`FiniteSupportEvenEdgeCycle`](Duality/FiniteSupportEvenEdgeCycle.lean) | Declarations: `edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet` |
| [`FreeAssociation`](Duality/FreeAssociation.lean) | Positive association for actual, unbounded free connectivity events. |
| [`FreeBoxDihedral`](Duality/FreeBoxDihedral.lean) | Declarations: `freeBoxLimit_latticeIso_invariant` |
| [`InfiniteDuality`](Duality/InfiniteDuality.lean) | Infinite-volume free/wired duality for the actual frozen box limits. |
| [`LargeCircuitWitness`](Duality/LargeCircuitWitness.lean) | If there is no infinite primal cluster, closed dual circuits force connections from arbitrarily distant points of a fixed ray to the opposite half-plane. |
| [`LatticeCellBoundary`](Duality/LatticeCellBoundary.lean) | Declarations: `mem_cellBoundaryBonds_faceBase`, `latticeCellBoundaryBonds`, `mem_latticeCellBoundaryBonds`, `latticeCellBoundaryBonds_finite`, … |
| [`LatticeCellBoundaryFiniteEdges`](Duality/LatticeCellBoundaryFiniteEdges.lean) | Declarations: `latticeCellBoundaryGraph_edgeSet_eq_image`, `latticeCellBoundaryGraph_edgeSet_finite` |
| [`LatticeCellBoundaryParity`](Duality/LatticeCellBoundaryParity.lean) | Declarations: `boundaryAdj_right`, `boundaryAdj_up`, `boundaryAdj_left`, `boundaryAdj_down`, … |
| [`LatticeEmbedding`](Duality/LatticeEmbedding.lean) | The positive-mesh square lattice in the complex plane The vertex `(x,y)` is embedded as `δ*x + I*δ*y` for a strictly positive real mesh `δ`. |
| [`LatticePorts`](Duality/LatticePorts.lean) | Actual square-lattice bonds and medial ports A bond is a horizontal or vertical unit lattice segment, normalized by its left or lower endpoint. |
| [`LatticeWalkInterpolation`](Duality/LatticeWalkInterpolation.lean) | Declarations: `latticeWalkPath`, `latticeWalkPath_range_subset_segments` |
| [`LongConnectionBound`](Duality/LongConnectionBound.lean) | Quantitative bounds on long connections with finitely many possible endpoints. |
| [`NormalizedPotentialSpace`](Duality/NormalizedPotentialSpace.lean) | Declarations: `componentPotentialEvaluation`, `normalizedComponentPotentials`, `componentPotentialEvaluation_surjective`, `componentPotentialEvaluation_range_eq_top`, … |
| [`Parameters`](Duality/Parameters.lean) | Dual edge parameter This module proves the algebra of planar FK duality, including the fixed point. |
| [`PeierlsSummability`](Duality/PeierlsSummability.lean) | A summable union bound for long dual connections across opposite half-planes. |
| [`PercolationErgodicity`](Duality/PercolationErgodicity.lean) | The proved zero–one law for infinite-volume random-cluster measures (`RCInfinite/PercolationZeroOne.lean`), on the exact cluster events of the planar-duality library (`Duality/`). |
| [`PlanarConnectionAlternative`](Duality/PlanarConnectionAlternative.lean) | The rectangle crossing alternative on the actual whole-plane configuration carrier, stated as a covering by long primal or dual connection events. |
| [`PrimalDualSegments`](Duality/PrimalDualSegments.lean) | Declarations: `LatticeBond.midpoint_mem_segment`, `dualFaceCenter`, `primalBondSegment`, `dualBondSegment`, … |
| [`RayIndex`](Duality/RayIndex.lean) | Signed intersections with the horizontal ray from a primal vertex. |
| [`RayIndexSeparation`](Duality/RayIndexSeparation.lean) | Finiteness of the nonzero-index region and the jump across a simple circuit. |
| [`ReachabilityLabels`](Duality/ReachabilityLabels.lean) | Declarations: `actualReachabilityLabel`, `actualReachabilityLabel_eq_true_iff`, `actualReachabilityLabel_eq_true_of_mem`, `actualReachabilityLabel_eq_of_actualConnected`, … |
| [`Rectangle`](Duality/Rectangle.lean) | Declarations: `latticeRectangle`, `mem_latticeRectangle`, `card_latticeRectangle`, `RectangleVertex`, … |
| [`RectangleCrossingExclusion`](Duality/RectangleCrossingExclusion.lean) | Declarations: `rectangleComplementDualVerticalCrossingEvent`, `exclusionMesh`, `exclusionOffset`, `rectangleDualOpenGraphToSquare`, … |
| [`RectangleCurl`](Duality/RectangleCurl.lean) | Declarations: `RectangleExteriorPotential`, `rectangleExtendedPotential`, `rectangleExtendedPotential_of_mem`, `rectangleExtendedPotential_of_not_mem`, … |
| [`RectangleCurlLinearEquiv`](Duality/RectangleCurlLinearEquiv.lean) | Declarations: `rectangleExteriorPotentialSubmodule`, `rectanglePotentialAsExterior`, `rectanglePrimalFlowDivergence_add`, `rectanglePrimalFlowDivergence_smul`, … |
| [`RectangleDualAmbient`](Duality/RectangleDualAmbient.lean) | Declarations: `rectangleDualAmbientGraph`, `rectangleDualAmbientGraph_adj_iff`, `primalBondOfDual_endpoints_mem_of_interior_endpoint`, `rectangleDualAmbient_adj_actual_of_left_interior`, … |
| [`RectangleDualAmbientMarginal`](Duality/RectangleDualAmbientMarginal.lean) | Declarations: `rectangleDualAmbient_law_restrict_to_dual` |
| [`RectangleDualBoundaryParity`](Duality/RectangleDualBoundaryParity.lean) | Declarations: `rectangleDualBottomPortVertex`, `rectangleDualTopPortVertex`, `rectangleDualBottomPorts`, `rectangleDualTopPorts`, … |
| [`RectangleDualCarrier`](Duality/RectangleDualCarrier.lean) | Declarations: `rectangleDualExpanded`, `rectangleDualInterior`, `rectangleDualBoundary`, `rectangleDualInterior_eq_empty_width_zero`, … |
| [`RectangleDualConfiguration`](Duality/RectangleDualConfiguration.lean) | Declarations: `rectangleDualConfigurationEquiv`, `rectangleDualConfigurationEquiv_apply`, `rectangleDualConfigurationEquiv_card`, `rectangleDualConfiguration_card_add`, … |
| [`RectangleDualCrossing`](Duality/RectangleDualCrossing.lean) | Declarations: `rectangleDual_mem_expanded_iff`, `bottomPort_mem_of_coords`, `topPort_mem_of_coords`, `exists_reachable_between_of_odd_ncard_neighbor_sum`, … |
| [`RectangleDualCutParity`](Duality/RectangleDualCutParity.lean) | Declarations: `rectangleCutFaceVertex`, `rectangleCutFaceWest`, `rectangleCutFaceEast`, `rectangleCutFaceSouth`, … |
| [`RectangleDualPotential`](Duality/RectangleDualPotential.lean) | Declarations: `rectangleDualConfiguration`, `mem_rectangleDualConfiguration`, `mem_rectangleDualConfiguration_iff`, `rectangleDualOpen_adj_iff`, … |
| [`RectangleEuler`](Duality/RectangleEuler.lean) | Declarations: `rectangleConfigurationOfCarrier`, `rectangleCarrierOfConfiguration`, `rectangleOpenDivSpace`, `rectanglePrimalBondSubtype`, … |
| [`RectangleEvents`](Duality/RectangleEvents.lean) | Declarations: `rectangleHorizontalCrossingEvent` |
| [`RectangleFlowDimension`](Duality/RectangleFlowDimension.lean) | Declarations: `rectanglePrimalEdgeBond_endpoints_mem_public`, `rectanglePrimalEdgeBond_toSym2_public`, `rectanglePrimalBondToEdge`, `rectanglePrimalEdgeBondEquiv`, … |
| [`RectangleFlowIntegration`](Duality/RectangleFlowIntegration.lean) | Declarations: `RectanglePrimalFlow`, `rectangleExtendedPrimalFlow`, `rectanglePrimalFlowDivergence`, `rectangleFlowH`, … |
| [`RectangleLabelCut`](Duality/RectangleLabelCut.lean) | Declarations: `rectangleLabelCutEndpointStates`, `rectangleLabelCutEdgeCarrier`, `mem_rectangleLabelCutEdgeCarrier`, `rectangleLabelCutDualConfiguration`, … |
| [`RectangleLabelCutIncidence`](Duality/RectangleLabelCutIncidence.lean) | Declarations: `rectangleCutDualEdgeOfBond`, `rectangleCutEdgeOfBond_mem_cut_iff`, `rectangleCutDualEdgeOfBond_adj_iff`, `rectangleCutDualEdgeOfBond_crossingBond`, … |
| [`RectangleOpenFlow`](Duality/RectangleOpenFlow.lean) | Declarations: `rectangleBondToGraphEdge`, `rectangleOpenFlowZeroExtend`, `rectangleOpenFlowZeroExtend_onOpen`, `rectangleOpenFlowZeroExtend_onClosed`, … |
| [`RectanglePathIntersection`](Duality/RectanglePathIntersection.lean) | Declarations: `unitClamp`, `unitClamp_mem`, `unitClamp_eq_zero_iff`, `unitClamp_eq_one_iff`, … |
| [`RectangleWalks`](Duality/RectangleWalks.lean) | Declarations: `rectangleOpenGraphToSquare`, `complex_segment_coordinate_bounds`, `latticeWalkPath_coordinate_bounds`, `rectangleOpenWalk_mapped_support_preimage` |
| [`ReverseInfiniteDuality`](Duality/ReverseInfiniteDuality.lean) | Applying the planar dual transform twice translates face-base coordinates. |
| [`ScreenBridge`](Duality/ScreenBridge.lean) | The copied whole-plane geometry uses the exact frozen open graph. |
| [`SignedFlowDimension`](Duality/SignedFlowDimension.lean) | Declarations: `OpenEdgeIndex`, `SignedFlowOrientation`, `signedIncidenceMatrix`, `signedGradient`, … |
| [`WholePlaneDualConfiguration`](Duality/WholePlaneDualConfiguration.lean) | Declarations: `dualEdgeFirst`, `dualEdgeSecond`, `wholePlaneBondEdgeEquiv`, `wholePlaneDualCrossingEdgeEquiv`, … |
| [`WholePlaneDualGraph`](Duality/WholePlaneDualGraph.lean) | Declarations: `dualBondOfPrimal`, `primalBondOfDual`, `primalBondOfDual_dualBondOfPrimal`, `dualBondOfPrimal_primalBondOfDual`, … |
| [`WiredDomainComparison`](Duality/WiredDomainComparison.lean) | Wired domain monotonicity on arbitrary finite induced lattice domains. |
| [`WiredDomainLimit`](Duality/WiredDomainLimit.lean) | Wired limits along finite domains squeezed between consecutive square boxes. |
| [`WiredPercolation`](Duality/WiredPercolation.lean) | Exponential decay of the free two-point function forces positive wired origin percolation at the dual parameter. |
| [`WiredPotentialSpace`](Duality/WiredPotentialSpace.lean) | Declarations: `componentConstantFunctions`, `componentPotentialLocalPredicate`, `componentConstant_iff_local`, `componentConstantQuotientEquiv`, … |
| [`ZeroOne`](Duality/ZeroOne.lean) | The conditional zero–one step This module only upgrades positive origin percolation to almost-sure existence of an infinite cluster, given a zero–one law for the existence event. |

### CorrLength

| Module | Summary |
|---|---|
| [`ConnectionEvents`](CorrLength/ConnectionEvents.lean) | Finite witnesses for infinite-lattice connection events Connection is expressed as the existence of a finite set of open edges that connects the marked vertices. |
| [`CorrelationRate`](CorrLength/CorrelationRate.lean) | Existence of the correlation-length rate The finite-distance connection probabilities are positive and supermultiplicative. |
| [`Positivity`](CorrLength/Positivity.lean) | Positive probability of finite-distance connection Every pair of square-lattice vertices has a deterministic finite path. |
| [`RotatedFreeLimit`](CorrLength/RotatedFreeLimit.lean) | Free limit and connection rate on the rotated lattice The rotated configuration space is transported through the graph isomorphism with the square lattice. |
| [`RotatedLattice`](CorrLength/RotatedLattice.lean) | The rotated lattice and its square-lattice coordinates The carrier `rotatedVertex` is the even-coordinate-sum sublattice of `ℤ²`. |
| [`SubadditiveRate`](CorrLength/SubadditiveRate.lean) | Fekete's lemma for connection probabilities This module isolates the analytic step used once the finite-distance connection probabilities are known to be positive and supermultiplicative. |

### Zhang

| Module | Summary |
|---|---|
| [`BoundaryLimit`](Zhang/BoundaryLimit.lean) | One-arm limits The coordinate-box one-arm probabilities converge to the probability that the actual origin cluster is infinite. |

### Torus

| Module | Summary |
|---|---|
| [`Checkerboard`](Torus/Checkerboard.lean) | A canonical orientation of every smoothed loop On an even medial torus the checkerboard arrow field has alternating types 5 and 6. |
| [`Corollary313`](Torus/Corollary313.lean) | Sector comparisons in Corollary 3.13 The two homological turn classifications are explicit premises here; they are discharged in `Torus/Corollary313Final.lean` by the turning classifications proved in `TorusTopology/Zero… |
| [`Corollary313Final`](Torus/Corollary313Final.lean) | Final torus random-cluster / six-vertex identities The homological turning classifications proved in `TorusTopology/ZeroWindingTurning.lean` and `TorusTopology/NonzeroWindingTurning.lean` discharge the explicit intermedi… |
| [`CorrectedRCWeight`](Torus/CorrectedRCWeight.lean) | The corrected RC summand with the homological `ell₀` statistic |
| [`Darts`](Torus/Darts.lean) | The finite dart permutation of a smoothed medial torus A dart is an incident edge slot at a vertex, directed away from that vertex. |
| [`DiamondChains`](Torus/DiamondChains.lean) | Indexed primal chains on the torus The incidence matrix retains each indexed open edge, including parallel edges and edges with identified endpoints. |
| [`DiamondClusterProjection`](Torus/DiamondClusterProjection.lean) | Projecting conserved flows to individual open clusters The incidence endpoints of an open indexed edge belong to one cluster. |
| [`DiamondCounts`](Torus/DiamondCounts.lean) | Sizes of the actual diamond-torus vertex and indexed edge carriers |
| [`DiamondCycleAnnihilator`](Torus/DiamondCycleAnnihilator.lean) | Potentials characterize the annihilator of conserved flows An edge coefficient vanishing on every actual cycle is an endpoint potential difference. |
| [`DiamondCycleExtension`](Torus/DiamondCycleExtension.lean) | Extending subgraph cycles to the full torus The inclusion extends indexed chains by zero on closed edges. |
| [`DiamondCycleRank`](Torus/DiamondCycleRank.lean) | Dimension of the actual indexed cycle space Zero edge differences mean a potential has one value on each open cluster. |
| [`DiamondDisplacement`](Torus/DiamondDisplacement.lean) | Intersection coordinates are lifted displacement With the endpoint-false to endpoint-true orientation, every primal edge has vertical increment minus one; its horizontal increment is minus one at a black midpoint and plu… |
| [`DiamondDualTranslation`](Torus/DiamondDualTranslation.lean) | Translating the dual diamond graph to the primal colour A horizontal unit translation exchanges the face colours and carries every indexed diamond edge to the corresponding edge. |
| [`DiamondFullConnectivity`](Torus/DiamondFullConnectivity.lean) | Connectivity of the fully open primal diamond torus Diagonal steps generate the black checkerboard faces. |
| [`DiamondFullFlows`](Torus/DiamondFullFlows.lean) | Explicit horizontal and vertical full-torus flows The all-one indexed flow and the checker-sign indexed flow are conserved. |
| [`DiamondGraph`](Torus/DiamondGraph.lean) | Indexed primal and dual diamond graphs on the even medial torus The face labelled `(i,j)` has centre `(i+1/2,j+1/2)`. |
| [`DiamondHomologyCoordinates`](Torus/DiamondHomologyCoordinates.lean) | Displacement coordinates of full torus homology Intersection with the two explicit conserved flows gives the two lifted displacement coordinates. |
| [`DiamondIntersectionDeterminant`](Torus/DiamondIntersectionDeterminant.lean) | Intersection is the determinant of lifted displacement Zero displacement is exactly a full-torus cellular boundary. |
| [`DiamondIntersectionLocality`](Torus/DiamondIntersectionLocality.lean) | Intersection localizes to one open cluster Corner primitives and edge coefficients restrict with the cluster of their vertex. |
| [`DiamondSeamWinding`](Torus/DiamondSeamWinding.lean) | Primal winding as algebraic intersection with fixed torus cuts The vertical reference cut lies between columns minus one and zero, and the horizontal cut lies between rows minus one and zero. |
| [`DualLoopTransport`](Torus/DualLoopTransport.lean) | The actual primal/dual loop correspondence Reverse a medial dart and translate it horizontally. |
| [`EdgeIndex`](Torus/EdgeIndex.lean) | Directed darts enumerate each indexed torus edge once The edge index is its left/lower endpoint and a horizontal/vertical Boolean. |
| [`EdgeOrder`](Torus/EdgeOrder.lean) | Explicit finite orders for indexed edge attachment Configurations are represented by lists of their open indexed edges. |
| [`LocalSmoothing`](Torus/LocalSmoothing.lean) | The two turning smoothings at a medial vertex Source: §3.3.1, Fig. |
| [`LoopCrossings`](Torus/LoopCrossings.lean) | Algebraic crossings of actual directed loop orbits Crossings are signed intersections with a fixed row of vertical edges. |
| [`LoopHomology`](Torus/LoopHomology.lean) | Discrete vertical homology of the smoothed loop cycles An elementary coboundary calculation shows that a closed orbit has the same signed intersection with every horizontal reference row. |
| [`LoopOrientation`](Torus/LoopOrientation.lean) | Orientation of a smoothed loop is one Boolean per cyclic orbit A fixed compatible arrow field is used solely to select a canonical direction on each loop. |
| [`LoopReorientation`](Torus/LoopReorientation.lean) | Changing loop orientations preserves the underlying cyclic edge partition The quotient equivalence below aligns each edge with the new arrow field. |
| [`LoopRotationNumber`](Torus/LoopRotationNumber.lean) | Integer rotation numbers of the smoothed torus loops The port-angle cocycle makes the total signed turn an integer multiple of one full turn. |
| [`LoopStatistics`](Torus/LoopStatistics.lean) | Vertical winding counts and the sector bound Parity of the signed flux proves the evenness of the total absolute vertical winding without a classification of essential loops. |
| [`LoopTurnDivisibility`](Torus/LoopTurnDivisibility.lean) | The discrete rotation sum is divisible by one full turn |
| [`LoopTurnOrientation`](Torus/LoopTurnOrientation.lean) | Discrete loop turning under reversal of orientation |
| [`LoopTurning`](Torus/LoopTurning.lean) | Summing the signed turns over the actual loop partition The local turn at an outgoing dart is determined by its paired incoming dart. |
| [`NetEuler`](Torus/NetEuler.lean) | Winding nets and the torus Euler relation A net is a single actual open cluster carrying two conserved rational one-cycles with independent lifted winding classes. |
| [`OrientationEquiv`](Torus/OrientationEquiv.lean) | All loop orientations, with no existence choices Choosing one Boolean per canonical cyclic loop reconstructs an arrow field compatible with the given smoothing. |
| [`OrientedLoopWeight`](Torus/OrientedLoopWeight.lean) | Turning weights of oriented loop configurations The source weight is the exponential of the sum of oriented loop turns. |
| [`Parameters`](Torus/Parameters.lean) | The parameter conversion in (3.12) This connects the proved local smoothing sums to the exact parameter `sqrt (2 + sqrt q)`. |
| [`PermutationCycleTransport`](Torus/PermutationCycleTransport.lean) | Transport of cyclic orbits under reversed traversal A bijection intertwining one path step with the inverse step on another carrier induces an explicit equivalence of cyclic orbits. |
| [`PermutationCycles`](Torus/PermutationCycles.lean) | Counting all permutation cycles, including fixed points The cyclic-orbit quotient is the disjoint union of fixed points and nontrivial cycle factors. |
| [`PermutationInvariantSpace`](Torus/PermutationInvariantSpace.lean) | Cycle counts as dimensions of invariant functions Functions invariant under a permutation are exactly functions on its cyclic orbits. |
| [`PermutationSurgery`](Torus/PermutationSurgery.lean) | Exact split-and-join counts A transposition splits one cyclic orbit if its ends lie on that orbit, and joins two orbits otherwise. |
| [`RCWeight`](Torus/RCWeight.lean) | The torus random-cluster loop weight identity The proved Euler/net relation converts the critical RC weight into the loop weight of Lemma 3.9, with the exact real-power normalization from the paper. |
| [`RibbonAttachment`](Torus/RibbonAttachment.lean) | Attaching one indexed ribbon Changing one primal edge composes the boundary permutation with the transposition of its two ends. |
| [`RibbonBoundary`](Torus/RibbonBoundary.lean) | The cellular boundary permutation Open primal ribbons interchange the two corner slots at their medial midpoint. |
| [`RibbonChainComplex`](Torus/RibbonChainComplex.lean) | The boundary-of-boundary identity Incidence pairing is discrete integration by parts. |
| [`RibbonClusterSurgery`](Torus/RibbonClusterSurgery.lean) | Component counts under attachment of a closed edge An attached ribbon imposes equality of the values at its two ends on component functions. |
| [`RibbonConnectivity`](Torus/RibbonConnectivity.lean) | Ribbon components are the open primal clusters Connectivity is generated by rotations within a vertex disc and crossings of an open ribbon. |
| [`RibbonCornerPrimitive`](Torus/RibbonCornerPrimitive.lean) | Cyclic-order primitives of conserved half-edge flows On each primal vertex disc the four outward flows sum to zero. |
| [`RibbonCorners`](Torus/RibbonCorners.lean) | Corners of the primal ribbon vertices The canonically directed medial edges are exactly the four boundary corners of every black face. |
| [`RibbonEdges`](Torus/RibbonEdges.lean) | Indexed ribbon ends and diamond endpoints Each medial midpoint carries two canonical outgoing slots. |
| [`RibbonEmpty`](Torus/RibbonEmpty.lean) | The empty ribbon subgraph Every primal vertex is an isolated disc, with one boundary component. |
| [`RibbonEuler`](Torus/RibbonEuler.lean) | Euler counting by cellular ribbon attachment A handle-creating attachment joins two different boundary cycles of the same component. |
| [`RibbonFaceBoundary`](Torus/RibbonFaceBoundary.lean) | Boundaries of the capped ribbon faces The coefficient on an indexed ribbon is the difference of the values assigned to the boundary cycles on its two sides. |
| [`RibbonFullBoundary`](Torus/RibbonFullBoundary.lean) | Boundary components of the fully open primal torus The complementary white faces are exactly the clockwise boundary cycles. |
| [`RibbonHalfFlow`](Torus/RibbonHalfFlow.lean) | Conserved flows on ribbon ends Extend an open-edge chain by zero on the closed indexed edges and assign opposite outward flows to its two ends. |
| [`RibbonHandleBound`](Torus/RibbonHandleBound.lean) | At most one handle on the cellular torus The full primal ribbon graph has one handle by the proved Euler count, connectivity, and white-face boundary count. |
| [`RibbonHandleIntersection`](Torus/RibbonHandleIntersection.lean) | Handles and nonzero cellular intersection The capped homology dimension and the exact radical theorem characterize the presence of a handle by two conserved flows with nonzero cyclic-order intersection. |
| [`RibbonHandleMonotone`](Torus/RibbonHandleMonotone.lean) | Monotonicity of the attachment handle count Extend any order of the old open edges by the newly open edges. |
| [`RibbonHomology`](Torus/RibbonHomology.lean) | Homology of the capped ribbon subgraph Take conserved indexed flows modulo the actual capped face boundaries. |
| [`RibbonIntersection`](Torus/RibbonIntersection.lean) | The cyclic-order intersection coefficient The corner primitive measures the separation between the two sides of an indexed ribbon. |
| [`RibbonIntersectionAlternating`](Torus/RibbonIntersectionAlternating.lean) | Alternation of the cellular intersection pairing Finite summation by parts around the vertex rotations shows antisymmetry. |
| [`RibbonIntersectionBoundary`](Torus/RibbonIntersectionBoundary.lean) | Cellular boundaries are the intersection radical For a capped boundary, its corner primitive differs from the boundary-cycle value by one potential per primal vertex. |
| [`RibbonIntersectionLinear`](Torus/RibbonIntersectionLinear.lean) | Bilinearity of the cyclic-order intersection pairing The normalized primitive is given by explicit linear combinations of corner flows. |
| [`RibbonInvariantSpace`](Torus/RibbonInvariantSpace.lean) | Invariant functions on ribbon components Functions invariant under both vertex rotation and open-edge pairing are exactly functions on the components of the actual ribbon subgraph. |
| [`RibbonSurgery`](Torus/RibbonSurgery.lean) | Boundary counts under ribbon surgery The general permutation cut-and-join theorem applies to the actual RC loops. |
| [`SmoothingSum`](Torus/SmoothingSum.lean) | Independent local smoothings and the six-vertex weight This module proves the finite product/sum step of Lemma 3.12 for the actual two turning pairings, on the same indexed torus as `SixVertex.ArrowConfig`. |
| [`WindingReorientation`](Torus/WindingReorientation.lean) | Vertical winding is independent of loop orientation The explicit loop equivalence and edge-antisymmetry of algebraic crossings show that reversing loops preserves their absolute vertical winding. |

### TorusLoops

| Module | Summary |
|---|---|
| [`BipartiteCirculations`](TorusLoops/BipartiteCirculations.lean) | Conserved flows on a bipartite indexed graph Edges are indexed independently of their endpoint pairs, so parallel edges are retained. |
| [`DualTranslation`](TorusLoops/DualTranslation.lean) | Duality as an actual translation of indexed torus configurations Translation by one column exchanges the primal and dual face colours. |
| [`FiniteEnergy`](TorusLoops/FiniteEnergy.lean) | One-edge finite-energy bound for the indexed torus law Opening one closed indexed edge changes the primal cluster count by either zero or one. |
| [`HorizontalHomology`](TorusLoops/HorizontalHomology.lean) | Horizontal intersection numbers of smoothed loops This is the coordinate-swapped counterpart of the existing vertical homology calculation. |
| [`Lemma314Corrected`](TorusLoops/Lemma314Corrected.lean) | Corrected Lemma 3.14 The source proof yields a limsup estimate, not the existence of a width limit. |
| [`LoopClusterProjection`](TorusLoops/LoopClusterProjection.lean) | Projection of a medial boundary loop to its incident primal cluster The lifted medial displacement equals the displacement of the open-ribbon traversals, up to an explicit corner coboundary. |
| [`LoopDensityExpectation`](TorusLoops/LoopDensityExpectation.lean) | Finite-volume expectation bounds from the winding-loop tail These inequalities are the finite-sum form of the truncation step in (3.18). |
| [`LoopDensityExponentialTail`](TorusLoops/LoopDensityExponentialTail.lean) | Exponential control of the weighted large-loop tail For a threshold proportional to the width, a sufficiently small one-arm probability makes both the large-loop probability and its maximal observable contribution expone… |
| [`LoopDensityLogBounds`](TorusLoops/LoopDensityLogBounds.lean) | Logarithmic rate bounds for the weighted loop observable The expectation truncation bounds and exponentially small weighted tail give a uniform estimate for the absolute logarithmic rate at every sufficiently large even … |
| [`LoopDensityObservable`](TorusLoops/LoopDensityObservable.lean) | The normalized loop observable on the finite torus The observable is `(2 / sqrt q)^ell₀ q^{-s}` with the fixed homological definition of `ell₀`. |
| [`LoopIncidence`](TorusLoops/LoopIncidence.lean) | Incidence of loops with their primal and dual clusters Each medial loop has one incident cluster of each colour. |
| [`LoopTailBoundaryDecay`](TorusLoops/LoopTailBoundaryDecay.lean) | Boundary-decay input for the rotated-box one-arm probabilities The exploration estimate loses one unit in the rotated square radius. |
| [`LoopTailProbability`](TorusLoops/LoopTailProbability.lean) | Finite-energy winding-loop tail after the root-set union bound Combining the seam-closing estimate with the root-set exploration estimate gives an explicit probability bound for a large homological loop count. |
| [`LoopTailRectangleFK`](TorusLoops/LoopTailRectangleFK.lean) | The corrected large-loop estimate under the free rectangle FK law The cut-graph crossing event is transported to an event on rectangle FK configurations through the seam-closed extension bijection. |
| [`LoopTailSeamBound`](TorusLoops/LoopTailSeamBound.lean) | Finite-energy reduction of winding-loop tails to rectangle crossings The deterministic corrected crossing count and the seam-stability of the cut-graph event give the first probability inequality in the proof of (3.17). |
| [`LoopTailUnionBound`](TorusLoops/LoopTailUnionBound.lean) | Union bound over disjoint horizontal crossings The crossing count is covered by root-set events. |
| [`Measure`](TorusLoops/Measure.lean) | The finite critical random-cluster law on the diamond torus This module re-exports the normalization of the indexed `torusRCWeight` built in `TorusRC/` as the paper's torus law `φ_T`. |
| [`RectangleBoxComparison`](TorusLoops/RectangleBoxComparison.lean) | Free FK comparison from the cut rectangle to a rotated square box Every increasing event of the cut rectangle has probability at most that of its exact restriction event in a containing square box. |
| [`RectangleClusterBoundary`](TorusLoops/RectangleClusterBoundary.lean) | Frozen open edges confined to an explored cluster If every open edge in the frozen state has both endpoints in the explored region, no two vertices embedded in its complement become identified by the induced frozen bound… |
| [`RectangleCrossingCount`](TorusLoops/RectangleCrossingCount.lean) | Winding loops produce distinct cut-rectangle crossing components Every full-torus primal cluster represented by a clean horizontal winding loop contains a cut-rectangle crossing. |
| [`RectangleCrossingEvents`](TorusLoops/RectangleCrossingEvents.lean) | Crossing components of the cut rectangle These components are defined from the cut graph itself, so their count is unchanged by changing any edge state on either deleted seam. |
| [`RectangleCrossings`](TorusLoops/RectangleCrossings.lean) | Rectangle cuts and crossings from conserved winding Removing the indexed edge rows and columns at the coordinate seams produces the finite rectangle graph. |
| [`RectangleExplorationFibers`](TorusLoops/RectangleExplorationFibers.lean) | Joint finite-FK estimates over frozen edge states A conditional upper comparison can be integrated over any selected set of frozen exterior states. |
| [`RectangleExplorationProduct`](TorusLoops/RectangleExplorationProduct.lean) | Root-set exploration events on the cut rectangle This module records the finite exploration states used to iterate the one-step estimate. |
| [`RectangleExplorationProductBound`](TorusLoops/RectangleExplorationProductBound.lean) | Probability bounds for sequential rectangle exploration This module turns the weighted one-step estimate into a bound on distinct rooted crossings, one exact old-cluster observation at a time. |
| [`RectangleExplorationStep`](TorusLoops/RectangleExplorationStep.lean) | One-step bound for exploration outside a revealed cluster Freezing all edges not in the induced complement graph, when the frozen open edges lie within the explored region, leaves a free FK boundary on the complement. |
| [`RectangleExplorationWeightedStep`](TorusLoops/RectangleExplorationWeightedStep.lean) | Weighted one-step exploration estimate The fixed-state conditional bound can be averaged over any selected collection of removed-edge states whose open edges stay in the explored region. |
| [`RectangleFK`](TorusLoops/RectangleFK.lean) | The fixed FK graph of the cut diamond rectangle The open rectangle graph from `RectangleCrossings` is the open subgraph of this fixed finite graph. |
| [`RectangleInfiniteComparison`](TorusLoops/RectangleInfiniteComparison.lean) | Increasing events under the free box limit Finite free FK boxes are monotone on every clopen increasing event of the whole-lattice configuration space. |
| [`RectangleLaw`](TorusLoops/RectangleLaw.lean) | The seam-closed torus fiber and the free rectangle FK law The torus configurations with both cut seams closed are in bijection with configurations of the fixed rectangle graph. |
| [`RectangleOneArmComparison`](TorusLoops/RectangleOneArmComparison.lean) | Free-box comparison for one-arm events The free finite-box law is dominated by the canonical free limit on the one-arm event. |
| [`RectangleRootCrossings`](TorusLoops/RectangleRootCrossings.lean) | Rooted horizontal crossings of the cut rectangle The distinct-crossing-count event is not increasing, but a crossing from one fixed left-boundary vertex to the right boundary is increasing. |
| [`RectangleRotatedEmbedding`](TorusLoops/RectangleRotatedEmbedding.lean) | Embedding the cut diamond rectangle in a finite square FK box The face coordinates of the cut rectangle are the coordinates of vertices in the rotated lattice. |
| [`RectangleTranslatedOneArm`](TorusLoops/RectangleTranslatedOneArm.lean) | Rooted one-arm probabilities in the canonical free limit Finite free origin boxes are dominated by the free-limit probability of a one-arm event rooted at any fixed lattice vertex. |
| [`WindingCirculations`](TorusLoops/WindingCirculations.lean) | Winding is conserved at both primal and dual clusters The sum of the boundary chains incident to one primal cluster is zero. |
| [`WindingClusterCount`](TorusLoops/WindingClusterCount.lean) | At most two winding boundary loops per primal cluster The two conserved displacement coordinates form circulations in the same at-most-one-dimensional incidence circulation space. |
| [`WindingLoopCount`](TorusLoops/WindingLoopCount.lean) | Bounds for loops with nonzero coordinate winding For a directed smoothed loop, nonzero intersection with either coordinate seam is its nonzero torus winding class. |

### TorusRC

| Module | Summary |
|---|---|
| [`AnnularExclusion`](TorusRC/AnnularExclusion.lean) | A genuine dual vertical winding blocks primal strip crossings |
| [`Association`](TorusRC/Association.lean) | FKG association for the critical indexed torus law |
| [`BarrierLower`](TorusRC/BarrierLower.lean) | The source barrier lower bound from crossing, surgery, and duality |
| [`BarrierSeam`](TorusRC/BarrierSeam.lean) | The seam edges fixed by the source barrier event |
| [`BlockChain`](TorusRC/BlockChain.lean) | Iterating the reflected double-block connection bound |
| [`BlockGeometry`](TorusRC/BlockGeometry.lean) | Actual lifted connections supplied by the reflected blocks |
| [`BlockLogRate`](TorusRC/BlockLogRate.lean) | The polynomial crossing prefactor has vanishing block rate |
| [`BoundedChain`](TorusRC/BoundedChain.lean) | Height-controlled chains for the seam-closing construction |
| [`BoundedPaths`](TorusRC/BoundedPaths.lean) | Lifted paths avoiding the horizontal seam |
| [`BoxInterior`](TorusRC/BoxInterior.lean) | Lifted boxes wholly inside the right-half interior |
| [`BoxLimitLower`](TorusRC/BoxLimitLower.lean) | Cofinal native squares recover the exact rotated free connection probability |
| [`BoxProbability`](TorusRC/BoxProbability.lean) | Positivity and normalization of the native box connection probability |
| [`BoxProduct`](TorusRC/BoxProduct.lean) | Products of local free-box bounds on an exact right-half fiber |
| [`BoxTranslation`](TorusRC/BoxTranslation.lean) | Translation invariance of native lifted free-box probabilities |
| [`CPrimeEstimate`](TorusRC/CPrimeEstimate.lean) | The corrected conditional chain bound, with a height-independent cost |
| [`CPrimeFiber`](TorusRC/CPrimeFiber.lean) | The corrected chain estimate on each barrier-compatible fiber |
| [`CollarEdges`](TorusRC/CollarEdges.lean) | A bounded set of retained edges sufficient for both seam collars |
| [`ColumnZigzag`](TorusRC/ColumnZigzag.lean) | Explicit vertical zigzags in the lifted right half |
| [`CorrelationRate`](TorusRC/CorrelationRate.lean) | The unique correlation rate of the exact rotated free law (`CorrLength/`) |
| [`CrossingContracts`](TorusRC/CrossingContracts.lean) | Rectangle crossing event and the crossing estimate (3.19) contract |
| [`CylinderEvents`](TorusRC/CylinderEvents.lean) | Barrier and seam-closed cylinder events for Lemma 3.15 |
| [`CylinderFiberBridge`](TorusRC/CylinderFiberBridge.lean) | Conditional finite-state laws on frozen torus edge fibers |
| [`CylinderFiberComparison`](TorusRC/CylinderFiberComparison.lean) | Conditional comparison and association on a torus edge fiber |
| [`CylinderFiniteEnergy`](TorusRC/CylinderFiniteEnergy.lean) | Finite-energy cost of cutting the torus seam |
| [`DiagonalIntersection`](TorusRC/DiagonalIntersection.lean) | Intersections of opposite-colour unit diagonal segments |
| [`DualPathSeparation`](TorusRC/DualPathSeparation.lean) | Geometric disjointness of actual primal and translated dual paths |
| [`ElementaryTail`](TorusRC/ElementaryTail.lean) | The zero-rate upper-tail case This module records the exact `r = 1` case of (3.16), where the right-hand side is zero. |
| [`Eq315`](TorusRC/Eq315.lean) | Lemma 3.15, equation (3.15), with h319 as the sole external premise |
| [`FiberDisintegration`](TorusRC/FiberDisintegration.lean) | Joint disintegration retaining the exterior configuration |
| [`FiberFiniteEnergy`](TorusRC/FiberFiniteEnergy.lean) | Finite-energy factors for prescribed retained open edges |
| [`FiniteConnectionTransport`](TorusRC/FiniteConnectionTransport.lean) | Actual connectivity under closed extension and embedded restriction |
| [`FiniteEventMeasure`](TorusRC/FiniteEventMeasure.lean) | Event expectations and lower semicontinuity of connection probabilities |
| [`IndexedFK`](TorusRC/IndexedFK.lean) | Connectivity and supermodularity for the indexed torus configurations The map to simple-graph edge sets is used only for connectivity. |
| [`IndexedGraphBridge`](TorusRC/IndexedGraphBridge.lean) | The large-period diamond torus is a simple graph |
| [`IndexedOpening`](TorusRC/IndexedOpening.lean) | Finite-energy opening of prescribed indexed torus edges |
| [`InnerLowerLimit`](TorusRC/InnerLowerLimit.lean) | The height limit in the lower bound of Lemma 3.15 |
| [`LiftedBoxes`](TorusRC/LiftedBoxes.lean) | Native square boxes in the integer cover and their torus embeddings |
| [`LiftedEvent`](TorusRC/LiftedEvent.lean) | Event C prime with a lifted end segment |
| [`LiftedInterpolation`](TorusRC/LiftedInterpolation.lean) | Straight-segment interpolation of lifted walks |
| [`LiftedPaths`](TorusRC/LiftedPaths.lean) | The lifted local connection event used in the corrected lower-bound proof The cover is the rotated lattice of `CorrLength/RotatedLattice.lean`. |
| [`LogProbabilityClosure`](TorusRC/LogProbabilityClosure.lean) | Closing strict probability lower bounds after taking logarithms |
| [`LogRateLimits`](TorusRC/LogRateLimits.lean) | Logarithmic limits of block-product lower bounds |
| [`LowerEstimate`](TorusRC/LowerEstimate.lean) | The complete finite-volume lower estimate for U=1 |
| [`Measure`](TorusRC/Measure.lean) | The critical random-cluster probability on the indexed diamond torus Normalize the actual indexed-edge weight `torusRCWeight` of `Torus/DiamondGraph.lean`, retaining loops and parallel edges for small periods. |
| [`MeasureBridge`](TorusRC/MeasureBridge.lean) | The large-period torus law as an ordinary finite FK law |
| [`MeasureFacts`](TorusRC/MeasureFacts.lean) | Finite-event formulas for the indexed torus probability |
| [`OuterLowerLimit`](TorusRC/OuterLowerLimit.lean) | The width limit in the lower bound of Lemma 3.15 |
| [`PeriodicReflection`](TorusRC/PeriodicReflection.lean) | Reflection of the actual lifted lattice and its indexed torus edges |
| [`PrimalWindingLower`](TorusRC/PrimalWindingLower.lean) | The source event-A lower bound from h319 and finite energy |
| [`RateRescaling`](TorusRC/RateRescaling.lean) | Absorbing a one-unit strip margin into a uniform crossing constant |
| [`RectanglePairs`](TorusRC/RectanglePairs.lean) | Extracting an endpoint pair from the rectangle-crossing estimate |
| [`ReflectedPairs`](TorusRC/ReflectedPairs.lean) | The reflected FKG connection across a double-height rectangle |
| [`ReflectionGraph`](TorusRC/ReflectionGraph.lean) | Reflection of the diamond torus endpoints |
| [`ReflectionLaw`](TorusRC/ReflectionLaw.lean) | Reflection symmetry of the exact indexed torus law |
| [`RetainedOpening`](TorusRC/RetainedOpening.lean) | Opening retained edge sets on every exact torus fiber |
| [`RightHalf`](TorusRC/RightHalf.lean) | The right-half interior and the exterior measurability of B |
| [`SeamCollar`](TorusRC/SeamCollar.lean) | Completing the localized chain with bounded seam collars |
| [`SelfDualTilt`](TorusRC/SelfDualTilt.lean) | The self-dual torus weight used in the crossing argument |
| [`SquareBoxComparison`](TorusRC/SquareBoxComparison.lean) | Comparison of rotated-lattice image boxes with native lifted square boxes |
| [`TiltDuality`](TorusRC/TiltDuality.lean) | Complementary duality invariance of the tilted torus law |
| [`TiltProbability`](TorusRC/TiltProbability.lean) | Comparing the self-dual tilt with the standard torus law |
| [`TopologyBounds`](TorusRC/TopologyBounds.lean) | Quantitative reductions with the torus topology premises discharged The premises that B ∩ C′ forces `U = 1` and that `U ≥ r` forces `r` distinct bottom-to-top clusters after the seam row is closed are discharged by `Toru… |
| [`WindingClosure`](TorusRC/WindingClosure.lean) | The finite terminal zigzag and the source winding event |
| [`WindingEnergy`](TorusRC/WindingEnergy.lean) | Finite-energy completion of the source's primal winding event |
| [`WindingPeriods`](TorusRC/WindingPeriods.lean) | Repeating a genuine lifted vertical period |

### TorusExploration

| Module | Summary |
|---|---|
| [`AdaptiveDomainMarkov`](TorusExploration/AdaptiveDomainMarkov.lean) | Declarations: `revealRecordEvent`, `revealRecordConfiguration`, `revealRecordEvent_eq_frozenStateEvent` |
| [`ClosedSubgraphLaw`](TorusExploration/ClosedSubgraphLaw.lean) | Closing all edges outside a subgraph leaves its exact free FK law. |
| [`ClusterComplementFreeLaw`](TorusExploration/ClusterComplementFreeLaw.lean) | Revealing complete clusters under a free outer law induces no identifications between the remaining vertices. |
| [`ClusterExploration`](TorusExploration/ClusterExploration.lean) | Declarations: `actualClusterReveal`, `actualClusterReveal_mem_iff`, `openGraph_adj_to_config_mem`, `config_mem_to_openGraph_adj`, … |
| [`ClusterRecords`](TorusExploration/ClusterRecords.lean) | The exact finite record of complete cluster explorations and the events of distinct prescribed connections determined by it. |
| [`ComplementEmbedding`](TorusExploration/ComplementEmbedding.lean) | Restricting the planar unrolling to complements of several explored clusters. |
| [`ConditionalConnectionBound`](TorusExploration/ConditionalConnectionBound.lean) | A genuine conditional exploration bound after revealing complete clusters. |
| [`Contract`](TorusExploration/Contract.lean) | Direct consumption check against the unchanged equation (3.16) contract `RCMProof.contract_eq316` of the Theorem 1.2 assembly. |
| [`CylinderIndexedBridge`](TorusExploration/CylinderIndexedBridge.lean) | Exact original-edge bridge for the full seam-closed cylinder. |
| [`CylinderIntersection`](TorusExploration/CylinderIntersection.lean) | Local intersection coefficients for cutting a cylinder along a crossing cluster. |
| [`CylinderIntersectionZero`](TorusExploration/CylinderIntersectionZero.lean) | A seam-band return has zero algebraic intersection with every cycle avoiding the explored crossing cluster in the cylinder interior. |
| [`CylinderProduct`](TorusExploration/CylinderProduct.lean) | The cylinder distinct-crossing product bound with its geometric premise proved. |
| [`CylinderUnionBound`](TorusExploration/CylinderUnionBound.lean) | Union over actual bottom and top endpoints of distinct cylinder crossings. |
| [`DistinctConnections`](TorusExploration/DistinctConnections.lean) | The successor event in a distinct-cluster exploration. |
| [`DistinctProduct`](TorusExploration/DistinctProduct.lean) | The exploration product bound, with the first crossing charged at most one. |
| [`EmbeddedCylinderEvent`](TorusExploration/EmbeddedCylinderEvent.lean) | Finite increasing cylinder events of an embedded graph. |
| [`Eq316`](TorusExploration/Eq316.lean) | Equation (3.16) with the exact positive-even periods, frozen free limit, and frozen diagonalSite rate used by RCMProof.contract_eq316. |
| [`ExteriorConfig`](TorusExploration/ExteriorConfig.lean) | Removing an entire actual cluster from an indexed configuration. |
| [`ExteriorWinding`](TorusExploration/ExteriorWinding.lean) | A bottom-to-top cluster cuts every horizontal winding cycle of its cylinder complement. |
| [`FiberAveraging`](TorusExploration/FiberAveraging.lean) | Exact averaging of conditional laws along the fibers of a finite record. |
| [`FilterUpperBound`](TorusExploration/FilterUpperBound.lean) | A joint event is bounded by its genuine conditional probability. |
| [`FiniteBoxComparison`](TorusExploration/FiniteBoxComparison.lean) | Free comparison for arbitrary finite graphs embedded in a lattice box. |
| [`FiniteFreeComparison`](TorusExploration/FiniteFreeComparison.lean) | Comparison of a genuinely embedded finite free FK law with the free infinite-volume law on the square lattice. |
| [`FiniteTailBound`](TorusExploration/FiniteTailBound.lean) | The complete finite-volume upper estimate underlying (3.16). |
| [`HorizontalPotential`](TorusExploration/HorizontalPotential.lean) | Integer potentials for horizontal cuts with no winding cycles. |
| [`InducedConnectivity`](TorusExploration/InducedConnectivity.lean) | Restriction of actual connectivity to an induced union of open clusters. |
| [`MultiSeedClusterExploration`](TorusExploration/MultiSeedClusterExploration.lean) | Declarations: `actualMultiClusterConnected`, `actualMultiClusterReveal`, `actualMultiClusterReveal_mem_iff`, `actualClusterReveal_subset_multi`, … |
| [`PlanarConnectionBound`](TorusExploration/PlanarConnectionBound.lean) | A uniform diagonal bound for a finite free FK connection in any planar unrolling, independent of the horizontal displacement of its endpoints. |
| [`PlanarLift`](TorusExploration/PlanarLift.lean) | Unrolling a horizontally exact cylinder into the rotated square lattice. |
| [`PlanarLiftEdges`](TorusExploration/PlanarLiftEdges.lean) | Horizontal seam potentials give genuine nearest-neighbour lifts. |
| [`ReflectionComparison`](TorusExploration/ReflectionComparison.lean) | A reflection bound uniform in the horizontal coordinate of an unrolled crossing. |
| [`SeamClosureWinding`](TorusExploration/SeamClosureWinding.lean) | The closure of a bottom-to-top cylinder path winds once vertically. |
| [`SeamCycle`](TorusExploration/SeamCycle.lean) | The seam band is one connected cycle through the bottom and top rows. |
| [`SeamLawBound`](TorusExploration/SeamLawBound.lean) | The torus joint seam-closed event is bounded by the exact free cylinder law. |
| [`TailPositivity`](TorusExploration/TailPositivity.lean) | Nonempty winding-tail events in the widths needed for logarithmic estimates. |
| [`UnexploredCylinder`](TorusExploration/UnexploredCylinder.lean) | The full unexplored cylinder graph, including its currently closed edges. |
| [`UnexploredEmbedding`](TorusExploration/UnexploredEmbedding.lean) | The full unexplored cylinder embeds in the planar rotated lattice. |
| [`UpperRateLimits`](TorusExploration/UpperRateLimits.lean) | Numerical passage from the finite cylinder estimate to the height limsup. |
| [`WalkClosure`](TorusExploration/WalkClosure.lean) | Closing an indexed cylinder path through the seam band. |

### TorusTopology

| Module | Summary |
|---|---|
| [`BarrierEvent`](TorusTopology/BarrierEvent.lean) | B intersect C prime forces U=1 on the exact events `TorusRC.torusRCBarrier` and `TorusRC.torusCPrime` used in the proof of (3.15). |
| [`BoundarySpan`](TorusTopology/BoundarySpan.lean) | Boundary-loop chains span the primal conserved chains whenever the horizontal displacement vanishes on all primal cycles. |
| [`ClosedMidpointCycle`](TorusTopology/ClosedMidpointCycle.lean) | A zero-winding torus orbit is an actual simple square-lattice cycle after lifting and rotating its edge midpoints. |
| [`ClusterIntegralWinding`](TorusTopology/ClusterIntegralWinding.lean) | Integer boundary decompositions within a specified original primal cluster. |
| [`ClusterVerticalValues`](TorusTopology/ClusterVerticalValues.lean) | The two possible nonzero vertical boundary values of one primal cluster. |
| [`CompassWordBounds`](TorusTopology/CompassWordBounds.lean) | Uniform turn bounds for a return consisting of three straight segments. |
| [`CompassWordTurning`](TorusTopology/CompassWordTurning.lean) | Algebra of the signed turn of finite compass words. |
| [`CylinderCount`](TorusTopology/CylinderCount.lean) | U at least r gives r distinct bottom-to-top clusters in the exact seam-closed cylinder (`hUr_proved`). |
| [`CylinderCrossing`](TorusTopology/CylinderCrossing.lean) | Crossing the seam-closed cylinder from nonzero conserved vertical winding. |
| [`IndexedWalk`](TorusTopology/IndexedWalk.lean) | Indexed diamond walks and their integral conserved-chain witnesses. |
| [`IntegralBoundary`](TorusTopology/IntegralBoundary.lean) | Integral saturation of the actual ribbon face boundary map. |
| [`LatticeQuarterRotation`](TorusTopology/LatticeQuarterRotation.lean) | Orientation-preserving quarter rotation of actual lattice curves. |
| [`LatticeSequenceWalk`](TorusTopology/LatticeSequenceWalk.lean) | Actual finite walks traced by a unit-step lattice sequence. |
| [`LatticeStraightWalk`](TorusTopology/LatticeStraightWalk.lean) | Literal directed straight segments for closing long periodic lattice arcs. |
| [`LatticeUpperReturn`](TorusTopology/LatticeUpperReturn.lean) | A literal three-sided lattice return above two endpoints. |
| [`LiftedEdgeCover`](TorusTopology/LiftedEdgeCover.lean) | Explicit integer lifts of indexed diamond endpoints and vertical deck translations. |
| [`LiftedPotentials`](TorusTopology/LiftedPotentials.lean) | Potentials on the finite torus telescope along the specified integer lifts. |
| [`LoopLiftProjection`](TorusTopology/LoopLiftProjection.lean) | The ordered integer lift projects to the actual directed dart orbit on the torus (under `Torus.stepPerm`) at every step. |
| [`LoopMidpoints`](TorusTopology/LoopMidpoints.lean) | A lattice embedding of the lifted smoothed loops. |
| [`LoopOrbitLift`](TorusTopology/LoopOrbitLift.lean) | Ordered periods and integer displacement of the actual dart orbits. |
| [`LoopPhaseCrossings`](TorusTopology/LoopPhaseCrossings.lean) | A loop of positive vertical winding b gives b distinct crossing clusters in the seam-closed cylinder, all within its original incident primal cluster. |
| [`MidpointCyclicTurning`](TorusTopology/MidpointCyclicTurning.lean) | Declarations: `portCompass`, `portCompass_quarterTurn`, `squareDartCompass_eq_portCompass`, `loopMidpointWalk_compassDirections`, … |
| [`MidpointTurning`](TorusTopology/MidpointTurning.lean) | Rotation-preserving transport of the actual turning sum to the lifted square-lattice midpoint polygon. |
| [`MidpointWalk`](TorusTopology/MidpointWalk.lean) | Actual square-lattice walks traversing the lifted midpoint polygons. |
| [`NonzeroWindingTurning`](TorusTopology/NonzeroWindingTurning.lean) | The essential-loop turning classification, on the exact torus loop carrier `Torus.Loop` used in Corollary 3.13. |
| [`PeriodicCurveBasics`](TorusTopology/PeriodicCurveBasics.lean) | Simplicity of the complete periodic lift, rather than only its first period. |
| [`PeriodicLatticeTurning`](TorusTopology/PeriodicLatticeTurning.lean) | Every actual simple periodic lattice curve has zero turn over a period. |
| [`PeriodicMidpointLift`](TorusTopology/PeriodicMidpointLift.lean) | The actual midpoint lift is periodic up to its geometric deck displacement. |
| [`PeriodicSupportingLine`](TorusTopology/PeriodicSupportingLine.lean) | Supporting phases and finite sums for an actual periodic lattice curve. |
| [`PhaseCrossings`](TorusTopology/PhaseCrossings.lean) | Each nonzero modular phase flux forces a genuine bottom-to-top cylinder component. |
| [`PhaseFlux`](TorusTopology/PhaseFlux.lean) | Conserved seam flux splits equally among the modular phases. |
| [`PlanarFiniteCompassFan`](TorusTopology/PlanarFiniteCompassFan.lean) | Declarations: `compassSectorBoundary`, `primalCompassQuarterTurn`, `compassSectorBoundary_zero_eq_empty_or_univ`, `primalCompassQuarterTurn_eq_sector_boundary_formula` |
| [`PlanarFiniteCycleSupportedFlow`](TorusTopology/PlanarFiniteCycleSupportedFlow.lean) | Declarations: `cycleFlow_zero_sum_on_neighborPair`, `cycleSupportedFlow_constantOnDarts`, `cycleSupportedFlow_constantOnDarts_sign` |
| [`PlanarFiniteEvenForest`](TorusTopology/PlanarFiniteEvenForest.lean) | Declarations: `walk_support_reachable_from`, `eq_bot_of_isAcyclic_even_degree` |
| [`PlanarFiniteEvenSubgraphOfCycle`](TorusTopology/PlanarFiniteEvenSubgraphOfCycle.lean) | Declarations: `evenSubgraphOfCycle_eq_bot_or_cycle` |
| [`PlanarFiniteEvenSymmDiff`](TorusTopology/PlanarFiniteEvenSymmDiff.lean) | Declarations: `card_symmDiff_add_two_card_inter`, `neighborFinset_symmDiff`, `degree_even_symmDiff` |
| [`PlanarFiniteEvenTriangularElimination`](TorusTopology/PlanarFiniteEvenTriangularElimination.lean) | Declarations: `faceSymmDiffList`, `locallyFiniteOfFintype`, `exists_faceSymmDiffList_of_even_subgraph` |
| [`PlanarFiniteFaceSubfamilyBoundary`](TorusTopology/PlanarFiniteFaceSubfamilyBoundary.lean) | Declarations: `faceSymmDiffList_edge_mem_mono_of_no_cross_shared_edge`, `faceSymmDiffList_le_of_no_cross_shared_edge` |
| [`PlanarFiniteTriangularFaceIndependence`](TorusTopology/PlanarFiniteTriangularFaceIndependence.lean) | Declarations: `faceSymmDiffList_edge_iff_countP_mod` |
| [`PlanarFiniteTriangularFaceUniqueness`](TorusTopology/PlanarFiniteTriangularFaceUniqueness.lean) | Declarations: `faceSymmDiffList_eq_implies_toFinset_eq` |
| [`PlanarFiniteTriangularPivotReachability`](TorusTopology/PlanarFiniteTriangularPivotReachability.lean) | Declarations: `reachable_of_walk_steps`, `reachable_of_sym2_pair`, `finiteTriangularPivotReachability` |
| [`PlanarLattice`](TorusTopology/PlanarLattice.lean) | The square lattice and its finite closed boxes. |
| [`PlanarParafermionicCoverBoxConnectivity`](TorusTopology/PlanarParafermionicCoverBoxConnectivity.lean) | Declarations: `coverBoxPoint`, `cover_horizontal_right_adj`, `box_vertical_down_walk`, `box_vertical_negative_up_walk`, … |
| [`PlanarParafermionicCoverCompass`](TorusTopology/PlanarParafermionicCoverCompass.lean) | Declarations: `parafermionicCoverCompassBaseNeighbor`, `parafermionicCoverCompassNeighbor`, `parafermionicCoverCompassBaseNeighbor_injective`, `parafermionicCoverCompassBaseNeighbor_adj`, … |
| [`PlanarParafermionicCoverCycleCompassTurn`](TorusTopology/PlanarParafermionicCoverCycleCompassTurn.lean) | Declarations: `parafermionicCoverWalkCompassDirections`, `parafermionicCoverWalkCompassDirections_nil`, `parafermionicCoverWalkCompassDirections_cons`, `parafermionicCoverWalkCompassDirections_append`, … |
| [`PlanarParafermionicCoverEulerCount`](TorusTopology/PlanarParafermionicCoverEulerCount.lean) | Declarations: `parafermionicCoverFiniteEulerCount` |
| [`PlanarParafermionicCoverFaceAdjacency`](TorusTopology/PlanarParafermionicCoverFaceAdjacency.lean) | Declarations: `parafermionicCoverFiniteFaceAdjacencyGraph`, `parafermionicCoverFiniteFaceAdjacencyGraph_adj_iff`, `parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph`, `parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_none_some_iff`, … |
| [`PlanarParafermionicCoverFaceBoundaryDivergence`](TorusTopology/PlanarParafermionicCoverFaceBoundaryDivergence.lean) | Declarations: `coverFaceDartList`, `coverFaceVertices_nodup`, `coverFaceDartList_nodup`, `coverFaceDartList_toFinset`, … |
| [`PlanarParafermionicCoverFaceBoundaryGraph`](TorusTopology/PlanarParafermionicCoverFaceBoundaryGraph.lean) | Declarations: `coverFace_box_mem`, `coverFaceActualCycle_spec`, `parafermionicCoverFiniteFaceBoundaryGraph`, `parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph`, … |
| [`PlanarParafermionicCoverFaceChainDecomposition`](TorusTopology/PlanarParafermionicCoverFaceChainDecomposition.lean) | Declarations: `coverChainLocallyFiniteOfFintype`, `coverFiniteFacePivot_boundary_classification`, `parafermionicCoverFiniteFaceChainDecomposition` |
| [`PlanarParafermionicCoverFaceChainUniqueness`](TorusTopology/PlanarParafermionicCoverFaceChainUniqueness.lean) | Declarations: `parafermionicCoverFiniteFacePivot_boundary_classification`, `parafermionicCoverFiniteFaceChain_toFinset_unique`, `parafermionicCoverFiniteFaceChain_unique_representation` |
| [`PlanarParafermionicCoverFaceCornerCompass`](TorusTopology/PlanarParafermionicCoverFaceCornerCompass.lean) | Declarations: `parafermionicCoverFiniteFaceCorner_next_adjacent`, `parafermionicCoverFiniteFaceCorner_next_base`, `parafermionicCoverFiniteFaceCorner_next_compass`, `parafermionicCoverFiniteFaceCorner_prev_compass`, … |
| [`PlanarParafermionicCoverFaceCorners`](TorusTopology/PlanarParafermionicCoverFaceCorners.lean) | Declarations: `parafermionicCoverFaceCorner`, `parafermionicCoverFaceCorner_zero`, `parafermionicCoverFaceCorner_one`, `parafermionicCoverFaceCorner_two`, … |
| [`PlanarParafermionicCoverFaceEdgeIncidence`](TorusTopology/PlanarParafermionicCoverFaceEdgeIncidence.lean) | Declarations: `CoverFiniteFaceDart`, `coverFaceDartBoxPair`, `coverFiniteFaceRawEdge_iff_dart`, `coverFaceDart_boxEdge_orientation`, … |
| [`PlanarParafermionicCoverFaceOrientedBoundary`](TorusTopology/PlanarParafermionicCoverFaceOrientedBoundary.lean) | Declarations: `parafermionicCoverFacePositiveDartCount`, `parafermionicCoverFaceBoundaryCoefficient`, `coverFaceDarts_no_opposite`, `list_countP_xor_mod`, … |
| [`PlanarParafermionicCoverFacePivotBypass`](TorusTopology/PlanarParafermionicCoverFacePivotBypass.lean) | Declarations: `reachable_of_sym2_pair_eq`, `parafermionicCoverFiniteFaceTopPivot_bypass` |
| [`PlanarParafermionicCoverFacePivotGeometry`](TorusTopology/PlanarParafermionicCoverFacePivotGeometry.lean) | Declarations: `ParafermionicCoverFiniteFaceTopIndex`, `parafermionicCoverFiniteFaceTopPivot`, `parafermionicCoverFiniteFaceTopPivot_map`, `parafermionicCoverFiniteFaceTopPivot_injective`, … |
| [`PlanarParafermionicCoverFaceSetBoundary`](TorusTopology/PlanarParafermionicCoverFaceSetBoundary.lean) | Declarations: `coverFaceSetLocallyFinite`, `faceSymmDiffList_even_degree`, `parafermionicCoverFiniteFaceSetBoundaryGraph`, `parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree`, … |
| [`PlanarParafermionicCoverFaceSetBoundaryPivot`](TorusTopology/PlanarParafermionicCoverFaceSetBoundaryPivot.lean) | Declarations: `parafermionicCoverFiniteFaceSetBoundaryGraph_maximal_pivot_mem`, `parafermionicCoverFiniteFaceSetBoundaryGraph_exists_pivot` |
| [`PlanarParafermionicCoverFaceSetEdgeCount`](TorusTopology/PlanarParafermionicCoverFaceSetEdgeCount.lean) | Declarations: `faceGraphEdges`, `coverFaceBoundary_edgeFinset_card_four`, `parafermionicCoverFiniteFaceSetEdgeSupport`, `parafermionicCoverFiniteFaceSetBoundaryEdges`, … |
| [`PlanarParafermionicCoverFaceSetPivotRemoval`](TorusTopology/PlanarParafermionicCoverFaceSetPivotRemoval.lean) | Declarations: `parafermionicCoverFiniteFaceSetWithoutPivotsGraph`, `parafermionicCoverFiniteFaceSetWithoutPivotsGraph_reachable_eq` |
| [`PlanarParafermionicCoverFaceSetPivots`](TorusTopology/PlanarParafermionicCoverFaceSetPivots.lean) | Declarations: `parafermionicCoverFiniteFaceSetPivots`, `parafermionicCoverFiniteFaceSetPivots_card`, `parafermionicCoverFiniteFaceSetPivots_subset_edgeSupport`, `parafermionicCoverFiniteFaceSetEdgeSupport_sdiff_pivots_card` |
| [`PlanarParafermionicCoverFaceSetVertexIncidence`](TorusTopology/PlanarParafermionicCoverFaceSetVertexIncidence.lean) | Declarations: `faceVertex0`, `faceVertex1`, `faceVertex2`, `faceVertex3`, … |
| [`PlanarParafermionicCoverFaceTopEdges`](TorusTopology/PlanarParafermionicCoverFaceTopEdges.lean) | Declarations: `parafermionicCoverFiniteFaceTopEdge`, `parafermionicCoverFiniteFaceTopEdge_endpoints_mem`, `parafermionicCoverFiniteFaceTopEdge_adjacent`, `parafermionicCoverFiniteFaceTopEdge_mem_edgeSet`, … |
| [`PlanarParafermionicCoverFaceTopRemoval`](TorusTopology/PlanarParafermionicCoverFaceTopRemoval.lean) | Declarations: `parafermionicCoverBoxGraphWithoutFaceTops`, `parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top`, `topEdge_ne_of_same_base_x`, `parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x`, … |
| [`PlanarParafermionicCoverFaceTopTree`](TorusTopology/PlanarParafermionicCoverFaceTopTree.lean) | Declarations: `parafermionicCoverFaceTopEdgeBox`, `parafermionicCoverFaceTopEdgeBox_map`, `parafermionicCoverFiniteFaceTopEdges`, `parafermionicCoverFiniteFaceTopEdges_subset`, … |
| [`PlanarParafermionicCoverFaceUnionCarrierTransport`](TorusTopology/PlanarParafermionicCoverFaceUnionCarrierTransport.lean) | Declarations: `parafermionicCoverFiniteFaceUnionGraph_edgeSet_eq_support`, `parafermionicCoverFaceUnionSubgraph_support_subset`, `parafermionicCoverFiniteFaceUnionCarrier_induce_reachable_iff`, `parafermionicCoverFiniteFaceUnionCarrier_induce_edgeSet_card` |
| [`PlanarParafermionicCoverFaceUnionConnectivity`](TorusTopology/PlanarParafermionicCoverFaceUnionConnectivity.lean) | Declarations: `parafermionicCoverFiniteFaceUnionGraph`, `parafermionicCoverFiniteFaceUnionCarrier`, `parafermionicCoverFiniteFaceUnionGraph_le_boxGraph`, `coverUnionFaceVertex0`, … |
| [`PlanarParafermionicCoverFaceVertexIncidenceBound`](TorusTopology/PlanarParafermionicCoverFaceVertexIncidenceBound.lean) | Declarations: `parafermionicCoverFaceBaseCorner_injective`, `parafermionicCoverFaceRightCorner_injective`, `parafermionicCoverFaceRightUpCorner_injective`, `parafermionicCoverFaceRightUpLeftCorner_injective` |
| [`PlanarParafermionicCoverFaces`](TorusTopology/PlanarParafermionicCoverFaces.lean) | Declarations: `parafermionicCoverFaceRightLift`, `parafermionicCoverFaceRightUpLift`, `parafermionicCoverFaceRightUpLeftLift`, `parafermionicCoverFaceLiftEndpoint`, … |
| [`PlanarParafermionicCoverFiniteEdgeCount`](TorusTopology/PlanarParafermionicCoverFiniteEdgeCount.lean) | Declarations: `parafermionicCoverForward`, `parafermionicCover_adj_forward_or_reverse`, `parafermionicCoverForward_not_reverse`, `coverHorizontalBase`, … |
| [`PlanarParafermionicCoverFiniteFaceCount`](TorusTopology/PlanarParafermionicCoverFiniteFaceCount.lean) | Declarations: `faceBaseRange`, `faceSheetRange`, `faceFullCarrier`, `faceBranchFiber`, … |
| [`PlanarParafermionicCoverFiniteFaceCycles`](TorusTopology/PlanarParafermionicCoverFiniteFaceCycles.lean) | Declarations: `parafermionicCoverFiniteOrdinaryFace_has_cycle` |
| [`PlanarParafermionicCoverFiniteFaceIncidence`](TorusTopology/PlanarParafermionicCoverFiniteFaceIncidence.lean) | Declarations: `parafermionicCoverFiniteFaceDarts`, `parafermionicCoverFiniteFaceDart_endpoints_mem`, `parafermionicCoverFiniteFaceDart_adjacent`, `parafermionicCoverFiniteFaceDart_unique` |
| [`PlanarParafermionicCoverFiniteFaces`](TorusTopology/PlanarParafermionicCoverFiniteFaces.lean) | Declarations: `coverFace_shift_right`, `coverFace_shift_up`, `coverFace_shift_left`, `coverFace_shift_down`, … |
| [`PlanarParafermionicCoverGraph`](TorusTopology/PlanarParafermionicCoverGraph.lean) | Declarations: `ParafermionicCoverVertex`, `parafermionicCoverSheetShift`, `parafermionicCoverAdjCases`, `parafermionicCoverSheetShift_reverse`, … |
| [`PlanarParafermionicCoverInteriorCorners`](TorusTopology/PlanarParafermionicCoverInteriorCorners.lean) | Declarations: `parafermionicCoverFiniteFaceSetBoundaryCoefficient_eq_zero_of_not_support`, `parafermionicCoverFiniteFaceSelectedCorners_sectorBoundary_eq_zero_of_not_support`, `parafermionicCoverFiniteFaceSelectedCorners_eq_univ_of_mem_unionCarrier_not_support` |
| [`PlanarParafermionicCoverPrimalCycleDirections`](TorusTopology/PlanarParafermionicCoverPrimalCycleDirections.lean) | Declarations: `parafermionicCoverCompassDirection`, `parafermionicCoverCompassDirection_neighbor`, `parafermionicCoverCompassDirection_reverse`, `parafermionicCoverPrimalCycleRotate_isCycle`, … |
| [`PlanarParafermionicCoverPrimalCycleTurnSum`](TorusTopology/PlanarParafermionicCoverPrimalCycleTurnSum.lean) | Declarations: `parafermionicCoverSimpleCycleFillingSet_boundarySupport_eq_walkSupport`, `parafermionicCoverSimpleCycleFillingSet_boundarySupport_toFinset`, `parafermionicCoverPrimalCycleTurnSum`, `parafermionicCoverPrimalCycleTurnSum_eq_support_sum_of_local_eq`, … |
| [`PlanarParafermionicCoverSelectedCornerCoefficient`](TorusTopology/PlanarParafermionicCoverSelectedCornerCoefficient.lean) | Declarations: `selectedCornerCoeff_positiveDartCount_le_one`, `selectedCornerCoeff_forward_count_one_iff`, `selectedCornerCoeff_reverse_count_one_iff`, `parafermionicCoverFacePositiveDartCount_eq_selectedCornerIndicator`, … |
| [`PlanarParafermionicCoverSelectedCornerNeighbors`](TorusTopology/PlanarParafermionicCoverSelectedCornerNeighbors.lean) | Declarations: `parafermionicCoverFiniteFaceSelectedCorner_neighbors_mem_box`, `parafermionicCoverFiniteFaceSelectedCorners_missing_of_outside_neighbor` |
| [`PlanarParafermionicCoverSelectedCorners`](TorusTopology/PlanarParafermionicCoverSelectedCorners.lean) | Declarations: `parafermionicCoverFiniteFaceSelectedCorners`, `parafermionicCoverFiniteFaceSelectedCorners_mem_iff`, `parafermionicCoverFiniteFaceSelectedCorners_card`, `parafermionicCoverFiniteFaceSelectedCorners_nonempty_iff_unionCarrier` |
| [`PlanarParafermionicCoverSelectedFaceIncidence`](TorusTopology/PlanarParafermionicCoverSelectedFaceIncidence.lean) | Declarations: `parafermionicCoverFiniteFaceSelectedIncidentFaces`, `parafermionicCoverFiniteFaceSelectedIncidentFaces_card_le_two`, `parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_odd`, `parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one` |
| [`PlanarParafermionicCoverSimpleCycleBoundaryCount`](TorusTopology/PlanarParafermionicCoverSimpleCycleBoundaryCount.lean) | Declarations: `parafermionicCoverSimpleCycleFillingSet_boundaryEdges_card_eq_length`, `faceSetBoundaryGraph_le_unionGraph`, `parafermionicCoverSimpleCycleFillingSet_boundarySupport_subset_unionCarrier`, `parafermionicCoverSimpleCycleFillingSet_boundarySupport_card_eq_length` |
| [`PlanarParafermionicCoverSimpleCycleBoundaryDefect`](TorusTopology/PlanarParafermionicCoverSimpleCycleBoundaryDefect.lean) | Declarations: `parafermionicCoverSimpleCycleFilling_boundary_defect` |
| [`PlanarParafermionicCoverSimpleCycleComplementConnectivity`](TorusTopology/PlanarParafermionicCoverSimpleCycleComplementConnectivity.lean) | Declarations: `parafermionicCoverSimpleCycleComplementCarrier`, `simpleCycleComplementNone`, `simpleCycleComplementFace`, `parafermionicCoverSimpleCycleComplementAdjacency_connected` |
| [`PlanarParafermionicCoverSimpleCycleEulerDefect`](TorusTopology/PlanarParafermionicCoverSimpleCycleEulerDefect.lean) | Declarations: `parafermionicCoverSimpleCycleFilling_euler_defect` |
| [`PlanarParafermionicCoverSimpleCycleFaceConnectivity`](TorusTopology/PlanarParafermionicCoverSimpleCycleFaceConnectivity.lean) | Declarations: `parafermionicCoverSimpleCycleFillingSet_induce_faceAdjacency_connected` |
| [`PlanarParafermionicCoverSimpleCycleFaceIndecomposable`](TorusTopology/PlanarParafermionicCoverSimpleCycleFaceIndecomposable.lean) | Declarations: `faceSymmDiffList_eq_of_perm`, `parafermionicCoverSimpleCycleFillingSet_no_disjoint_nonempty_subfamily`, `parafermionicCoverSimpleCycleFillingSet_boundary_eq` |
| [`PlanarParafermionicCoverSimpleCycleFilling`](TorusTopology/PlanarParafermionicCoverSimpleCycleFilling.lean) | Declarations: `coverCycle_spanningCoe_even_degree`, `parafermionicCoverSimpleCycle_unique_face_filling`, `parafermionicCoverSimpleCycleFillingSet`, `parafermionicCoverSimpleCycleFillingSet_spec` |
| [`PlanarParafermionicCoverSimpleCycleFillingContainment`](TorusTopology/PlanarParafermionicCoverSimpleCycleFillingContainment.lean) | Declarations: `fillingContainment_selectedIncident_mem`, `fillingContainment_support_mem_iff`, `fillingContainment_no_three_incident`, `fillingContainment_crossEdge_card_one`, … |
| [`PlanarParafermionicCoverSimpleCycleFillingEuler`](TorusTopology/PlanarParafermionicCoverSimpleCycleFillingEuler.lean) | Declarations: `parafermionicCoverSimpleCycleFilling_inducedGraph_isTree`, `parafermionicCoverSimpleCycleFilling_euler_count` |
| [`PlanarParafermionicCoverSimpleCycleLocalTurning`](TorusTopology/PlanarParafermionicCoverSimpleCycleLocalTurning.lean) | Declarations: `parafermionicCoverSimpleCycleLocalTurning` |
| [`PlanarParafermionicCoverSimpleCycleOrientation`](TorusTopology/PlanarParafermionicCoverSimpleCycleOrientation.lean) | (import-only module) |
| [`PlanarParafermionicCoverSimpleCyclePivotAcyclic`](TorusTopology/PlanarParafermionicCoverSimpleCyclePivotAcyclic.lean) | Declarations: `faceUnionGraph_edgeSet_subset_support`, `parafermionicCoverSimpleCyclePivotAcyclic` |
| [`PlanarParafermionicCoverSimpleCyclePivotCarrier`](TorusTopology/PlanarParafermionicCoverSimpleCyclePivotCarrier.lean) | Declarations: `parafermionicCoverSimpleCyclePivotGraph_induce_carrier_connected`, `parafermionicCoverFiniteFaceSetWithoutPivotsGraph_induce_carrier_edge_card_add_faces` |
| [`PlanarParafermionicCoverSimpleCycleSectorProfile`](TorusTopology/PlanarParafermionicCoverSimpleCycleSectorProfile.lean) | Declarations: `primalCycleRotate_isCycle`, `primalCycleRotate_not_nil`, `primalCycle_selectedCoefficient_outgoing`, `primalCycle_selectedCoefficient_incoming`, … |
| [`PlanarParafermionicCoverSimpleCycleTurning`](TorusTopology/PlanarParafermionicCoverSimpleCycleTurning.lean) | Declarations: `parafermionicCoverPrimalCycleTurnSum_eq_four_or_neg_four` |
| [`PlanarParafermionicCoverUnselectedBoundary`](TorusTopology/PlanarParafermionicCoverUnselectedBoundary.lean) | Declarations: `coverFaceSetPositiveDartCount_le_one`, `coverFaceSetDarts_no_opposite`, `coverFaceSet_exists_dart`, `coverFaceSet_not_three_incident`, … |
| [`PlanarParafermionicCoverVertexNeighbors`](TorusTopology/PlanarParafermionicCoverVertexNeighbors.lean) | Declarations: `parafermionicCoverGraph_neighborSet_eq_neighborLift_image` |
| [`PlanarParafermionicCoverWalkFiniteBox`](TorusTopology/PlanarParafermionicCoverWalkFiniteBox.lean) | Declarations: `parafermionicCoverWalkVertexHeight`, `exists_box_height_for_list`, `parafermionicCoverWalk_support_subset_some_box`, `parafermionicCoverWalk_exists_box_restriction`, … |
| [`PositiveLoops`](TorusTopology/PositiveLoops.lean) | U counts positive winding with multiplicity. |
| [`RightwardPeriodicTurning`](TorusTopology/RightwardPeriodicTurning.lean) | A simple periodic lattice curve with rightward deck displacement has zero turn over a period. |
| [`SeamWinding`](TorusTopology/SeamWinding.lean) | The zigzag seam bound, via the homotopic primal and dual ribbon shadows. |
| [`SquareLatticeTurning`](TorusTopology/SquareLatticeTurning.lean) | The discrete Umlaufsatz on the project's literal square lattice. |
| [`StripCover`](TorusTopology/StripCover.lean) | Lifting the finite annular strip while retaining its horizontal coordinates. |
| [`StripPotential`](TorusTopology/StripPotential.lean) | A missing annular strip crossing makes the horizontal winding cocycle an actual vertex coboundary. |
| [`UnitWindingContract`](TorusTopology/UnitWindingContract.lean) | The corrected complete U=1 loop-homology structure for the torus correspondence (Corollary 3.13). |
| [`UnitWindingHomology`](TorusTopology/UnitWindingHomology.lean) | The complete homological form of U=1: the two essential loops have opposite classes (a,1) and (-a,-1), with no restriction on the integer a. |
| [`UnitWindingStructure`](TorusTopology/UnitWindingStructure.lean) | The exact vertical support when U=1. |
| [`UpperReturnGeometry`](TorusTopology/UpperReturnGeometry.lean) | A supporting-line return for a simple periodic lattice arc. |
| [`VerticalSupport`](TorusTopology/VerticalSupport.lean) | The weak form of the vertical loop structure for U = 1 (at most two loops with nonzero vertical winding), required by the sector estimate, uses only the absolute winding mass, not classification of essential torus curves… |
| [`WindingPhase`](TorusTopology/WindingPhase.lean) | An integer winding divisor gives a modular vertex phase, constant on seam-closed components. |
| [`ZeroWindingTurning`](TorusTopology/ZeroWindingTurning.lean) | The contractible-loop turning classification, on the exact torus loop carrier `Torus.Loop` used in Corollary 3.13. |

### TorusCrossing

| Module | Summary |
|---|---|
| [`BaseConn`](TorusCrossing/BaseConn.lean) | The dual board graph is connected |
| [`BdConn`](TorusCrossing/BdConn.lean) | The boundary of the exploration is connected The boundary edges of the explored region separate the class `U` (joined to the row `p₂`) from the class `X` (the rest). |
| [`BdEven`](TorusCrossing/BdEven.lean) | Parity of boundary edges at primal cells Around a primal cell `c` the four crossing dual edges form a 4-cycle through the odd cells `W, S, E, N`. |
| [`Cochain`](TorusCrossing/Cochain.lean) | Indicator cochains: edges and collar paths `ind A` is the `ZMod 2`-valued indicator of a finite set of medial vertices. |
| [`Cut`](TorusCrossing/Cut.lean) | Parity of a vertex cut around an odd cell For a set `X` of primal cells, an edge of the board is *cut* when exactly one of its ends lies in `X`. |
| [`EndGraph`](TorusCrossing/EndGraph.lean) | Graphs given by their edge-end maps Both the primal board graph and the dual board graph are of the form: vertex set `P` (a finite set of cells) and one edge `ends m` for each medial vertex `m` of a finite set `M`. |
| [`Euler`](TorusCrossing/Euler.lean) | Euler's relation for the mixed board and exact weight duality Flipping a closed edge `m` of a primal configuration `A` changes the number `kP` of wired primal clusters by `-1` exactly when the ends of `m` are not connect… |
| [`Exact`](TorusCrossing/Exact.lean) | Closed one-cochains are exact (planar Poincare lemma on the rotated lattice) A `ZMod 2`-valued function `f` on medial vertices is a *cochain*; its *degree* at a cell is the sum over the four corners. |
| [`Exclusion`](TorusCrossing/Exclusion.lean) | Exclusion: a primal connection and a crossing dual connection cannot coexist If two primal cells are connected (with the bottom and top rows wired) in the configuration `A`, then the dual endpoints of any closed edge `m`… |
| [`Existence`](TorusCrossing/Existence.lean) | Existence: a missing primal connection forces a dual connection If two primal cells joined by a closed edge `m` are not connected (rows wired), the dual endpoints of `m` are connected in the complementary dual configurat… |
| [`Explore`](TorusCrossing/Explore.lean) | Exploration of the dual cluster of a boundary row For a board `R`, an open edge set `A ⊆ R.inner`, and a row `p₁` of faces, let `D₁` be the set of odd cells reachable from the row `p₁` through dual-open edges. |
| [`ExploreLocal`](TorusCrossing/ExploreLocal.lean) | Local structure of the exploration at primal cells For an exploration of a board `R` (port rows `p₁` the source row and `p₂` the opposite row): every corner edge of a primal cell on the row `p₁` is explored; a corner edg… |
| [`Fiber`](TorusCrossing/Fiber.lean) | The conditional crossing bound given the two explorations Conditionally on the state of all explored edges of the two explorations (a *fiber*), the probability of a crossing from the lower boundary to the upper boundary … |
| [`Final`](TorusCrossing/Final.lean) | The crossing estimate (3.19) For every `q ≥ 1` there is `c > 0` such that for all even periods `N, M ≥ 4` and all `n ≥ 1` with `3n ≤ min(N, M)`, the torus random-cluster measure at `p_c(q)` gives probability at least `c`… |
| [`Hex`](TorusCrossing/Hex.lean) | Hex-type existence: no vertical primal crossing forces a horizontal dual crossing The cut edges of the component of the bottom row, which contains no top cell, form a dual subgraph in which every odd cell strictly betwee… |
| [`Ivt`](TorusCrossing/Ivt.lean) | A discrete intermediate value property for paths If a path moves the integer level `r` by at most one at each step, then a path from level `≤ c` to level `≥ c + k` contains a sub-path from level `c` to level `c + k` stay… |
| [`Lattice`](TorusCrossing/Lattice.lean) | Cells, medial vertices and the local incidence of the rotated lattice Planar bookkeeping for the diamond random-cluster lattice. |
| [`Local`](TorusCrossing/Local.lean) | A local lemma at a primal cell Around a primal cell `c` of a board, the (up to four) inner medial vertices of its corners carry the dual edges `W S`, `E S`, `N W`, `N E` of the 4-cycle `W - S - E - N`. |
| [`Markov`](TorusCrossing/Markov.lean) | Domain Markov property and boundary comparison for an embedded subgraph A conditioning of the FK measure of a graph `H` on the exact state of all edges outside an embedded subgraph `G` gives, on `G`, the FK law with the … |
| [`Mixture`](TorusCrossing/Mixture.lean) | Mixture lifting from an embedded board to the ambient graph The law of the restriction of the FK measure of `H` to an embedded subgraph `G` is a mixture, over the state of the remaining edges, of FK laws of `G` with vari… |
| [`Planar`](TorusCrossing/Planar.lean) | Rectangular boards of the rotated lattice, with their primal and dual graphs `Rect` is a block of cells `[x0, x0 + w] × [y0, y0 + h]`. |
| [`Rotation`](TorusCrossing/Rotation.lean) | The quarter-turn of an odd square exchanges primal and dual For a square board of odd side the rotation by a quarter turn about its centre maps the odd cells onto the primal cells and carries the dual graph isomorphicall… |
| [`SelfDual`](TorusCrossing/SelfDual.lean) | Exact weight duality of the mixed board at the self-dual point At `p = p_c(q)` the Fortuin-Kasteleyn weight of a primal configuration `A` (rows wired) is a fixed constant multiple of the weight of the complementary dual … |
| [`Square`](TorusCrossing/Square.lean) | The mixed-boundary square crossing bound ([BefDum12]) For an odd square board with the bottom and top rows wired (separately) and free sides, the critical random-cluster measure gives probability at least `1/(1+q)` (henc… |
| [`SubGraph`](TorusCrossing/SubGraph.lean) | The graph of unexplored edges For a set `Ex` of medial vertices of a board `Q` (the explored edges), the unexplored edges `Un = Q.inner \ Ex` form a graph `subG` on the cells they touch; it embeds in `Q.pG`. |
| [`TorusBarrier`](TorusCrossing/TorusBarrier.lean) | Failure of a barrier gives a vertical crossing of the translated dual configuration A dual-open path of a board, joining the two port rows of a sub-board, becomes (after the unit horizontal translation exchanging face co… |
| [`TorusDict`](TorusCrossing/TorusDict.lean) | Dictionary between boards of the rotated lattice and the diamond torus A board whose cell block fits in one period of the torus embeds in the primal diamond torus graph. |
| [`TorusEvents`](TorusCrossing/TorusEvents.lean) | Torus crossing events seen from a board Conversion of cell-level open paths of a board (for the primal configuration, and for the complementary translated configuration) into walks of the lifted strip graph of the torus. |
| [`TorusTranslate`](TorusCrossing/TorusTranslate.lean) | Translation invariance of the indexed torus law For `a + b` even, the translation of the indexed configuration by `(a, b)` preserves the cluster count, hence the law. |
| [`TwoBoard`](TorusCrossing/TwoBoard.lean) | Two explorations in the two ends of a board A board `Q` contains a bottom sub-board `B` (height `bB`) and a top sub-board `T` (height `bT`), with at least one row of gap. |
| [`WiringCompare`](TorusCrossing/WiringCompare.lean) | Comparing two wirings that differ by one identification If a boundary condition `η` is obtained from `ξ` by wiring one more pair `(b₀, t₀)` of classes together, then the number of clusters changes by at most one, and not… |

