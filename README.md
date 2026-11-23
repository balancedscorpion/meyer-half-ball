# Independent half-ball counts characterize finite sums of lattice combs

For a crystalline measure on ℝᵖ, p ≥ 1, independently chosen physical and spectral half-ball counts characterize finite sums of shifted, modulated full-rank lattice combs. Each term can have its own lattice and arbitrary complex coefficient. The support and spectrum may each contain arbitrarily close distinct sites. This branch proves both implications of Theorem 1.1 and the geometric Theorem A.3 of Jamie Martin’s *Half-line density, spectral generation and lattice structure of crystalline measures* (23 November 2026). [Challenge](HalfBallChallenge.lean) · [Solution](HalfBallSolution.lean)

The half-balls are closed and centred at the origin. On each side there must exist a unit normal and positive radii tending to infinity along which the number of sites is eventually bounded by a constant times the radius to the power p. Counts use actual nonzero atoms after cancellation. A crystalline measure here is a tempered distribution with locally finite atomic expansions on compactly supported tests on both Fourier sides.

## Theorem A.3

Let B be locally finite in Euclidean space of dimension p ≥ 1 and let η be a unit vector. Assume both of the following.

1. One finite real number bounds the total Lebesgue volume of every admissible ordered patch family at every site s. Each patch is a positive-volume finite union of closed coordinate boxes. Its self-differences, translated by s, meet B only at s. For i > k the translated differences from the kth to the ith patch avoid B.
2. Along some positive radii tending to infinity, the number of sites in the origin-centred closed ball on the side ⟨η,s⟩ ≥ 0 is eventually at most C times the radius to the power p.

Then some natural number M bounds the number of distinct s in B satisfying ⟨η,s⟩ ≥ 0 and ‖s − y‖ < 1, for every centre y in the entire space. Sites on the bounding hyperplane count. Site isolation can vary from point to point.

### Proof of A.3

| Manuscript | Lean proof |
| --- | --- |
| A.4, exact signed-offset triples | [Anchored triangle bound](HalfBall/AnchoredTriangles.lean). Sampling coarse cells, deleting conflicting cells and estimating independent sets in the remaining triangle-free graph give enough fine-cell volume to violate the ordered patch bound if there are too few triples. [Sampling and deletion](HalfBall/Combinatorics/Pruning.lean) · [Triangle-free independent sets](HalfBall/Combinatorics/IndependentSet.lean) · [Ordered patches](HalfBall/Geometry/Patches.lean) |
| A.5, signed representations | [Common-subsequence proof](HalfBall/Representations.lean). Repeated Balog–Szemerédi–Gowers extraction leaves a low-energy remainder. All normalized packing fractions converge on one subsequence chosen before any anchor. The surviving labels and three signs may vary with the anchor and scale. [Decomposition](HalfBall/Decomposition.lean) · [Remainder estimate](HalfBall/Energy.lean) · [Counting signed triples](HalfBall/Forcing.lean) |
| A.6, represented anchors | [Local cap](HalfBall/LocalCount.lean). For one tuple, encode a packed site and a representation by subtracting the packed site from the first coordinate and recording the remaining two. In a ball of radius 1/7 the odd signed multiplier gives an injective encoding. A finite translated cover and the finite list of tuples give the unit-ball bound. [Injection](HalfBall/Packing.lean) |
| A.3, arbitrary centres | [Theorem](HalfBallSolution.lean). For a finite family of measured sites in a ball, intersect their eventual representation bounds on the common subsequence. At a late index all sites qualify together. Local finiteness supplies the finite set whose cardinality appears in the conclusion. |

The fine boxes have half the cell side and are ordered by corner height. A mesh below the least nonzero absolute site projection makes every site displacement from an earlier to a later box nonnegative in height. This gives the ordered exclusions directly and accounts for a dimension-dependent volume factor.

## Reproduce

Install Elan and run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Axioms.lean
lake env lean checks/Carriers.lean
lake env lean checks/Classification.lean
lake env lean checks/Converse.lean
```

The project pins Lean 4.35.0-rc3 and Mathlib commit `d870b9068518a0870842d15a0cd42637ec30b587`. The Challenge has one intentional placeholder for each of the two compared declarations. The Solution and all its proof dependencies build independently of the Challenge. Lean prints:

```text
'HalfBall.geometric_local_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'HalfBall.half_ball_theorem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

On Linux with Bubblewrap installed, run `lake env lake comparator --config comparator.json`. The manual Palomar workflow checks the public commit selected for dispatch. Intake and registration are separate decisions. [Comparator scope](comparator.json) · [Workflow](.github/workflows/palomar.yml) · [Palomar submission guidance](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

## Scope and provenance

The root Comparator configuration on this branch checks Theorems A.3 and 1.1 in one entry. The original A.3-only candidate remains on the main branch. The earlier uniformly discrete classification supplied proofs about individual lattices and the algebraic Laurent theorem. The proofs here derive the coefficient bounds needed for the full classification from the independent half-ball hypotheses. [MeyerGeneralProblem](https://github.com/ls558/MeyerGeneralProblem/tree/43a4a33069b48d7f303113a3a2ffab25c15f4c8f/lean) · [Uniformly discrete classification](https://github.com/balancedscorpion/lev-olevskii-lattice-cover)

Jamie Martin supplied the manuscript and task specification. Codex prepared the Lean development. The adapted Apache-2.0 BSG file retains its source header. [Pinned BSG source](https://github.com/roos-j/lean-trilinearht/blob/7b4209609e6a7fb9d9935973ee8541495f943660/TrilinearHT/Auto/Prerequisites/BalogSzemerediGowers.lean) · [Metadata](formalization.yaml) · [Licence](LICENSE)

## Theorem 1.1

The A.3 review candidate is [commit e5aa82e](https://github.com/balancedscorpion/meyer-half-ball/tree/e5aa82e3f879ff11f20975c34d748ce3840711a8). This branch also contains the following results.

1. [Lemma A.2](HalfBall/Recurrence.lean) proves that the approximate returns of each finite pattern meet every open ball of a fixed radius. The proof selects an ordered monochromatic list using an ultrafilter on a sequence of hypothetical holes of growing radius.
2. [Global count](HalfBall/GlobalCount.lean) moves a finite cluster into the measured half-space. The error tolerance depends on that cluster’s boundary margin and pairwise distances. Combining A.2 and A.3 gives a cap on all sites from the ordered patch and half-ball hypotheses.
3. [The two-carrier theorem](HalfBall/FourierPatch.lean) proves `HalfBall.both_carriers_relatively_separated` from independent physical and spectral half-ball data. It derives the finite-constant ordered patch estimate, applies A.2 and A.3, and uses [Fourier reflection](HalfBall/FourierCarriers.lean) to exchange the carriers. The hypotheses allow arbitrarily close sites and require only the local atomic expansions on compact tests. The proof establishes the existence of a finite patch constant. The manuscript’s sharper numerical constant is outside this declaration.
4. [The full-dimensional converse](HalfBall/Converse.lean) proves that a finite sum of shifted and modulated full-rank lattice combs satisfies the two half-ball hypotheses. Each summand has its own basis, shift, frequency and complex coefficient. The empty sum is allowed. The proof periodizes a compact test on the standard torus and unfolds its Fourier coefficients over translated coordinate boxes. [Poisson summation](HalfBall/Poisson/Summation.lean) and the [inverse-transpose formula](HalfBall/Poisson/Comb.lean) give a finite lattice-coset cover on the Fourier side. A compact test isolates each actual site, including when different summands cancel nearby or at the same point. The [lattice count](HalfBall/LatticeCount.lean) gives a bound in every translated closed ball and hence along arbitrary independently chosen positive divergent radii on the two sides.

Run `lake build`, `lake env lean checks/Carriers.lean`, and `lake env lean checks/Converse.lean` on this branch. Lean reports `[propext, Classical.choice, Quot.sound]` for `HalfBall.half_ball_converse` and its existential-witness form `HalfBall.independentHalfBallData_of_weighted_combs`. Lean reports the same axioms for `HalfBall.fourier_patch_estimate` and `HalfBall.both_carriers_relatively_separated`.

### The ordered Fourier patch estimate

For one ordered patch family, the [physical rank bound](HalfBall/Fourier/PhysicalRank.lean) factors a finite matrix through the atoms in the measured half-ball. A [compact spectral model](HalfBall/Fourier/AtomicModel.lean) approximates its entries with an error that decays faster than any fixed inverse power of the scale. [Separated samples](HalfBall/Fourier/PatchSampling.lean) control the volume of every patch. Ordering gives small entries below the diagonal blocks, and separation bounds the off-diagonal sums within each block. [Scaling the blocks](HalfBall/Fourier/BlockRank.lean) gives a full-rank matrix at sufficiently large scale. Comparing ranks yields one volume bound for all patch families.

The reflection and separated-sum estimates adapt parts of the author’s earlier uniformly discrete development. [Pinned source repository](https://github.com/balancedscorpion/lev-olevskii-lattice-cover/tree/f78b7d12876f95be3bce8b37ee57684d51b21d9c/AppendixA) · [MIT licence](LICENSES/lev-olevskii-lattice-cover-MIT.txt)

### Appendix B

[Qualitative window detection](HalfBall/Classification/Detection.lean) proves that compact spectral tests in one ball suffice to detect whether a distribution vanishes. The ball depends only on the dimension and the unit-ball count. The proof partitions the sites into separated classes and uses one isolating factor per class. It allows arbitrarily close pairs across classes and uses the local atomic expansion only on compact tests.

[Filtered density](HalfBall/Classification/FilteredDensity.lean) proves that a trigonometric polynomial which is nonzero at one physical site is nonzero at sites in every sufficiently large ball. The [character rank estimate](HalfBall/Classification/CharacterRank.lean) controls the rank of finite lists of modulations on the actual carrier.

[Finite generation](HalfBall/Classification/FiniteGeneration.lean) proves that the spectral sites in one bounded ball generate the full spectral group. To control differences of translates, the proof interpolates a power of a small-frequency character on each separated class and combines the classes by a telescoping identity. The bandwidth is independent of the power and the sites. Compact approximation gives a smooth test in one frequency window with exactly the required samples on a carrier and its translate. [Interpolation](HalfBall/Classification/CharacterInterpolation.lean) · [Test recovery](HalfBall/Classification/IsolatingRecovery.lean) · [Phase estimate](HalfBall/Classification/PhaseDifference.lean)

[The lattice-cover theorem](HalfBall/Classification/LatticeCover.lean) proves `HalfBall.lattice_covers_of_half_balls` from the original independent data. Fourier reflection gives finite generation for the other carrier. The proof of B.3 uses the verified unitary Laurent theorem from the author’s pinned development. Run `lake env lean checks/Classification.lean` for the axiom audit. [Pinned Laurent reduction](https://github.com/balancedscorpion/lev-olevskii-lattice-cover/blob/f78b7d12876f95be3bce8b37ee57684d51b21d9c/AppendixA/LaurentReduction.lean)

[Weight recovery](HalfBall/Weights/CombRecovery.lean) proves B.4. First, compact spectral tests uniformly bound weights at sites isolated by any fixed positive distance. A product of characters vanishing on the opposite lattice cover gives a finite recurrence. Along a subsequence of potential large weights, lattice translates have simultaneous limits. Displacements can be chosen so that every nonempty subset sum avoids all the proper affine subspaces where distinct sites can approach one another. The recurrence now bounds the original coefficient by uniformly bounded shifted coefficients. [Isolated sites](HalfBall/Weights/Isolation.lean) · [Collision limits](HalfBall/Weights/CollisionLimits.lean) · [Uniform coefficient bound](HalfBall/Weights/BoundedWeights.lean)

Uniform bounds on the coefficients give absolute convergence on Schwartz tests and bounded total variation on every translate of a fixed ball. Restriction to finite intersections of lattice cosets and inclusion–exclusion recover the exact coefficients, including cancellations on overlaps. Fourier inversion yields the physical comb formula. [Variation and summability](HalfBall/Weights/Records.lean) · [Restrictions](HalfBall/Weights/Restrictions.lean) · [Classification](HalfBall/Classification.lean)

The proof uses the finite patch constant required by A.3 and the translated-difference estimate required by B.2. The manuscript’s sharp A.1 constant and its stronger single-seminorm B.1 inequality for all Schwartz tests are outside the claims of this submission. Neither is an unproved dependency of the two exported theorems.
