# A geometric local count from half-ball data

**One integer bounds the number of measured sites in every open unit ball.** This repository proves Theorem A.3 of Jamie Martin’s *Half-line density, spectral generation and lattice structure of crystalline measures* (23 November 2026, pp. 19–22). [Challenge](Challenge.lean) · [Solution](Solution.lean)

Let B be locally finite in Euclidean space of dimension p ≥ 1 and let η be a unit vector. The two hypotheses are:

1. One finite real number bounds the total Lebesgue volume of every admissible ordered patch family at every site s. Each patch is a positive-volume finite union of closed coordinate boxes. Its self-differences, translated by s, meet B only at s. For i > k the translated differences from the kth to the ith patch avoid B.
2. Along some positive radii tending to infinity, the number of sites in the origin-centred closed ball on the side ⟨η,s⟩ ≥ 0 is eventually at most C times the radius to the power p.

Then some natural number M bounds the number of distinct s in B satisfying ⟨η,s⟩ ≥ 0 and ‖s − y‖ < 1, for every centre y in the entire space. Sites on the bounding hyperplane count. Site isolation can vary from point to point.

## Proof

| Manuscript | Lean proof |
| --- | --- |
| A.4, exact signed-offset triples | [Anchored triangle bound](HalfBall/AnchoredTriangles.lean). Sampling coarse cells, deleting conflicting cells and estimating independent sets in the remaining triangle-free graph give enough fine-cell volume to violate the ordered patch bound if there are too few triples. [Sampling and deletion](HalfBall/Combinatorics/Pruning.lean) · [Triangle-free independent sets](HalfBall/Combinatorics/IndependentSet.lean) · [Ordered patches](HalfBall/Geometry/Patches.lean) |
| A.5, signed representations | [Common-subsequence proof](HalfBall/Representations.lean). Repeated Balog–Szemerédi–Gowers extraction leaves a low-energy remainder. All normalized packing fractions converge on one subsequence chosen before any anchor. The surviving labels and three signs may vary with the anchor and scale. [Decomposition](HalfBall/Decomposition.lean) · [Remainder estimate](HalfBall/Energy.lean) · [Counting signed triples](HalfBall/Forcing.lean) |
| A.6, represented anchors | [Local cap](HalfBall/LocalCount.lean). For one tuple, encode a packed site and a representation by subtracting the packed site from the first coordinate and recording the remaining two. In a ball of radius 1/7 the odd signed multiplier gives an injective encoding. A finite translated cover and the finite list of tuples give the unit-ball bound. [Injection](HalfBall/Packing.lean) |
| A.3, arbitrary centres | [Theorem](Solution.lean). For a finite family of measured sites in a ball, intersect their eventual representation bounds on the common subsequence. At a late index all sites qualify together. Local finiteness supplies the finite set whose cardinality appears in the conclusion. |

The fine boxes have half the cell side and are ordered by corner height. A mesh below the least nonzero absolute site projection makes every site displacement from an earlier to a later box nonnegative in height. This gives the ordered exclusions directly and accounts for a dimension-dependent volume factor.

## Reproduce

Install Elan and run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Axioms.lean
```

The project pins Lean 4.35.0-rc3 and Mathlib commit `d870b9068518a0870842d15a0cd42637ec30b587`. The Challenge has one intentional placeholder. The Solution and all its proof dependencies build independently of the Challenge. Lean prints:

```text
'HalfBall.geometric_local_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

On Linux with Bubblewrap installed, run `lake env lake comparator --config comparator.json`. The manual Palomar workflow checks the public commit selected for dispatch. Intake and registration are separate decisions. [Comparator scope](comparator.json) · [Workflow](.github/workflows/palomar.yml) · [Palomar submission guidance](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

## Scope and provenance

The recorded theorem is A.3. To reach the paper’s Theorem 1.1, the ordered Fourier patch estimate and finite-pattern recurrence must supply global bounds for both actual carriers with independently chosen half-ball data. The remaining classification recovers the complex comb weights and its converse uses Poisson summation. The earlier uniformly discrete result assumes positive minimum spacing. [MeyerGeneralProblem](https://github.com/ls558/MeyerGeneralProblem/tree/43a4a33069b48d7f303113a3a2ffab25c15f4c8f/lean) · [Uniformly discrete classification](https://github.com/balancedscorpion/lev-olevskii-lattice-cover)

Jamie Martin supplied the manuscript and task specification. Codex prepared the Lean development. The adapted Apache-2.0 BSG file retains its source header. [Pinned BSG source](https://github.com/roos-j/lean-trilinearht/blob/7b4209609e6a7fb9d9935973ee8541495f943660/TrilinearHT/Auto/Prerequisites/BalogSzemerediGowers.lean) · [Metadata](formalization.yaml) · [Licence](LICENSE)

## Further work on this branch

The A.3 review candidate is [commit e5aa82e](https://github.com/balancedscorpion/meyer-half-ball/tree/e5aa82e3f879ff11f20975c34d748ce3840711a8). This branch also contains the following results.

1. [Lemma A.2](HalfBall/Recurrence.lean) proves that the approximate returns of each finite pattern meet every open ball of a fixed radius. The proof selects an ordered monochromatic list using an ultrafilter on a sequence of hypothetical holes of growing radius.
2. [Global count](HalfBall/GlobalCount.lean) moves a finite cluster into the measured half-space. The error tolerance depends on that cluster’s boundary margin and pairwise distances. Combining A.2 and A.3 gives a cap on all sites from the ordered patch and half-ball hypotheses.
3. [Fourier carriers](HalfBall/FourierCarriers.lean) proves reflection on compactly supported tests and applies the global count on both sides. The theorem `both_carriers_of_fourier_patch_estimate` explicitly takes `FourierPatchEstimate p` as an argument. This is the open Lemma A.1 deriving the ordered patch bound for the other carrier from one physical count. The physical and spectral directions and radii remain independent. There is no polynomial total-variation hypothesis. The reflection proof adapts [the earlier formalization](https://github.com/balancedscorpion/lev-olevskii-lattice-cover/blob/f78b7d12876f95be3bce8b37ee57684d51b21d9c/AppendixA/FourierReflection.lean) under its [MIT licence](LICENSES/lev-olevskii-lattice-cover-MIT.txt).

4. [The full-dimensional converse](HalfBall/Converse.lean) proves that a finite sum of shifted and modulated full-rank lattice combs satisfies the two half-ball hypotheses. Each summand has its own basis, shift, frequency and complex coefficient. The empty sum is allowed. The proof periodizes a compact test on the standard torus and unfolds its Fourier coefficients over translated coordinate boxes. [Poisson summation](HalfBall/Poisson/Summation.lean) and the [inverse-transpose formula](HalfBall/Poisson/Comb.lean) give a finite lattice-coset cover on the Fourier side. A compact test isolates each actual site, including when different summands cancel nearby or at the same point. The [lattice count](HalfBall/LatticeCount.lean) gives a bound in every translated closed ball and hence along arbitrary independently chosen positive divergent radii on the two sides.

Run `lake build`, `lake env lean checks/Carriers.lean`, and `lake env lean checks/Converse.lean` on this branch. Lean reports `[propext, Classical.choice, Quot.sound]` for `HalfBall.half_ball_converse` and its existential-witness form `HalfBall.independentHalfBallData_of_weighted_combs`. The remaining forward steps are A.1 and Appendix B’s derivation of the weighted comb representation from bounded local counts.
