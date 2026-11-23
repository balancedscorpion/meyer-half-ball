# Independent half-ball counts for crystalline measures

Work in progress on Theorem A.3 in Jamie Martin’s *Half-line density, spectral generation and lattice structure of crystalline measures* (23 November 2026, pp. 19–22).

The target is one integer bounding the number of sites in every open unit ball on the measured side. The centre may lie anywhere. The closed half-space includes its boundary. The assumptions are local finiteness, a unit vector, a common bound on ordered patch volumes, and an upper site count along one sequence of origin-centred closed half-balls. The definition of the target in [the statement module](HalfBall/Statement.lean) is independent of Fourier analysis.

## Checked results

- [Energy decomposition](HalfBall/Decomposition.lean) extracts disjoint small-difference pieces and bounds the remaining additive energy. Its constants and maximum number of pieces are uniform in the scale.
- [Mixed energy](HalfBall/Energy.lean) bounds the fourth power of a representation count involving a remainder coordinate.
- [Lemma A.5 from A.4](HalfBall/Representations.lean) constructs all retained pieces and their signed representations on one subsequence. The proof chooses the energy threshold before extracting pieces, sums over eight sign patterns and three possible remainder positions, and allows repeated labels.
- [Subsequence selection](HalfBall/Subsequence.lean) gives simultaneous limits for the normalized packing numbers of a finite list of labels.
- [Lemma A.6](HalfBall/LocalCount.lean) bounds the number of qualifying anchors for all signed tuples at a scale. For a single tuple, encode a packed site and a representation by the difference from the first coordinate and the two remaining coordinates. In a ball of radius 1/7, two anchors have multiplied displacement of norm less than one. The separated packing makes this encoding injective. A finite translated cover then gives the unit-ball estimate.
- The theorem `HalfBall.geometric_local_count_of_representations` takes the signed representation data of A.5 as an explicit hypothesis. Each fixed anchor can have its own threshold on the shared subsequence. The proof intersects finitely many eventual bounds to obtain one index for all sites in a proposed cluster.

## Open proof obligations

The implication from the ordered patch bound to the anchored exact-triple estimate in A.4 is open. The theorem `HalfBall.geometric_local_count_of_anchored_triangles` derives the unit-ball cap with that exact-triple estimate as its sole additional mathematical hypothesis. The independent [Palomar Challenge](Challenge.lean) states the unconditional A.3 and contains the intentional Challenge placeholder. The proof library builds independently of it. There is no unconditional Solution declaration yet.

The two-carrier Fourier implication, Appendix B’s classification with arbitrary complex weights and the Poisson converse are further milestones. The earlier uniformly discrete classification requires a positive spacing and cannot be applied to every relatively separated carrier. [MeyerGeneralProblem](https://github.com/ls558/MeyerGeneralProblem/tree/43a4a33069b48d7f303113a3a2ffab25c15f4c8f/lean) · [Uniformly discrete result](https://github.com/balancedscorpion/lev-olevskii-lattice-cover)

## Reproduce

With Elan installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Axioms.lean
lake build Challenge
```

The project pins Lean 4.35.0-rc3 and Mathlib in the lockfile. The Challenge build is expected to report its statement placeholder. The independent mathlib-only Challenge follows the [submission reference](https://github.com/balancedscorpion/countably-infinite-dimension-strong-meyer-spaces). Palomar submission awaits an unconditional Solution, a comparison against Challenge and review of the verified commit.

## Sources and licence

Jamie Martin supplied the mathematical argument. Codex prepared the Lean development. The Apache-2.0 Balog–Szemerédi–Gowers proof is adapted from Joris Roos’s trilinear Hilbert transform project at a fixed revision. The file retains its source header. [Upstream BSG proof](https://github.com/roos-j/lean-trilinearht/blob/7b4209609e6a7fb9d9935973ee8541495f943660/TrilinearHT/Auto/Prerequisites/BalogSzemerediGowers.lean) · [Licence](LICENSE)
