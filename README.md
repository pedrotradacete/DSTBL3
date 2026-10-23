# DSTBL3

Lean 4 formalization accompanying the paper `Coordinate systems and maximal
order complexity in Banach lattices` by A. Aviles, C. Rosendal, M. A. Taylor
and P. Tradacete.

The repository is one Lake project containing the developments for Theorems
A, B, and C in the paper, concerning order and σ-order bases and complete
coanalytic sets in separable Banach lattices.

## Formalized results

| Paper result | Principal Lean declaration | Module |
|---|---|---|
| Proposition `order-sigma`: order convergence and σ-order convergence agree for sequences in a separable Banach lattice | `ThmA.orderConvergesTo_iff_sigmaOrderTendsto` | `Lean_Code.ThmA.OrderSigma` |
| Theorem A, σ-order maximal inequality | `ThmA.theoremA_sigma_order_form` | `Lean_Code.ThmA.MaximalInequality` |
| Theorem A, order-basis maximal inequality | `ThmA.theoremA_order_form` | `Lean_Code.ThmA.MaximalInequality` |
| Theorem A, Schauder-basis conclusions | `ThmA.theoremA_sigma_order_schauder`, `ThmA.theoremA_order_schauder` | `Lean_Code.ThmA.MaximalInequality` |
| Theorem B: some separable Banach lattice has Π¹₁-complete `X_{↓0}` | `DSTBL3.WeightedTree.LowerComplete.lower_complete_template` | `ThmBC.Lower.Complete` |
| Theorem C: some separable Banach lattice has Π¹₁-complete `Y^{↑∞}` | `DSTBL3.WeightedTree.UpperComplete.upper_complete_template` | `ThmBC.Upper.Upper` |

For Theorem A, the development constructs the coordinate projections, proves
the auxiliary `ρ`-norm is complete, derives the maximal inequality by the
bounded inverse theorem, and proves norm convergence and uniqueness of the
basis expansion. The paper's further conclusion that the basis is a *uniform
basis* uses Taylor's external uniform-basis theorem; that external theorem is
not formalized here.

For Theorems B and C, the development formalizes the weighted-tree spaces and
their intrinsic Banach-lattice structures, the finite-rank and separability
arguments, the lower and upper tree reductions, the relevant coanalyticity
statements, and the transfer of Π¹₁-completeness from well-founded trees.

## Repository layout

| Path | Purpose |
|---|---|
| `DSTBL3.lean` | unified import of the A/B/C developments |
| `TheoremA/Lean_Code/` | implementation of Theorem A and `order-sigma` |
| `ThmBC/BasicPi11.lean` | descriptive-set-theoretic definitions and Π¹₁-completeness of well-founded trees |
| `ThmBC/Tree/` | weighted-tree construction, intrinsic spaces, density, and fattening |
| `ThmBC/Lower/` | lower/decreasing construction and Theorem B |
| `ThmBC/Upper/` | upper/increasing construction and Theorem C |
| `TheoremA/Showcase_ThmA.lean` | frozen Theorem A specification with one intentional `sorry` |
| `ThmBC/Showcase_ThmB.lean` | frozen Theorem B specification with one intentional `sorry` |
| `ThmBC/Showcase_ThmC.lean` | frozen Theorem C specification with one intentional `sorry` |

The three showcase specifications are deliberately excluded from the Lake
library globs. They retain exactly the requested three `sorry`s. The proved
counterpart of the A showcase is `TheoremA/Showcase_WithProofs_ThmA.lean`.

Detailed traceability and axiom information is in:

- `TheoremA/README.md`
- `TheoremA/Lean_Code/AXIOM_STATUS.md`
- `ThmBC/Blueprint.md`
- `ThmBC/AXIOM_STATUS.md`

## Dependencies

The root project pins Lean and Mathlib `v4.34.1`. BanLat is not vendored or a
Git submodule: Lake fetches the official
[`davidmunozlahoz/banlat`](https://github.com/davidmunozlahoz/banlat)
repository into the ignored `.lake/packages/banLat` directory. For reproducible
builds it is pinned to commit
`a190b2011f720742badca9baaa1bd4ab93f2d438` in `lakefile.toml` and
`lake-manifest.json`.

That BanLat revision declares Lean/mathlib `v4.32.1`, but the unified dependency
graph resolves Mathlib to this root project's `v4.34.1`. The imported BanLat
modules compile successfully with 4.34.1. They currently emit upstream
deprecation/style warnings on that newer version.

## Build and verification

Install Lean through `elan`, then run from the repository root:

```bash
lake update
lake exe cache get
lake build DSTBL3 Lean_Code dstbl3 -q --log-level=info
```

The default build is equivalent to building the two libraries:

```bash
lake build
```

To check the three frozen showcase specifications separately:

```bash
lake env lean TheoremA/Showcase_ThmA.lean
lake env lean ThmBC/Showcase_ThmB.lean
lake env lean ThmBC/Showcase_ThmC.lean
```

Each command is expected to report its single intentional "declaration uses
`sorry`" warning.

## License

This project is licensed under the [Apache License 2.0](LICENSE).
