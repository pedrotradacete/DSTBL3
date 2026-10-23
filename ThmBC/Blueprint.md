# Blueprint — Lean formalization of Theorems B and C

This directory reorganizes the verified material for Theorems B and C of
`paper.tex` in the same style as the Theorem A development: a dependency-ordered
module tree, one re-export file, and an axiom/status log.

The development is part of the unified root project on Lean/Mathlib `v4.34.1`.
BanLat is consumed as an external Lake dependency from
[`davidmunozlahoz/banlat`](https://github.com/davidmunozlahoz/banlat), pinned at
commit `a190b2011f720742badca9baaa1bd4ab93f2d438`; there is no vendored BanLat
directory or submodule.

## File Split

| Paper material | Lean module | Contents |
|---|---|---|
| DST preliminaries | `ThmBC.BasicPi11` | coanalytic sets, continuous reducibility, `Pi11Complete`, transfer principle, `WF` `Π¹₁`-completeness |
| Section 5 weighted tree space | `ThmBC.Tree.Basic`, `ThmBC.Tree.Intrinsic` | nodes, weights, intrinsic normed vector lattice `V_E`, tree definitions |
| Section 5 finite-rank closure | `ThmBC.Tree.FiniteRank` | finite-rank elements, `S_E`, `Z_E`, weighted completeness/closure |
| Section 5 separability and child limits | `ThmBC.Tree.Dense` | separability of `Z_E`, `finiteRank_template`, `child_convergence_template` |
| Section 5 eventual-constancy template | `ThmBC.Tree.Eventual` | controlled finite trees, `eventually_constant_template` |
| Lemma `fattening` | `ThmBC.Tree.Tree` | pointwise node order, branches, fattening, preservation of well-foundedness |
| Section 6 setup | `ThmBC.Lower.Basic` | `d_m`, `z_m^R`, `thetaLower`, lower sequence predicates |
| Lemmas `dead-sequence`, `z-lower-in-X`, `z-lower-continuous` | `ThmBC.Lower.Continuity` | lower local properties and continuity |
| Section 6 tree reduction | `ThmBC.Lower.Reduction` | branch-cone lower bound, `lower-IF`, `dead-subtree`, `lower-WF` |
| Section 6 topology and Polish spaces | `ThmBC.Lower.Topology` | continuity of the reduction, intrinsic `Z_E` and sequence spaces |
| Section 6 descriptive-set-theoretic conclusion / Theorem B | `ThmBC.Lower.Complete` | coanalyticity, continuous reduction, `lower_complete_template` |
| Section 7 setup | `ThmBC.Upper.Basic` | `Y`, the local sequence `a_m`, pasted sequences `u_m^R`, positivity and monotonicity |
| Section 7 continuity and branch bounds | `ThmBC.Upper.Continuity` | continuity of `u_m^R` and `Phi`, branch-cone upper bounds |
| Section 7 tree reduction | `ThmBC.Upper.Reduction` | ill-founded/well-founded directions, closedness and separability of `Y` |
| Section 7 descriptive-set-theoretic conclusion / Theorem C | `ThmBC.Upper.Upper` | intrinsic Polish target, coanalyticity, reduction, `upper_complete_template` |
| Re-export | `ThmBC.ThmBC` | imports the complete B/C development |

The active Theorem B/C import chain is self-contained under `ThmBC`.

## Traceability Table

| TeX label | Lean name | Module |
|---|---|---|
| `prop:coanalytic` | specialized as `xDownarrowZeroZ_coanalytic`, `yUpwardUnboundedY_coanalytic` | `ThmBC.Lower.Complete`, `ThmBC.Upper.Upper` |
| `def:finite-rank` | `FiniteRank`, `S`, `Z` | `ThmBC.Tree.FiniteRank` |
| `lem:S-template` | `finiteRank_template`, plus `Z_isClosedBanachSubLattice`, `Z_isSeparableForWeightedNorm` | `ThmBC.Tree.Dense` |
| `lem:child-convergence-template` | `child_convergence_template` | `ThmBC.Tree.Dense` |
| `lem:eventually-constant-template` | `eventually_constant_template` | `ThmBC.Tree.Eventual` |
| `lem:fattening` | `fattening_template` | `ThmBC.Tree.Tree` |
| `lem:dead-sequence` | `dead_sequence_template` | `ThmBC.Lower.Continuity` |
| `lem:z-lower-in-X` | `z_lower_in_X_template` | `ThmBC.Lower.Continuity` |
| `lem:z-lower-continuous` | `z_lower_continuous_template`, `z_lower_sequence_continuous_template` | `ThmBC.Lower.Continuity` |
| `lem:lower-IF` | `lower_IF_template` | `ThmBC.Lower.Reduction` |
| `lem:dead-subtree` | `dead_subtree_template` | `ThmBC.Lower.Reduction` |
| `lem:lower-WF` | `lower_WF_template` | `ThmBC.Lower.Reduction` |
| `thm:lower-complete` / Theorem B | `lower_complete_template` | `ThmBC.Lower.Complete` |
| `lem:local-unbounded` | `local_unbounded_template` | `ThmBC.Upper.Basic` |
| `lem:u-upper-in-Y` | `u_upper_in_Y_template` | `ThmBC.Upper.Continuity` |
| `lem:u-upper-continuous` | `u_upper_continuous_template` | `ThmBC.Upper.Continuity` |
| `prop:upper-IF` | `upper_IF_template` | `ThmBC.Upper.Reduction` |
| `prop:upper-WF` | `upper_WF_template` | `ThmBC.Upper.Reduction` |
| `thm:upper-complete` / Theorem C | `upper_complete_template` | `ThmBC.Upper.Upper` |

## Notes

The Theorem B witness uses the paper's coefficient lattice `L₁[0,1]`, realized
as `MeasureTheory.Lp ℝ 1 volume` on Mathlib's unit interval. The final B and C
witnesses package genuine intrinsic separable Banach lattices, rather than only
predicates describing ambient subspaces.
