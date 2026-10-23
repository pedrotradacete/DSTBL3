# Theorem A — Lean 4 / Mathlib verification

This directory contains the Theorem A part of the unified `DSTBL3` project.
It verifies the maximal inequality for σ-order bases and order bases, and the
resulting Schauder-basis conclusions.

The principal declarations are:

- `ThmA.theoremA_sigma_order_form`
- `ThmA.theoremA_order_form`
- `ThmA.theoremA_sigma_order_schauder`
- `ThmA.theoremA_order_schauder`

The proved implementation contains no `sorry` and introduces no project-specific axioms. `#print
axioms` reports only Lean/Mathlib's standard `propext`, `Classical.choice`, and
`Quot.sound`.

## Layout

| Path | Contents |
|---|---|
| `Showcase_ThmA.lean` | frozen specification, retaining its intentional `sorry` |
| `Showcase_WithProofs_ThmA.lean` | the same target statement proved from `Lean_Code` |
| `Lean_Code/ThmA/OrderSigma.lean` | order convergence versus σ-order convergence and basis conversion |
| `Lean_Code/ThmA/MaximalInequality.lean` | maximal inequalities, norm convergence, uniqueness, and Schauder conclusions |
| `Lean_Code/ThmA.lean` | re-export of the complete development |

The older blueprint and findings files are retained as historical proof notes.

## Building

Theorem A is no longer a separate Lake project. From the repository root:

```bash
lake exe cache get
lake build Lean_Code
```

The root project pins Lean and Mathlib `v4.34.1`. BanLat is an external Lake
dependency, pinned to a commit from
[`davidmunozlahoz/banlat`](https://github.com/davidmunozlahoz/banlat); Lake
installs it under `.lake/packages/banLat` rather than inside this repository.
The exact BanLat revision is
`a190b2011f720742badca9baaa1bd4ab93f2d438`.
