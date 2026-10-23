# AXIOM_STATUS — Theorem A formalization

## Current status

- Lean and Mathlib: `v4.34.1`, configured by the repository root.
- Theorem A is part of the root `Lean_Code` library; there is no nested Lake
  project.
- BanLat is the external Lake dependency
  [`davidmunozlahoz/banlat`](https://github.com/davidmunozlahoz/banlat), pinned
  at commit `a190b2011f720742badca9baaa1bd4ab93f2d438`; it is not stored in this
  repository.
- No implementation module under `Lean_Code` contains `sorry`, `admit`, or a
  custom `axiom` declaration.
- `Showcase_ThmA.lean` remains a frozen specification with one intentional
  `sorry`; `Showcase_WithProofs_ThmA.lean` proves that statement without one.

## Main verified results

| Paper result | Lean declaration | Module |
|---|---|---|
| order convergence is equivalent to σ-order convergence in the separable setting | `ThmA.orderConvergesTo_iff_sigmaOrderTendsto` | `ThmA.OrderSigma` |
| σ-order maximal inequality | `ThmA.theoremA_sigma_order_form` | `ThmA.MaximalInequality` |
| order-basis maximal inequality | `ThmA.theoremA_order_form` | `ThmA.MaximalInequality` |
| σ-order basis is a Schauder basis | `ThmA.theoremA_sigma_order_schauder` | `ThmA.MaximalInequality` |
| order basis is a Schauder basis | `ThmA.theoremA_order_schauder` | `ThmA.MaximalInequality` |

The paper's final uniform-basis corollary also invokes Taylor's external
uniform-basis theorem. The Lean development proves the new maximal inequality
and Schauder-basis input, but does not formalize that external theorem.

## Axiom audit

Running `#print axioms` on all four endpoint declarations above reports:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard logical principles used throughout Mathlib, not assumptions
specific to this project.

## Verification

From the repository root:

```bash
lake exe cache get
lake build Lean_Code -q --log-level=info
```

The historical scaffold/proof log was retired when the two Lake projects were
unified; every item that had appeared in its temporary axiom ledger is now a
proved theorem or an implemented instance.
