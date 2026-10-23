# AXIOM_STATUS — Theorems B and C formalization

This log mirrors the status file used for Theorem A.

## Current Status

- Lean and Mathlib are pinned to `v4.34.1` by the repository root.
- BanLat is fetched as an external Lake dependency from
  [`davidmunozlahoz/banlat`](https://github.com/davidmunozlahoz/banlat), pinned
  at commit `a190b2011f720742badca9baaa1bd4ab93f2d438`.
- No `sorry` or `admit` occurs in the implementation modules imported by
  `ThmBC.ThmBC`.
- No new axioms or constants are introduced by the B/C development.
- The active local dependencies for Theorems B and C all live under
  `ThmBC`.
- `Showcase_ThmB.lean` and `Showcase_ThmC.lean` are frozen standalone
  specifications and retain one intentional `sorry` each.

## Main Verified Results

| Paper theorem | Lean theorem | Module |
|---|---|---|
| Theorem B | `DSTBL3.WeightedTree.LowerComplete.lower_complete_template` | `ThmBC.Lower.Complete` |
| Theorem C | `DSTBL3.WeightedTree.UpperComplete.upper_complete_template` | `ThmBC.Upper.Upper` |

## Verification Commands

```bash
lake exe cache get
lake build DSTBL3 -q --log-level=info
```

The project modules compile without warnings. A clean build can display
deprecation/style warnings from the pinned BanLat sources under
`.lake/packages/banLat`; those warnings are upstream and the dependency is not
patched locally.
