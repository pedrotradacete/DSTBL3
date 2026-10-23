# Historical findings — Lean-verifying "Theorem A (σ-order form)"

This document records the pre-implementation review. The identified work has
since been implemented. For current results, dependency versions, and axiom
status, see `TheoremA/README.md` and `Lean_Code/AXIOM_STATUS.md`.

The active repository uses Lean/Mathlib `v4.34.1`. The historical checks below
used a `v4.31.0-rc2` Mathlib checkout and are retained to explain the original
design decisions. `Showcase_ThmA.lean` remains an unchanged specification with
its one intentional `sorry`.

---

## TL;DR verdict

| Question | Answer |
|---|---|
| Is the TEX a fully self-contained proof? | **Yes.** Every step is proved or reduces to a standard theorem (open-mapping / finite-dim / series), with no logical gaps found. |
| Is it split in a Lean-friendly way? | **Mostly yes.** The Def → Lemma 1 → Lemma 2 → Lemma 3 → Prop 4 → final structure maps almost 1:1 onto Lean lemmas. Two implicit constructions (coordinate/projection maps; the auxiliary norm as a *second* `NormedAddCommGroup` on `X`) are not called out in the TEX and must be added. |
| Does it only use Mathlib? | **Almost entirely yes.** Every analytic ingredient is present in Mathlib (verified below). **One genuine gap:** `\|α • x\| = \|α\| • \|x\|` for a *non-linear* vector lattice is **not** in Mathlib; it must be derived (~15–30 lines). |
| "No additional infrastructure"? | **Not fully achievable.** You need (a) the `abs_smul` derivation above, and (b) the standard-but-nontrivial packaging of `ρ` as a type-synonym normed space. Neither is *general reusable theory*; both are localized to this proof. Everything else is off-the-shelf Mathlib. |

**Bottom line:** formalizable with current Mathlib, no new *theory* required, but it is a
**substantial** effort (rough order 800–1500 lines) whose cost is concentrated in
Proposition 4 and the `ρ`-norm packaging — not in missing Mathlib lemmas.

---

## 1. The statement matches the TEX faithfully

`Showcase_ThmA.lean` encodes a **Banach lattice** as the unbundled bundle
```
[NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
[NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]
```
This is exactly Mathlib's normed-lattice setting (see §2) plus a real module with
monotone positive scalars plus completeness — a faithful "Banach lattice".

- `DownToZero z` ⇔ `z_m ↓ 0` (positive, decreasing, only common lower bound is 0). Matches TEX Definitions.
- `SigmaOrderTendsto x x0` ⇔ `x_n --σo--> x0` (`∀ m, ∃ n0, ∀ n ≥ n0, |x n - x0| ≤ z m` = `∀ m ∀^∞ n`). Matches.
- `IsSigmaOrderBasis e` ⇔ σ-order basis (`∃!` scalar sequence whose partial sums σo-converge). Matches.
- Goal: `∃ C, ∀ N ≥ 1, ∀ a, ‖ ⨆_{m<N} |∑_{k≤m} a k • e k| ‖ ≤ C * ‖∑_{k<N} a k • e k‖`.
  `(range N).sup'` = finite lattice sup ⋁; `range (m+1)` = first `m+1` terms. Matches TEX
  `‖ ⋁_{m=1}^N |∑_{k=1}^m a_k e_k| ‖ ≤ C ‖∑_{k=1}^N a_k e_k‖` (0-indexed vs 1-indexed, consistent).

**Note — `hspan` is unused.** The hypothesis
`(Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤` encodes "X = [e_n]", but the
mathematical proof never uses it: `IsSigmaOrderBasis e` already quantifies over *every*
`x : X`. It can be ignored in the proof (may trigger an unused-variable linter warning; harmless).

---

## 2. The linchpin: the typeclass bundle already unlocks the normed-lattice API

File `Analysis/Normed/Order/Lattice.lean`. Everything here is stated in exactly the
Showcase's unbundled form `[NormedAddCommGroup α] [Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α]`,
so it applies to `X` directly:

- `HasSolidNorm.solid` / `norm_le_norm_of_abs_le_abs : |a| ≤ |b| → ‖a‖ ≤ ‖b‖` (:52) — "monotonicity of the lattice norm", used pervasively.
- `norm_abs_eq_norm : ‖|a|‖ = ‖a‖` (:90).
- `continuous_posPart`, `continuous_negPart` (:173, :176); `norm_abs_sub_abs` (Birkhoff, :153).
- `isClosed_nonneg : IsClosed {x | 0 ≤ x}` (:178) — the positive cone is norm-closed.
- **`HasSolidNorm.orderClosedTopology : OrderClosedTopology X`** (:193) — *the* tool for "pass an
  order inequality to the norm limit" (Lemma 1(4); Prop 4 eqs (5),(6),(10)). Gives `isClosed_le`,
  `isClosed_Icc`, and `le_of_tendsto'`/`ge_of_tendsto'`.
- `HasSolidNorm.continuousInf/continuousSup`, `TopologicalLattice` (:130,:142,:150).

`Continuous (abs : X → X)` is not named here but is a 1-liner from `continuous_posPart`+`continuous_negPart`
(`|a| = a⁺ + a⁻`) or from `continuousSup` (`|a| = a ⊔ -a`).

---

## 3. Dependency map — every proof step vs. Mathlib (all verified present)

### Lattice-ordered-group `abs` / `posPart` algebra (for the many `(h−z)⁺`, triangle, `|·|` manipulations)
`Algebra/Order/Group/Unbundled/Abs.lean` **`section Lattice` (`variable [Lattice α]`, `[AddCommGroup]`, `[AddLeftMono]`)** — holds for our *non-linear* `X` (via `to_additive`; `IsOrderedAddMonoid` supplies `AddLeftMono`):
`abs_add_le`, `le_abs_self`, `neg_abs_le`, `abs_le`, `abs_nonneg`, `abs_neg`, `abs_abs`, `abs_sub_comm`.
`Algebra/Order/Group/PosPart.lean`: `posPart_nonneg`, **`posPart_eq_zero : a⁺ = 0 ↔ a ≤ 0`** (drives `(h−z_M)⁺ = 0 ⟹ h ≤ z_M`).

### Lemma 1 (5 parts) — σ-order convergence basics
- (1) add/scalar compat: `add_le_add` (from `IsOrderedAddMonoid`), `le_inf`, `posPart_eq_zero`, `abs_add_le`; scalar case needs **`abs_smul` (see §4 GAP)** + `PosSMulMono` monotonicity.
- (2) order bounded: finite sup of the exceptional terms — `Finset.sup'`/`le_sup'`.
- (3) `|x_n|≤u ⟹ |x|≤u`: `abs_add_le`, `posPart_eq_zero`, `DownToZero`.
- (4) norm-limit of order interval: **`OrderClosedTopology`** + `le_of_tendsto'` + `continuous_abs`.
- (5) tails of a norm-convergent positive series `↓ 0`:
  `Summable.of_norm` (`Analysis/Normed/Group/InfiniteSum.lean:194`), `tsum_nonneg`,
  `tsum_eq_zero_add` (tail recursion `U_R = u_R + U_{R+1}`), tails→0 via
  `tendsto_sum_nat_add` / `tendsto_tsum_compl_atTop_zero`, then `solid` to kill `h`.

### Lemma 2 — linearity of `e_n^#`, `P_m`; linear independence of `(e_n)`
Pure consequence of `IsSigmaOrderBasis` uniqueness + Lemma 1(1). Needs the coordinate/projection
maps to exist first (§5, construction C1).

### Lemma 3 — `ρ` is a norm and `‖x‖ ≤ ρ(x)`
`ρ(x) = sInf { ‖u‖ | u ≥ 0 ∧ ∀ m, |P_m x| ≤ u }`. Nonempty by Lemma 1(2), bdd below by 0
→ `Real` `csInf_le` / `le_csInf`. Homogeneity needs **`abs_smul` (GAP)**. `‖x‖ ≤ ρ(x)` from Lemma 1(3)+`solid`.

### Proposition 4 — completeness of `(X, ρ)`  ← **the hard core**
- absolute convergence ⟹ convergence in Banach `X`: `Summable.of_norm`, `CompleteSpace`.
- `x = lim x_R` in `‖·‖`; pass order inequalities to limit: `OrderClosedTopology`, `le_of_tendsto'`.
- the `b_j = ⋀_{R≤j}(U_R+T_R+w_j^R)` construction: finite `⊓` (`le_inf`, `inf_le_of...`), monotone in `j`, `↓ 0`.
- **`y_m = P_m x` identification** (most intricate): `E_m = span{e_0..e_m}` closed
  (`Submodule.closed_of_finiteDimensional`, `Analysis/Normed/Module/FiniteDimension.lean`) so `y_m ∈ E_m`;
  truncation `Q_m` continuous (`LinearMap.continuous_of_finiteDimensional`, same file); compatibility
  `Q_m y_{m+1} = y_m` + `∃!` uniqueness ⟹ `y_m = P_m x`. Uses Lemma 2 (linear independence) for coordinates on `E_m`.

### Final maximal inequality
- **Second normed structure on `X`** (§5, construction C2) + bounded-inverse theorem
  `ContinuousLinearEquiv.ofBijective` (`Analysis/Normed/Operator/Banach.lean:431`; needs
  `[CompleteSpace E]` on the source `(X,ρ)` = Prop 4, `ker = ⊥`, `range = ⊤` — both trivial for `id`).
  Continuity of `id : (X,ρ) →L X` from `‖x‖ ≤ ρ(x)` via `LinearMap.mkContinuous` (bound 1).
  `C := ‖(ofBijective …).symm‖`, and `ρ(x) ≤ C‖x‖` from `le_opNorm`.
- `ρ(x) = ‖v‖` with `v = ⋁_{m<N}|∑_{k≤m}|`: `v` is the least order bound of `{|P_m x|}`
  (`Finset.le_sup'`, `Finset.sup'_le`) so `v` is `sInf`-admissible and minimal → `solid` gives `‖v‖ = ρ(x)`.
- eventually-constant partial sums σo-converge with regulator `z ≡ 0` (`DownToZero 0` holds:
  `h ≥ 0 ∧ h ≤ 0 ⟹ h = 0` by antisymmetry) → uniqueness pins the coordinates; no `hspan` needed.

Other confirmed API: `NormedAddCommGroup.ofCore` (build `ρ`-norm), `AddGroupNorm.toNormedAddCommGroup`,
`LinearMap.mkContinuous`, `le_opNorm`, `nonempty_range_iff`, `isClosed_Icc`, `IsClosed.mem_of_tendsto`.

---

## 4. The ONE real Mathlib gap: `abs_smul` for a non-linear vector lattice

Needed as `|α • x| = |α| • |x|` (equivalently `α • (a ⊔ b) = α•a ⊔ α•b` for `0 ≤ α`) in:
Lemma 1(1) scalar case, and Lemma 3 homogeneity.

**Why it's missing:**
- `abs_smul` in `Algebra/Order/Module/Basic.lean:42` **requires `[LinearOrder M]`** — a Banach lattice is
  *not* linearly ordered, so it does not apply.
- `smul_max_of_nonneg` / `smul_min_of_nonneg` (`Algebra/Order/Module/Defs.lean:479–483`) are also inside
  `section LinearOrder` (they use `Monotone.map_max`, which needs a total order). Not usable.
- For general (semi)lattices Mathlib only has the **one-sided** `smul_inf_le`
  (`Algebra/Order/Group/Action.lean:35`): `m • (a ⊓ b) ≤ m•a ⊓ m•b` (and dual). No equality.
- `Analysis/Normed/Order/Lattice.lean` contains **no** `•` lemmas at all — Mathlib's normed-lattice
  theory says nothing about scalar multiplication vs. the lattice.
- There is no Riesz-space / vector-lattice scalar theory (`Analysis/Order/` does not exist; only the
  additive `Algebra/Order/Group/Lattice.lean`).

**How to close it (localized, ~15–30 lines, uses only existing lemmas — not "theory"):**
From `PosSMulMono ℝ X`: for `0 ≤ c`, `c•a ⊔ c•b ≤ c•(a⊔b)` is the one-sided direction
(`smul_le_smul_of_nonneg_left`/`monotone_smul_left_of_nonneg`); the reverse for `c > 0` follows by
applying the same to `c⁻¹` and rescaling (field inverse). Hence `c•(a⊔b) = c•a ⊔ c•b` for `0 ≤ c`.
Then `|c•x| = (c•x) ⊔ (c•(-x)) = c•(x ⊔ -x) = c•|x| = |c|•|x|` for `c ≥ 0`, and reduce `c < 0`
via `c•x = -((-c)•x)`, `abs_neg`. This is the only genuinely new lemma to prove.

---

## 5. Lean-specific constructions the TEX leaves implicit

**C1 — coordinate functionals and projections.** `e_n^#` and `P_m` are not primitive; extract them
by `Classical.choose` on the `∃!` in `IsSigmaOrderBasis`:
`coord x := Classical.choose (hbasis x)`, `P m x := ∑ k ∈ range (m+1), coord x k • e k`.
Linearity (Lemma 2) then follows from uniqueness. This slots between the definitions and Lemma 3.

**C2 — the auxiliary norm as a *second* normed space (unavoidable for the open-mapping step).**
Lean cannot put two `NormedAddCommGroup` instances on one type. Introduce a type synonym
`def Xρ := X` carrying `AddCommGroup`/`Module ℝ` (transported), a `Norm` from `ρ`, then
`NormedAddCommGroup Xρ` via `AddGroupNorm.toNormedAddCommGroup` (or `NormedAddCommGroup.ofCore`),
`NormedSpace ℝ Xρ` via `norm_smul_le` (= homogeneity), and `CompleteSpace Xρ` = Prop 4. The maximal
inequality is then `ContinuousLinearEquiv.ofBijective (id : Xρ →L[ℝ] X) …`. This is standard Mathlib
plumbing but is real work and is the second reason "zero infrastructure" isn't literally attainable.

---

## 6. Suggested Lean decomposition (each `→` a separate lemma/def)

```
-- reusable micro-lemma (the §4 gap)
abs_smul_vectorLattice : ∀ (c : ℝ) (x : X), |c • x| = |c| • |x|

-- Lemma 1
downToZero_zero            : DownToZero (0 : ℕ → X)          -- regulator z ≡ 0
sigmaOrderTendsto_add / _smul                                -- L1(1)
SigmaOrderTendsto.orderBounded                               -- L1(2)
SigmaOrderTendsto.abs_le_of_abs_le                           -- L1(3)
abs_le_of_tendsto (norm-limit of order interval)            -- L1(4)
downToZero_tsum_tail : DownToZero (fun R => ∑' r, u (r+R))   -- L1(5)

-- coordinates / projections (C1) + Lemma 2
coord, proj (P);  proj_add, proj_smul;  linearIndependent_e

-- Lemma 3
rho; rho_nonempty_bddBelow; rho_add_le; rho_smul; norm_le_rho; rho_eq_zero_iff

-- Proposition 4  (hard core)
rho_completeSpace : CompleteSpace Xρ

-- Final
theoremA_sigma_order_form   -- via ContinuousLinearEquiv.ofBijective + rho = ‖v‖
```

## 7. Difficulty / risk ranking

1. **Proposition 4**, esp. `y_m = P_m x` (finite-dim truncation + `∃!`). Highest risk & length.
2. **C2** type-synonym `ρ`-space packaging (fiddly instance wiring; easy to get defeq/`Module` transport wrong).
3. **Lemma 3** `sInf` `ρ`-arithmetic (ε-arguments with `csInf_le`/`le_csInf`).
4. **§4 `abs_smul`** gap — conceptually trivial, must not be forgotten (breaks L1(1) & L3 if missing).
5. Lemma 1(5) series/tail bookkeeping.
6. Lemma 1(1–4), Lemma 2, final assembly — routine given the above.

No Dedekind/order-completeness is ever required (all suprema/infima used are either **finite** lattice
ops or **norm-convergent** series), so the given typeclasses are sufficient — no extra order hypotheses needed.
