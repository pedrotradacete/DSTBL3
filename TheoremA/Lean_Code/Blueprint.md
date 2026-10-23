# Historical blueprint — Lean formalization of Theorem A (σ-order form)

This is the pre-implementation proof plan and is retained for historical
traceability. The current, completed development is documented in
`TheoremA/README.md` and `AXIOM_STATUS.md`; it now also contains the order-basis
case, the order/σ-order equivalence, norm convergence, and the Schauder-basis
conclusions.

The active repository toolchain is Lean/Mathlib `v4.34.1`, configured at the
repository root. Historical API names below describe the original plan and may
not match the current source verbatim.

**Frozen variable bundle (C2), verbatim from `Showcase_ThmA.lean`:**
```
variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]
```

---

## Imported facts (Section 2 — DAG leaves, already in Mathlib; never axiomatize)

| Label | Content | Mathlib names |
|---|---|---|
| `fact:solid` | `|a|≤|b| ⇒ ‖a‖≤‖b‖`; `‖|a|‖=‖a‖` | `norm_le_norm_of_abs_le_abs`, `HasSolidNorm.solid`, `norm_abs_eq_norm` |
| `fact:orderclosed` | `OrderClosedTopology X`; order ≤ passes to norm limits | `HasSolidNorm.orderClosedTopology`, `le_of_tendsto'`, `ge_of_tendsto'`, `isClosed_Icc` |
| `fact:contabs` | `x⁺`, `x⁻`, `|·|`, `⊔`, `⊓` norm-continuous | `continuous_posPart`, `continuous_negPart`, `HasSolidNorm.continuousSup`, `isClosed_nonneg` |
| `fact:absgroup` | lattice-ordered-group abs/posPart algebra (non-linear!) | `abs_add_le`, `le_abs_self`, `neg_abs_le`, `abs_le`, `abs_nonneg`, `abs_neg`, `posPart_nonneg`, `posPart_eq_zero` |
| `fact:possmul` | `0≤α, a≤b ⇒ α•a≤α•b`; `0≤α,0≤a ⇒ 0≤α•a` | `PosSMulMono`, `monotone_smul_left_of_nonneg`, `smul_le_smul_of_nonneg_left`, `smul_nonneg` |
| `fact:series` | norm-summable ⇒ converges in Banach; tails of positive series | `Summable.of_norm`, `tsum_nonneg`, `Summable.tsum_eq_zero_add`/`tsum_eq_zero_add'`, `tendsto_sum_nat_add`, `tendsto_tsum_compl_atTop_zero` |
| `fact:csinf` | real inf: `csInf_le`, `le_csInf`, `Real.sInf_nonneg` | `csInf_le`, `le_csInf`, `Real.sInf_nonneg` |
| `fact:finset` | finite `⊔`/`⊓` are lub/glb, monotone | `Finset.le_sup'`, `Finset.sup'_le`, `Finset.le_inf'`, `Finset.inf'_le`, `Finset.inf'_mono` |
| `fact:findim` | fin-dim subspace closed; lin map from fin-dim continuous; basis of span | `Submodule.closed_of_finiteDimensional`, `LinearMap.continuous_of_finiteDimensional`, `Module.Basis.span`, `LinearIndependent` |
| `fact:banach` | norm-core → NormedAddCommGroup; bounded inverse theorem | `NormedAddCommGroup.ofCore`, `AddGroupNorm.toNormedAddCommGroup`, `LinearMap.mkContinuous`, `ContinuousLinearEquiv.ofBijective`, `ContinuousLinearMap.le_opNorm` |
| `fact:completecrit` | complete ⇐ every norm-summable series converges | `Metric.complete_of_cauchySeq_tendsto` / normed-group series criterion (e.g. `NormedAddCommGroup.completeSpace_of_summable_imp_hasSum`-style) |

---

## Labeled blocks (in dependency / file order)

### File `ThmA/Prelim/AbsSmul.lean`  — the ONLY new theory (Remark rem:gap; prove for real, C6)

- **`lem:smul_sup_nonneg`** `[Lean: smul_sup_of_nonneg]`
  For `0 ≤ α` (α:ℝ) and `a b : X`: `α • (a ⊔ b) = (α • a) ⊔ (α • b)`.
  Uses: `fact:possmul`.
  *Proof:* one-sided `(d•p)⊔(d•q) ≤ d•(p⊔q)` for `0≤d` (monotonicity); gives `≥`. For `≤`:
  α=0 trivial; α>0 apply one-sided to `α⁻¹` at `p=α•a,q=α•b`, LHS `= a⊔b`, act by α.

- **`lem:abs_smul`** `[Lean: abs_smul_vectorLattice]`
  For all `α:ℝ`, `x:X`: `|α • x| = |α| • |x|`.
  Uses: `lem:smul_sup_nonneg`, `fact:absgroup`.
  *Proof:* α≥0: `|α•x| = (α•x)⊔(α•(-x)) = α•(x⊔-x) = α•|x| = |α|•|x|`. α≤0: `d=-α≥0`,
  `α•x = -(d•x)`, `|α•x| = |d•x| = d•|x| = |α|•|x|` via `abs_neg`.

### File `ThmA/Defs.lean`  — frozen defs VERBATIM from Showcase (C2) + coordinate construction

- **`def:downto`** `[Lean: DownToZero]` — `z_m ↓ 0` (VERBATIM). Uses: —.
  `(∀m, 0≤z m) ∧ (∀m, z (m+1)≤z m) ∧ ∀h, 0≤h → (∀m, h≤z m) → h=0`.
- **`def:sigo`** `[Lean: SigmaOrderTendsto]` (VERBATIM). Uses: `def:downto`.
  `∃ z, DownToZero z ∧ ∀m, ∃n0, ∀n≥n0, |x n - x0| ≤ z m`.
- **`def:basis`** `[Lean: IsSigmaOrderBasis]` (VERBATIM). Uses: `def:sigo`.
  `∀x, ∃! a:ℕ→ℝ, SigmaOrderTendsto (fun m => ∑ k∈range (m+1), a k • e k) x`.
- **`con:coord`** `[Lean: coord, proj]` — NEW def. Uses: `def:basis`.
  Given `hbasis : IsSigmaOrderBasis e`: `coord x := Classical.choose (hbasis x)` (the unique
  `aˣ`); `e_k#(x) = coord x k`; `proj m x := ∑ k∈range (m+1), coord x k • e k` (= `s_m(aˣ)`).

### File `ThmA/Regulators.lean`  — regulator calculus (needs Defs only)

- **`lem:reg_zero`** `[Lean: downToZero_zero]` — `DownToZero (0:ℕ→X)`. Uses: `def:downto`.
  *Proof:* (i),(ii) trivial; (iii) `0≤h≤0 ⇒ h=0` antisymmetry.
- **`lem:reg_add`** `[Lean: DownToZero.add]` — `z↓0, w↓0 ⇒ (z+w)↓0`. Uses: `def:downto`, `fact:absgroup`.
  *Proof:* pos/mono termwise; (iii) fix M; for m≥M, `h≤z_M+w_m` so `(h-z_M)⁺≤w_m`; for m<M use
  `w_m≥w_M≥(h-z_M)⁺`; so `(h-z_M)⁺≤w_m ∀m ⇒ =0` (`w↓0`) ⇒ `h≤z_M ∀M ⇒ h=0` (`z↓0`). (`posPart_eq_zero`)
- **`lem:reg_smul`** `[Lean: DownToZero.smul]` — `z↓0 ⇒ (|α|•z_m)↓0`. Uses: `def:downto`, `lem:reg_zero`, `fact:possmul`.
  *Proof:* pos/mono via `fact:possmul` (`|α|≥0`); α=0 → `reg_zero`; α≠0: `0≤h≤|α|•z_m`, act by
  `|α|⁻¹≥0` → `0≤|α|⁻¹•h≤z_m ⇒ |α|⁻¹•h=0 ⇒ h=0`.
- **`lem:diagonal`** `[Lean: sigmaOrderTendsto_of_diagonal]`. Uses: `def:downto`, `def:sigo`, `lem:reg_add`, `fact:absgroup`, `fact:finset`.
  Given `c↓0` and, for each `R`, `w^R↓0`, with `∀R j, ∀^∞m, |y_m - x| ≤ c_R + w^R_j`. Then `y_m ⟶σo x`.
  *Proof:* `b_j = ⋀_{R=0}^{j}(c_R+w^R_j)`. pos/mono via `fact:finset`+`w^R` decreasing. Bound: for
  m past max of finitely many thresholds, `|y_m-x|≤b_j` (glb). `b↓0`: `0≤h≤b_j∀j` ⇒ fix R, for j≥R
  `b_j≤c_R+w^R_j` so `(h-c_R)⁺≤w^R_j` ⇒ (mono) ∀j ⇒ `=0` ⇒ `h≤c_R ∀R ⇒ h=0`.

### File `ThmA/SigmaOrder.lean`  — Lemma 1 refactored (uses AbsSmul, Regulators)

- **`lem:so_eventuallyEq`** `[Lean: sigmaOrderTendsto_of_eventuallyEq]` — `(∀^∞n, x_n=x0) ⇒ x_n⟶σo x0`. Uses: `def:sigo`, `lem:reg_zero`.
- **`lem:so_add`** `[Lean: SigmaOrderTendsto.add]` — `x_n⟶σo x, y_n⟶σo y ⇒ x_n+y_n⟶σo x+y`. Uses: `def:sigo`, `lem:reg_add`, `fact:absgroup`. (`abs_add_le`)
- **`lem:so_smul`** `[Lean: SigmaOrderTendsto.smul]` — `x_n⟶σo x ⇒ α•x_n⟶σo α•x`. Uses: `def:sigo`, `lem:reg_smul`, `lem:abs_smul`, `fact:possmul`.
- **`lem:so_bounded`** `[Lean: SigmaOrderTendsto.orderBounded]` — `x_n⟶σo x ⇒ ∃u≥0, ∀n, |x_n|≤u`. Uses: `def:sigo`, `fact:absgroup`, `fact:finset`.
  *Proof:* m=0 gives n0 with `|x_n|≤|x|+z_0` (n≥n0); `u=(⋁_{n<n0}|x_n|)⊔(|x|+z_0)`.
- **`lem:so_abs_le`** `[Lean: SigmaOrderTendsto.abs_le]` — `x_n⟶σo x, u≥0, ∀n|x_n|≤u ⇒ |x|≤u`. Uses: `def:sigo`, `fact:absgroup`.
  *Proof:* per m pick large n: `|x|≤|x_n|+|x_n-x|≤u+z_m` ⇒ `(|x|-u)⁺≤z_m ∀m ⇒ =0`.
- **`lem:norm_limit_abs_le`** `[Lean: abs_le_of_tendsto]` — `x_i→x in norm, ∀i|x_i|≤u ⇒ |x|≤u`. Uses: `fact:orderclosed`, `fact:absgroup`.
  *Proof:* `|x_i|≤u ⇔ -u≤x_i≤u`; half-spaces closed; pass to limit. (`abs_le`, `le_of_tendsto'`/`ge_of_tendsto'`)
- **`lem:reg_tail`** `[Lean: downToZero_tsum_tail]` — `u_r≥0, ∑‖u_r‖<∞, U_R=∑_{r≥R}u_r ⇒ (U_R)↓0`. Uses: `def:downto`, `fact:series`, `fact:solid`.
  *Proof:* converges; `U_R≥0` (`tsum_nonneg`); `U_R=u_R+U_{R+1}≥U_{R+1}`; `‖U_R‖→0`; `0≤h≤U_R∀R ⇒ ‖h‖≤‖U_R‖→0 ⇒ h=0`.

### File `ThmA/Coordinates.lean`  — Lemma 2 refactored

- **`lem:proj_sotends`** `[Lean: proj_sigmaOrderTendsto]` — `∀x, proj m x ⟶σo x`. Uses: `con:coord`, `def:basis`. (`Classical.choose_spec`)
- **`lem:coord_unique`** `[Lean: coord_unique]` — `s_m(a)⟶σo x ⇒ a = coord x`. Uses: `con:coord`, `def:basis`. (`ExistsUnique.unique`)
- **`lem:coord_add`** `[Lean: coord_add]` — `coord (x+y) k = coord x k + coord y k`. Uses: `lem:proj_sotends`, `lem:so_add`, `lem:coord_unique`.
- **`lem:coord_smul`** `[Lean: coord_smul]` — `coord (α•x) k = α * coord x k`. Uses: `lem:proj_sotends`, `lem:so_smul`, `lem:coord_unique`.
- **`lem:proj_linear`** `[Lean: proj_add, proj_smul]` — `proj m (x+y)=proj m x+proj m y`; `proj m (α•x)=α•proj m x`. Uses: `lem:coord_add`, `lem:coord_smul`.
- **`lem:e_indep`** `[Lean: e_linearIndependent]` — `(e_n)` linearly independent. Uses: `con:coord`, `lem:so_eventuallyEq`, `lem:coord_unique`.
  *Proof:* `∑_{k≤N} a_k e_k=0`; extend `â` by 0: `s_m(â)=0∀m≥N ⇒ ⟶σo 0`; 0-seq also ⟶σo 0; uniqueness ⇒ `â=0`.

### File `ThmA/AuxNorm.lean`  — Lemma 3 + second normed structure (type synonym)

- **`con:rho`** `[Lean: rho]` — `A(x)={u≥0 : ∀m, |proj m x|≤u}`, `rho x = sInf {‖u‖ : u∈A(x)}`. Uses: `con:coord`.
- **`lem:rho_wd`** `[Lean: rho_admissible_nonempty]` — `A(x)≠∅`; `rho x` well-defined ≥0. Uses: `con:rho`, `lem:proj_sotends`, `lem:so_bounded`, `fact:csinf`.
- **`lem:norm_le_rho`** `[Lean: norm_le_rho]` — `‖x‖ ≤ rho x`. Uses: `con:rho`, `lem:proj_sotends`, `lem:so_abs_le`, `fact:solid`, `fact:csinf`.
- **`lem:rho_approx`** `[Lean: rho_approx]` — `∀ε>0, ∃u∈A(x), ‖u‖≤rho x+ε`. Uses: `con:rho`, `lem:rho_wd`, `fact:csinf`.
- **`lem:rho_smul`** `[Lean: rho_smul]` — `rho (α•x) = |α| * rho x`. Uses: `con:rho`, `lem:proj_linear`, `lem:abs_smul`, `fact:possmul`.
  *Proof:* α=0 easy; α≠0: `u↦|α|•u` bijects `A(x)→A(α•x)`, `‖|α|•u‖=|α|‖u‖`; take inf.
- **`lem:rho_add`** `[Lean: rho_add_le]` — `rho (x+y) ≤ rho x + rho y`. Uses: `con:rho`, `lem:proj_linear`, `lem:rho_approx`, `fact:absgroup`, `fact:csinf`.
  *Proof:* pick u∈A(x),v∈A(y) near inf; `u+v∈A(x+y)` (proj linear + `abs_add_le`); `rho(x+y)≤‖u+v‖≤‖u‖+‖v‖`.
- **`lem:rho_zero`** `[Lean: rho_eq_zero_iff]` — `rho x = 0 ↔ x = 0`. Uses: `con:rho`, `lem:norm_le_rho`.
- **`con:Xrho`** `[Lean: Xrho + instances]` — type synonym `Xρ := X` with transported `AddCommGroup`/`Module ℝ`,
  `Norm` from `rho`, `NormedAddCommGroup` (via `AddGroupNorm.toNormedAddCommGroup`), `NormedSpace ℝ`.
  `ι : Xρ → X` set-theoretic identity, linear. Uses: `lem:rho_smul`, `lem:rho_add`, `lem:rho_zero`, `fact:banach`.

### File `ThmA/Complete.lean`  — Proposition 4 (heaviest)

- **`lem:tower_eq_proj`** `[Lean: proj_of_compatible_tower]`. Uses: `lem:e_indep`, `lem:coord_unique`, `fact:findim`.
  `y_m∈E_m=span{e_0..e_m}`, `Q_m y_{m+1}=y_m` (truncation), `y_m⟶σo x` ⇒ `y_m = proj m x`.
  *Proof:* lin indep ⇒ unique coords `y_m=∑_{k≤m}c^{(m)}_k e_k`; (ii) ⇒ `c^{(m+1)}_k=c^{(m)}_k` (k≤m);
  `a_k:=c^{(k)}_k` ⇒ `y_m=s_m(a)`; (iii)+`coord_unique` ⇒ `a=aˣ` ⇒ `y_m=proj m x`.
- **`lem:rho_series`** `[Lean: rho_summable_of_rho_summable]`. Uses: `con:rho`, `lem:rho_approx`, `lem:norm_le_rho`, `lem:reg_tail`, `lem:reg_add`, `lem:proj_sotends`, `lem:proj_linear`, `lem:norm_limit_abs_le`, `lem:diagonal`, `lem:tower_eq_proj`, `fact:series`, `fact:findim`.
  `∑_r rho(v_r)<∞ ⇒ x_R=∑_{r<R}v_r ρ-converges: ∃x, rho(x-x_R)→0`. 6 steps:
  1. `u_r∈A(v_r)`, `‖u_r‖≤rho(v_r)+2^{-r}` ⇒ `∑‖u_r‖<∞`, `∑‖v_r‖<∞`; `U_R=∑_{r≥R}u_r`, `T_R=∑_{r≥R}|v_r|`; `reg_tail` ⇒ `U_R↓0`, `T_R↓0`.
  2. `x=∑v_r` (Banach), `x_R→x`; `|x_S-x_R|≤T_R` ⇒ (`norm_limit_abs_le`) `|x-x_R|≤T_R`.
  3. fix m: `|P_m x_S - P_m x_R|≤U_R` ⇒ `(P_m x_R)_R` norm-Cauchy; `y_m=lim_R P_m x_R`; `|y_m-P_m x_R|≤U_R`.
  4. fix R: `P_m x_R⟶σo x_R` (reg `w^R`); `|y_m-x|≤U_R+T_R+w^R_j`; `c_R=U_R+T_R↓0` (`reg_add`); `diagonal` ⇒ `y_m⟶σo x`.
  5. `P_m x_R∈E_m` closed ⇒ `y_m∈E_m`; `Q_m` continuous, `Q_m(P_{m+1}x_R)=P_m x_R` ⇒ `Q_m y_{m+1}=y_m`; `tower_eq_proj` ⇒ `y_m=P_m x`.
  6. `|P_m(x-x_R)|=|y_m-P_m x_R|≤U_R` ⇒ `U_R∈A(x-x_R)` ⇒ `rho(x-x_R)≤‖U_R‖→0`.
- **`prop:rho_complete`** `[Lean: instCompleteSpace_Xrho]` — `Xρ` is Banach. Uses: `con:Xrho`, `lem:rho_series`, `fact:completecrit`.

### File `ThmA/MaximalInequality.lean`  — endgame (final theorem VERBATIM from Showcase)

- **`lem:proj_finite`** `[Lean: proj_of_finite]`. Uses: `con:coord`, `lem:so_eventuallyEq`, `lem:coord_unique`.
  `N≥1`, `x=∑_{k<N}a_k e_k`, `â_k=a_k (k<N) else 0`. Then `coord x=â`, `proj m x=∑_{k≤min(m,N-1)}a_k e_k`;
  `proj m x=s_m(a)` (m≤N-1), `=x` (m≥N-1).
- **`lem:rho_eq_sup`** `[Lean: rho_eq_norm_sup]`. Uses: `con:rho`, `lem:proj_finite`, `fact:finset`, `fact:solid`, `fact:csinf`.
  With `v=(range N).sup' _ (fun m => |∑_{k∈range(m+1)}a_k•e_k|)`: `rho x = ‖v‖`.
  *Proof:* `{|proj m x|:m} = {|s_m(a)|:0≤m≤N-1}`; `v` is lub ⇒ `v∈A(x)` & minimal ⇒ `rho x≤‖v‖`; `v≤u∀u∈A(x)` ⇒ `‖v‖≤rho x`.
- **`lem:const`** `[Lean: exists_const_rho_le]` — `∃C, ∀x, rho x ≤ C‖x‖`. Uses: `con:Xrho`, `prop:rho_complete`, `lem:norm_le_rho`, `fact:banach`.
  *Proof:* `ι:Xρ→X` linear, `‖ιx‖=‖x‖≤rho x` ⇒ continuous (bound 1), bijective; `Xρ` complete + `X` Banach ⇒
  bounded inverse (`ContinuousLinearEquiv.ofBijective`, ker=⊥ range=⊤); `C=‖ι⁻¹‖`, `rho x=‖ι⁻¹x‖_ρ≤C‖x‖`.
- **`thm:main`** `[Lean: theoremA_sigma_order_form]` (FIXED, VERBATIM from Showcase). Uses: `lem:const`, `lem:rho_eq_sup`.
  *Proof:* `C` from `lem:const`; `x=∑_{k<N}a_k e_k`, `v` from `lem:rho_eq_sup`: `‖v‖=rho x≤C‖x‖`. hspan unused (rem:hspan, C3).

---

## Traceability table (TeX label → Lean name → file)

| TeX label | Lean name | File |
|---|---|---|
| lem:smul_sup_nonneg | `smul_sup_of_nonneg` | ThmA/Prelim/AbsSmul.lean |
| lem:abs_smul | `abs_smul_vectorLattice` | ThmA/Prelim/AbsSmul.lean |
| def:downto | `DownToZero` | ThmA/Defs.lean |
| def:sigo | `SigmaOrderTendsto` | ThmA/Defs.lean |
| def:basis | `IsSigmaOrderBasis` | ThmA/Defs.lean |
| con:coord | `coord`, `proj` | ThmA/Defs.lean |
| lem:reg_zero | `downToZero_zero` | ThmA/Regulators.lean |
| lem:reg_add | `DownToZero.add` | ThmA/Regulators.lean |
| lem:reg_smul | `DownToZero.smul` | ThmA/Regulators.lean |
| lem:diagonal | `sigmaOrderTendsto_of_diagonal` | ThmA/Regulators.lean |
| lem:so_eventuallyEq | `sigmaOrderTendsto_of_eventuallyEq` | ThmA/SigmaOrder.lean |
| lem:so_add | `SigmaOrderTendsto.add` | ThmA/SigmaOrder.lean |
| lem:so_smul | `SigmaOrderTendsto.smul` | ThmA/SigmaOrder.lean |
| lem:so_bounded | `SigmaOrderTendsto.orderBounded` | ThmA/SigmaOrder.lean |
| lem:so_abs_le | `SigmaOrderTendsto.abs_le` | ThmA/SigmaOrder.lean |
| lem:norm_limit_abs_le | `abs_le_of_tendsto` | ThmA/SigmaOrder.lean |
| lem:reg_tail | `downToZero_tsum_tail` | ThmA/SigmaOrder.lean |
| lem:proj_sotends | `proj_sigmaOrderTendsto` | ThmA/Coordinates.lean |
| lem:coord_unique | `coord_unique` | ThmA/Coordinates.lean |
| lem:coord_add | `coord_add` | ThmA/Coordinates.lean |
| lem:coord_smul | `coord_smul` | ThmA/Coordinates.lean |
| lem:proj_linear | `proj_add`, `proj_smul` | ThmA/Coordinates.lean |
| lem:e_indep | `e_linearIndependent` | ThmA/Coordinates.lean |
| con:rho | `rho` | ThmA/AuxNorm.lean |
| lem:rho_wd | `rho_admissible_nonempty` | ThmA/AuxNorm.lean |
| lem:norm_le_rho | `norm_le_rho` | ThmA/AuxNorm.lean |
| lem:rho_approx | `rho_approx` | ThmA/AuxNorm.lean |
| lem:rho_smul | `rho_smul` | ThmA/AuxNorm.lean |
| lem:rho_add | `rho_add_le` | ThmA/AuxNorm.lean |
| lem:rho_zero | `rho_eq_zero_iff` | ThmA/AuxNorm.lean |
| con:Xrho | `Xrho` (+ instances) | ThmA/AuxNorm.lean |
| lem:tower_eq_proj | `proj_of_compatible_tower` | ThmA/Complete.lean |
| lem:rho_series | `rho_summable_of_rho_summable` | ThmA/Complete.lean |
| prop:rho_complete | `instCompleteSpace_Xrho` | ThmA/Complete.lean |
| lem:proj_finite | `proj_of_finite` | ThmA/MaximalInequality.lean |
| lem:rho_eq_sup | `rho_eq_norm_sup` | ThmA/MaximalInequality.lean |
| lem:const | `exists_const_rho_le` | ThmA/MaximalInequality.lean |
| thm:main | `theoremA_sigma_order_form` | ThmA/MaximalInequality.lean |

**Total:** 3 frozen defs + 3 constructions (coord/proj, rho, Xrho) + 30 lemmas + 1 proposition
+ 1 theorem = 38 results, on 11 imported Mathlib facts.
