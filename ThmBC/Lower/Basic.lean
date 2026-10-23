import ThmBC.BasicPi11
import ThmBC.Tree.Tree

/-!
# The lower complete coanalytic example

This file records the definitions and lemma statements from Section 6 of
`paper.tex`: the decreasing "dead" sequence, the tree-indexed pasted
sequences `z_m^R`, the reduction map `Theta`, and the statements used to prove
that `X_{\downarrow 0}` is complete coanalytic.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree
namespace LowerComplete

universe u

/-- The distinguished positive unit vector used in Section 6. In the paper this
is the constant function `1_[0,1]` in `L₁[0,1]`. -/
def UnitPositiveElement {E : Type u} [Norm E] [Zero E] [LE E] (e : E) : Prop :=
  0 ≤ e ∧ ‖e‖ = 1

/-- Coordinatewise order on the ambient weighted sequence space. -/
def CoordinatewiseLE {E : Type u} [Norm E] [LE E] (x y : V E) : Prop :=
  ∀ s : Node, x s ≤ y s

/-- Coordinatewise positivity on the ambient weighted sequence space. -/
def CoordinatewiseNonnegative {E : Type u} [Norm E] [Zero E] [LE E] (x : V E) :
    Prop :=
  ∀ s : Node, 0 ≤ x s

/-- A positive decreasing sequence in the pointwise order. -/
def IsPositiveDecreasing {E : Type u} [SeminormedAddCommGroup E] [LE E]
    (u : ℕ → V E) : Prop :=
  (∀ m : ℕ, CoordinatewiseNonnegative (u m)) ∧
    ∀ m : ℕ, CoordinatewiseLE (u (m + 1)) (u m)

/-- A non-zero positive lower bound in `Z_E` for a sequence in `V_E`. -/
def IsNonzeroPositiveLowerBoundInZ {E : Type u} [SeminormedAddCommGroup E] [LE E]
    (y : V E) (u : ℕ → V E) : Prop :=
  y ∈ Z E ∧ CoordinatewiseNonnegative y ∧ y ≠ 0 ∧
    ∀ m : ℕ, CoordinatewiseLE y (u m)

/-- The statement that a positive decreasing sequence has infimum zero in
`X = Z_E`: it has no non-zero positive lower bound in `Z_E`. -/
def HasInfimumZeroInZ {E : Type u} [SeminormedAddCommGroup E] [LE E]
    (u : ℕ → V E) : Prop :=
  ¬ ∃ y : V E, IsNonzeroPositiveLowerBoundInZ y u

/-- The set `X_{\downarrow 0}` for `X = Z_E`, represented as a predicate on
sequences in the ambient space. -/
def XDownarrowZero {E : Type u} [SeminormedAddCommGroup E] [LE E]
    (u : ℕ → V E) : Prop :=
  (∀ m : ℕ, u m ∈ Z E) ∧ IsPositiveDecreasing u ∧ HasInfimumZeroInZ u

/-- The raw Section 6 sequence `d_m`, before bundling it as an element of `V_E`.
At the root it is `e`; on the first-level subtree indexed by `n`, it is
identically `0` when `n < m` and identically `e` otherwise. -/
noncomputable def deadSequenceRaw {E : Type u} [Zero E] (e : E) (m : ℕ) :
    TreeSeq E
  | [] => e
  | n :: _ => if n < m then 0 else e

/-- Coordinate norm bound for the raw Section 6 element `d_m`: every
coordinate is either `0` or `e`. -/
theorem deadSequenceRaw_norm_le {E : Type u} [SeminormedAddCommGroup E]
    (e : E) (m : ℕ) (s : Node) :
    ‖deadSequenceRaw e m s‖ ≤ ‖e‖ := by
  cases s with
  | nil =>
      simp [deadSequenceRaw]
  | cons n rest =>
      by_cases h : n < m
      · simp [deadSequenceRaw, h]
      · simp [deadSequenceRaw, h]

/-- Weighted boundedness of the raw Section 6 sequence `d_m`, allowing it to
be bundled as an element of `V_E`. -/
theorem deadSequenceRaw_weightedBounded {E : Type u} [SeminormedAddCommGroup E]
    (e : E) (m : ℕ) :
    WeightedBounded (deadSequenceRaw e m) := by
  refine ⟨‖e‖, ?_⟩
  intro s
  calc
    weight s * ‖deadSequenceRaw e m s‖ ≤ 1 * ‖e‖ := by
      exact mul_le_mul (weight_le_one s) (deadSequenceRaw_norm_le e m s)
        (norm_nonneg _) (by norm_num)
    _ = ‖e‖ := by ring

/-- The element `d_m ∈ V_E`. -/
noncomputable def deadSequence {E : Type u} [SeminormedAddCommGroup E]
    (e : E) (m : ℕ) : V E :=
  ⟨deadSequenceRaw e m, deadSequenceRaw_weightedBounded e m⟩

/-- The paper indexes the sequence as `d₁, d₂, ...`; this zero-based Lean
sequence has `d_{m+1}` in slot `m`. -/
noncomputable def deadSequenceSeq {E : Type u} [SeminormedAddCommGroup E]
    (e : E) : ℕ → V E :=
  fun m => deadSequence e (m + 1)

/-- Follow a node through a tree. The value remains `e` until the first exit
from `R`; below that exit, the supplied sequence `d` is pasted in. -/
noncomputable def pasteAtFirstExitAux {E : Type u} [Zero E] (R : Set Node)
    (e : E) (d : TreeSeq E) : Node → Node → E
  | _q, [] => e
  | q, n :: r =>
      match Classical.dec (child q n ∈ R) with
      | isTrue _ =>
        pasteAtFirstExitAux R e d (child q n) r
      | isFalse _ =>
        d r

/-- If the pasted sequence is norm-bounded by `e`, then every first-exit
paste is also norm-bounded by `e`. This proves boundedness of `z_m^R`. -/
theorem pasteAtFirstExitAux_norm_le {E : Type u} [SeminormedAddCommGroup E]
    {R : Set Node} {e : E} {d : TreeSeq E}
    (hd : ∀ s : Node, ‖d s‖ ≤ ‖e‖) :
    ∀ q r : Node, ‖pasteAtFirstExitAux R e d q r‖ ≤ ‖e‖ := by
  intro q r
  induction r generalizing q with
  | nil =>
      simp [pasteAtFirstExitAux]
  | cons n r ih =>
      by_cases h : child q n ∈ R
      · have hdec : Classical.dec (child q n ∈ R) = isTrue h := Subsingleton.elim _ _
        simpa [pasteAtFirstExitAux, hdec] using ih (child q n)
      · have hdec : Classical.dec (child q n ∈ R) = isFalse h := Subsingleton.elim _ _
        simpa [pasteAtFirstExitAux, hdec] using hd r

/-- Eventual child constancy is preserved by first-exit pasting. This is the
technical input for putting `z_m^R` and `u_m^R` into the closed space `Z_E`. -/
theorem pasteAtFirstExitAux_eventuallyChildEq {E : Type u} [Zero E]
    (R : Set Node) (e : E) (d : TreeSeq E)
    (hd_root : d root = e)
    (hd_event :
      ∀ s : Node, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → d (child s n) = d s) :
    ∀ q r : Node, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      pasteAtFirstExitAux R e d q (child r n) = pasteAtFirstExitAux R e d q r := by
  intro q r
  induction r generalizing q with
  | nil =>
      refine ⟨0, ?_⟩
      intro n _hn
      by_cases h : q ++ [n] ∈ R
      · have hdec : Classical.dec (q ++ [n] ∈ R) = isTrue h := Subsingleton.elim _ _
        simp [child, pasteAtFirstExitAux, hdec]
      · have hdec : Classical.dec (q ++ [n] ∈ R) = isFalse h := Subsingleton.elim _ _
        simpa [child, pasteAtFirstExitAux, hdec, root] using hd_root
  | cons a rest ih =>
      by_cases h : q ++ [a] ∈ R
      · rcases ih (q ++ [a]) with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn
        have hdec : Classical.dec (q ++ [a] ∈ R) = isTrue h := Subsingleton.elim _ _
        simpa [child, pasteAtFirstExitAux, hdec, List.append_assoc] using hN n hn
      · rcases hd_event rest with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn
        have hdec : Classical.dec (q ++ [a] ∈ R) = isFalse h := Subsingleton.elim _ _
        simpa [child, pasteAtFirstExitAux, hdec, List.append_assoc] using hN n hn

/-- Positivity is preserved by first-exit pasting, used in Lemmas
`z-lower-in-X` and `u-upper-in-Y`. -/
theorem pasteAtFirstExitAux_nonnegative {E : Type u} [Zero E] [LE E]
    (R : Set Node) (e : E) (d : TreeSeq E)
    (he : 0 ≤ e) (hd : ∀ s : Node, 0 ≤ d s) :
    ∀ q r : Node, 0 ≤ pasteAtFirstExitAux R e d q r := by
  intro q r
  induction r generalizing q with
  | nil =>
      simpa [pasteAtFirstExitAux] using he
  | cons a rest ih =>
      by_cases h : q ++ [a] ∈ R
      · have hdec : Classical.dec (q ++ [a] ∈ R) = isTrue h := Subsingleton.elim _ _
        simpa [child, pasteAtFirstExitAux, hdec] using ih (q ++ [a])
      · have hdec : Classical.dec (q ++ [a] ∈ R) = isFalse h := Subsingleton.elim _ _
        simpa [child, pasteAtFirstExitAux, hdec] using hd rest

/-- Coordinatewise monotonicity is preserved by first-exit pasting, used to
transfer monotonicity of `d_m` and `a_m` to the tree-indexed sequences. -/
theorem pasteAtFirstExitAux_mono {E : Type u} [Zero E] [Preorder E]
    (R : Set Node) (e : E) (d₁ d₂ : TreeSeq E)
    (hd : ∀ s : Node, d₁ s ≤ d₂ s) :
    ∀ q r : Node, pasteAtFirstExitAux R e d₁ q r ≤ pasteAtFirstExitAux R e d₂ q r := by
  intro q r
  induction r generalizing q with
  | nil =>
      simp [pasteAtFirstExitAux]
  | cons a rest ih =>
      by_cases h : q ++ [a] ∈ R
      · have hdec : Classical.dec (q ++ [a] ∈ R) = isTrue h := Subsingleton.elim _ _
        simpa [child, pasteAtFirstExitAux, hdec] using ih (q ++ [a])
      · have hdec : Classical.dec (q ++ [a] ∈ R) = isFalse h := Subsingleton.elim _ _
        simpa [child, pasteAtFirstExitAux, hdec] using hd rest

/-- The raw element `z_m^R`: it is constantly `e` while inside `R`, and after
the first exit it is a pasted copy of `d_m`. -/
noncomputable def zLowerRaw {E : Type u} [Zero E] (R : Tree) (e : E) (m : ℕ) :
    TreeSeq E :=
  fun s => pasteAtFirstExitAux (R : Set Node) e (deadSequenceRaw e m) root s

/-- Weighted boundedness of the raw Section 6 pasted sequence `z_m^R`. -/
theorem zLowerRaw_weightedBounded {E : Type u} [SeminormedAddCommGroup E]
    (R : Tree) (e : E) (m : ℕ) :
    WeightedBounded (zLowerRaw R e m) := by
  refine ⟨‖e‖, ?_⟩
  intro s
  have hnorm :
      ‖zLowerRaw R e m s‖ ≤ ‖e‖ :=
    pasteAtFirstExitAux_norm_le (R := (R : Set Node))
      (d := deadSequenceRaw e m) (deadSequenceRaw_norm_le e m) root s
  calc
    weight s * ‖zLowerRaw R e m s‖ ≤ 1 * ‖e‖ := by
      exact mul_le_mul (weight_le_one s) hnorm (norm_nonneg _) (by norm_num)
    _ = ‖e‖ := by ring

/-- The element `z_m^R ∈ V_E`. -/
noncomputable def zLower {E : Type u} [SeminormedAddCommGroup E]
    (R : Tree) (e : E) (m : ℕ) : V E :=
  ⟨zLowerRaw R e m, zLowerRaw_weightedBounded R e m⟩

/-- The zero-based sequence `m ↦ z_{m+1}^R`. -/
noncomputable def zLowerSeq {E : Type u} [SeminormedAddCommGroup E]
    (R : Tree) (e : E) : ℕ → V E :=
  fun m => zLower R e (m + 1)

/-- The reduction map `Theta(T) = (z_m^{\widehat T})_m`. -/
noncomputable def thetaLower {E : Type u} [SeminormedAddCommGroup E]
    (e : E) (T : Tree) : ℕ → V E :=
  zLowerSeq (fatten T) e

/-- The element `y^a` from the ill-founded case: the indicator of the domination
cone over a branch, with values `e` and `0`. -/
noncomputable def branchConeIndicatorRaw {E : Type u} [Zero E] (e : E)
    (b : ℕ → ℕ) : TreeSeq E :=
  fun s =>
    match Classical.dec (s ∈ BranchCone b) with
    | isTrue _ => e
    | isFalse _ => 0

/-- Weighted boundedness of the branch-cone indicator `y^a` used in the
ill-founded direction of the lower reduction. -/
theorem branchConeIndicatorRaw_weightedBounded {E : Type u}
    [SeminormedAddCommGroup E] (e : E) (b : ℕ → ℕ) :
    WeightedBounded (branchConeIndicatorRaw e b) := by
  refine ⟨‖e‖, ?_⟩
  intro s
  have hnorm : ‖branchConeIndicatorRaw e b s‖ ≤ ‖e‖ := by
    by_cases h : s ∈ BranchCone b
    · have hdec : Classical.dec (s ∈ BranchCone b) = isTrue h := Subsingleton.elim _ _
      simp [branchConeIndicatorRaw, hdec]
    · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse h := Subsingleton.elim _ _
      simp [branchConeIndicatorRaw, hdec]
  calc
    weight s * ‖branchConeIndicatorRaw e b s‖ ≤ 1 * ‖e‖ := by
      exact mul_le_mul (weight_le_one s) hnorm (norm_nonneg _) (by norm_num)
    _ = ‖e‖ := by ring

/-- The bundled lower-bound candidate `y^a ∈ V_E`. -/
noncomputable def branchConeIndicator {E : Type u} [SeminormedAddCommGroup E]
    (e : E) (b : ℕ → ℕ) : V E :=
  ⟨branchConeIndicatorRaw e b, branchConeIndicatorRaw_weightedBounded e b⟩

/-- Continuity of a map from trees, expressed by finite agreement in the tree
coordinate and weighted-norm closeness in the target. -/
def TreeToWeightedContinuous {E : Type u} [SeminormedAddCommGroup E]
    (F : Tree → V E) : Prop :=
  ∀ T : Tree, ∀ ε : ℝ, 0 < ε →
    ∃ A : Finset Node,
      ∀ U : Tree,
        (∀ s : Node, s ∈ A → (s ∈ (T : Set Node) ↔ s ∈ (U : Set Node))) →
          ‖F T - F U‖ < ε

/-- Coordinatewise continuity for maps from trees into sequence spaces. -/
def TreeToSequenceContinuous {E : Type u} [SeminormedAddCommGroup E]
    (F : Tree → ℕ → V E) : Prop :=
  ∀ m : ℕ, TreeToWeightedContinuous fun T => F T m

/-- The finite control set used in the proof of continuity of `R ↦ z_m^R`. -/
def lowerContinuityControlSet (ε : ℝ) : Set Node :=
  {r : Node | r ≠ root ∧ ε ≤ properExtensionWeightBound r}

/-- The bundled sequence `d_m` is uniformly bounded in the unweighted norm,
one hypothesis of Lemma `eventually-constant-template`. -/
theorem deadSequence_unweightedBounded {E : Type u} [NormedAddCommGroup E]
    (e : E) (m : ℕ) :
    UnweightedBounded (deadSequence e m) := by
  refine ⟨‖e‖, ?_⟩
  intro s
  exact deadSequenceRaw_norm_le e m s

/-- The Section 6 sequence `d_m` is eventually constant along children,
another hypothesis of Lemma `eventually-constant-template`. -/
theorem deadSequence_eventuallyConstant {E : Type u} [NormedAddCommGroup E]
    (e : E) (m : ℕ) :
    EventuallyConstantAlongChildren (deadSequence e m) := by
  intro s
  cases s with
  | nil =>
      refine ⟨m, ?_⟩
      intro n hn
      change deadSequenceRaw e m (child root n) = deadSequenceRaw e m root
      simp [deadSequenceRaw, root, child, hn]
  | cons a rest =>
      refine ⟨0, ?_⟩
      intro n _hn
      change deadSequenceRaw e m (child (a :: rest) n) = deadSequenceRaw e m (a :: rest)
      simp [deadSequenceRaw, child]

/-- Raw eventual-child form for `d_m`, used by the first-exit paste helper. -/
theorem deadSequenceRaw_eventuallyChildEq {E : Type u} [Zero E] (e : E) (m : ℕ) :
    ∀ s : Node, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      deadSequenceRaw e m (child s n) = deadSequenceRaw e m s := by
  intro s
  cases s with
  | nil =>
      refine ⟨m, ?_⟩
      intro n hn
      simp [deadSequenceRaw, child, hn]
  | cons a rest =>
      refine ⟨0, ?_⟩
      intro n _hn
      simp [deadSequenceRaw, child]

/-- Membership `d_m ∈ Z_E`, formalizing the `d_m ∈ X_+` setup in Section 6
via the eventual-constancy template. -/
theorem deadSequence_mem_Z {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] (e : E) (m : ℕ) :
    deadSequence e m ∈ Z E := by
  exact eventually_constant_template (deadSequence e m)
    (deadSequence_unweightedBounded e m) (deadSequence_eventuallyConstant e m)

/-- Positivity of the zero-based sequence `m ↦ d_{m+1}` from Section 6. -/
theorem deadSequenceSeq_coordinate_nonnegative {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) :
    ∀ m : ℕ, CoordinatewiseNonnegative (deadSequenceSeq e m) := by
  intro m s
  change 0 ≤ deadSequenceRaw e (m + 1) s
  cases s with
  | nil =>
      simpa [deadSequenceRaw] using he.1
  | cons n rest =>
      by_cases h : n < m + 1
      · simp [deadSequenceRaw, h]
      · simpa [deadSequenceRaw, h] using he.1

/-- Monotonicity of the Section 6 sequence: `d_{m+2} ≤ d_{m+1}` in Lean's
zero-based indexing. -/
theorem deadSequenceSeq_decreasing {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) :
    ∀ m : ℕ, CoordinatewiseLE (deadSequenceSeq e (m + 1)) (deadSequenceSeq e m) := by
  intro m s
  change deadSequenceRaw e ((m + 1) + 1) s ≤ deadSequenceRaw e (m + 1) s
  cases s with
  | nil =>
      simp [deadSequenceRaw]
  | cons n rest =>
      by_cases h : n < m + 1
      · have h' : n < (m + 1) + 1 := Nat.lt_succ_of_lt h
        simp [deadSequenceRaw, h, h']
      · by_cases h' : n < (m + 1) + 1
        · simpa [deadSequenceRaw, h, h'] using he.1
        · simp [deadSequenceRaw, h, h']

/-- The pasted lower element `z_m^R` is uniformly bounded in the unweighted
norm, as in Lemma `z-lower-in-X`. -/
theorem zLower_unweightedBounded {E : Type u} [NormedAddCommGroup E]
    (R : Tree) (e : E) (m : ℕ) :
    UnweightedBounded (zLower R e m) := by
  refine ⟨‖e‖, ?_⟩
  intro s
  exact pasteAtFirstExitAux_norm_le (R := (R : Set Node))
    (d := deadSequenceRaw e m) (deadSequenceRaw_norm_le e m) root s

/-- The pasted lower element `z_m^R` is eventually constant along children,
the eventual-constancy half of Lemma `z-lower-in-X`. -/
theorem zLower_eventuallyConstant {E : Type u} [NormedAddCommGroup E]
    (R : Tree) (e : E) (m : ℕ) :
    EventuallyConstantAlongChildren (zLower R e m) := by
  intro s
  exact pasteAtFirstExitAux_eventuallyChildEq (R : Set Node) e (deadSequenceRaw e m)
    (by simp [deadSequenceRaw, root]) (deadSequenceRaw_eventuallyChildEq e m) root s

/-- Membership `z_m^R ∈ Z_E`, one of the conclusions of Lemma
`z-lower-in-X`. -/
theorem zLower_mem_Z {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] (R : Tree) (e : E) (m : ℕ) :
    zLower R e m ∈ Z E := by
  exact eventually_constant_template (zLower R e m)
    (zLower_unweightedBounded R e m) (zLower_eventuallyConstant R e m)

/-- Positivity of the pasted lower sequence `(z_m^R)_m`, part of Lemma
`z-lower-in-X`. -/
theorem zLowerSeq_coordinate_nonnegative {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) (R : Tree) :
    ∀ m : ℕ, CoordinatewiseNonnegative (zLowerSeq R e m) := by
  intro m s
  exact pasteAtFirstExitAux_nonnegative (R : Set Node) e (deadSequenceRaw e (m + 1))
    he.1 (deadSequenceSeq_coordinate_nonnegative he m) root s

/-- Decreasingness of the pasted sequence `(z_m^R)_m`, part of Lemma
`z-lower-in-X`. -/
theorem zLowerSeq_decreasing {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) (R : Tree) :
    ∀ m : ℕ, CoordinatewiseLE (zLowerSeq R e (m + 1)) (zLowerSeq R e m) := by
  intro m s
  exact pasteAtFirstExitAux_mono (R : Set Node) e
    (deadSequenceRaw e ((m + 1) + 1)) (deadSequenceRaw e (m + 1))
    (deadSequenceSeq_decreasing he m) root s

end LowerComplete
end WeightedTree
end DSTBL3
