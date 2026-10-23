import ThmBC.Lower.Complete

/-!
# The upper construction — basic sequences

This file begins Section 7 of `paper.tex`: it defines the sublattice `Y`, the
increasing local sequence `a_m`, and the tree-indexed pasted sequences `u_m^R`,
then proves their basic membership, positivity, and monotonicity properties.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

open DSTBL3.WeightedTree
open LowerComplete

namespace UpperComplete

/-- The closed sublattice `Y = {y ∈ Z_ℝ | y_root = 0}` from Section 7. -/
def Y : Set (V ℝ) :=
  {y : V ℝ | y ∈ Z ℝ ∧ y root = 0}

/-- Order upper bounds for sequences in the sublattice `Y`. -/
def IsOrderUpperBoundInY (y : V ℝ) (u : ℕ → V ℝ) : Prop :=
  y ∈ Y ∧ ∀ m : ℕ, CoordinatewiseLE (u m) y

/-- A positive increasing sequence in the coordinatewise order. -/
def IsPositiveIncreasing (u : ℕ → V ℝ) : Prop :=
  (∀ m : ℕ, CoordinatewiseNonnegative (u m)) ∧
    ∀ m : ℕ, CoordinatewiseLE (u m) (u (m + 1))

/-- The set `Y^{\uparrow\infty}`: positive increasing sequences in `Y` which
are not order bounded in `Y`. -/
def YUpwardUnbounded (u : ℕ → V ℝ) : Prop :=
  (∀ m : ℕ, u m ∈ Y) ∧
    IsPositiveIncreasing u ∧
      ¬ ∃ y : V ℝ, IsOrderUpperBoundInY y u

/-- The local Section 7 sequence `a_m`, before bundling it as an element of
`V_ℝ`. It has root value `0`; on first-level subtree `j` it is constantly `1`
when `j ≤ m`, and constantly `0` otherwise. -/
noncomputable def upperSequenceRaw (m : ℕ) : TreeSeq ℝ
  | [] => 0
  | j :: _ => if j ≤ m then 1 else 0

/-- This is the boundedness part of the paragraph defining `a_m` in
Section 7: the coordinates of `a_m` are only `0` and `1`, so the weighted
supremum is finite and the raw indexed sequence can be bundled as an element
of `V_ℝ`. -/
theorem upperSequenceRaw_weightedBounded (m : ℕ) :
    WeightedBounded (upperSequenceRaw m) := by
  refine ⟨1, ?_⟩
  intro s
  have hnorm : ‖upperSequenceRaw m s‖ ≤ (1 : ℝ) := by
    cases s with
    | nil =>
        simp [upperSequenceRaw]
    | cons j rest =>
        by_cases h : j ≤ m
        · simp [upperSequenceRaw, h]
        · simp [upperSequenceRaw, h]
  calc
    weight s * ‖upperSequenceRaw m s‖ ≤ 1 * (1 : ℝ) := by
      exact mul_le_mul (weight_le_one s) hnorm (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The element `a_m ∈ V_ℝ`. -/
noncomputable def upperSequence (m : ℕ) : V ℝ :=
  ⟨upperSequenceRaw m, upperSequenceRaw_weightedBounded m⟩

/-- The increasing local sequence `(a_m)_m`. -/
noncomputable def upperSequenceSeq : ℕ → V ℝ :=
  fun m => upperSequence m

/-- Formalizes the displayed defining equation `(a_m)_∅ = 0` in Section 7. -/
theorem upperSequence_root (m : ℕ) :
    upperSequence m root = 0 := by
  simp [upperSequence, upperSequenceRaw, root]

/-- Records the membership assertion `a_m ∈ Y` from the paragraph defining
the local sequence before Lemma `local-unbounded`. -/
theorem upperSequence_mem_Y (m : ℕ) :
    upperSequence m ∈ Y := by
  refine ⟨?_, upperSequence_root m⟩
  apply eventually_constant_template (upperSequence m)
  · refine ⟨1, ?_⟩
    intro s
    have hnorm : ‖upperSequenceRaw m s‖ ≤ (1 : ℝ) := by
      cases s with
      | nil =>
          simp [upperSequenceRaw]
      | cons j rest =>
          by_cases h : j ≤ m
          · simp [upperSequenceRaw, h]
          · simp [upperSequenceRaw, h]
    simpa [upperSequence] using hnorm
  · intro s
    cases s with
    | nil =>
        refine ⟨m + 1, ?_⟩
        intro n hn
        have hn_not_le : ¬ n ≤ m := by omega
        simp [upperSequence, upperSequenceRaw, child, hn_not_le]
    | cons j rest =>
        refine ⟨0, ?_⟩
        intro n _hn
        simp [upperSequence, upperSequenceRaw, child]

/-- This is the positivity part of the paper's statement `a_m ∈ Y_+`: every
coordinate of `a_m` is either `0` or `1`. -/
theorem upperSequence_coordinate_nonnegative (m : ℕ) :
    CoordinatewiseNonnegative (upperSequence m) := by
  intro s
  change 0 ≤ upperSequenceRaw m s
  cases s with
  | nil =>
      simp [upperSequenceRaw]
  | cons j rest =>
      by_cases h : j ≤ m
      · simp [upperSequenceRaw, h]
      · simp [upperSequenceRaw, h]

/-- Formalizes the displayed monotonicity
`0 ≤ a_1 ≤ a_2 ≤ ...` from Section 7, using the zero-based Lean indexing
`a_m ≤ a_{m+1}`. -/
theorem upperSequence_increasing :
    ∀ m : ℕ, CoordinatewiseLE (upperSequence m) (upperSequence (m + 1)) := by
  intro m s
  change upperSequenceRaw m s ≤ upperSequenceRaw (m + 1) s
  cases s with
  | nil =>
      simp [upperSequenceRaw]
  | cons j rest =>
      by_cases h : j ≤ m
      · have hsucc : j ≤ m + 1 := h.trans (Nat.le_succ m)
        simp [upperSequenceRaw, h, hsucc]
      · by_cases hsucc : j ≤ m + 1
        · simp [upperSequenceRaw, h, hsucc]
        · simp [upperSequenceRaw, h, hsucc]

/-- Formalizes the sentence "Note that each `a_m` is finite-rank" in
Section 7; this is one route to the eventual-constant facts used later to put
pasted sequences in `Z_ℝ`. -/
theorem upperSequence_finiteRank (m : ℕ) :
    FiniteRank (upperSequence m) := by
  let N : Node → ℕ := fun _ => m + 1
  let F : Set Node := (controlledTree N 1 : Set Node)
  refine ⟨F, controlledTree_isFiniteDownwardClosedTree N 1, ?_⟩
  intro s n hs hchild t
  change upperSequenceRaw m (child s n ++ t) = upperSequenceRaw m s
  cases s with
  | nil =>
      have hn_not_lt : ¬n < m + 1 := by
        intro hn
        have hn_le : n ≤ m := Nat.le_of_lt_succ hn
        apply hchild
        simp [F, N, controlledTree, child, root, hn_le]
      have hn_not_le : ¬n ≤ m := by
        intro hn
        exact hn_not_lt (Nat.lt_succ_of_le hn)
      simp [upperSequenceRaw, child, hn_not_le]
  | cons j rest =>
      have hj_le : j ≤ m := by
        have hs' := hs
        simp [F, N, controlledTree, child, root] at hs'
        exact hs'.1
      simp [upperSequenceRaw, child, hj_le]

/-- Paper Lemma `local-unbounded`: the local sequence `(a_m)` is not order
bounded in `Y`.  The paper's argument says that an upper bound would force
all first-level coordinates to be at least `1`, contradicting child
convergence to the root value `0`. -/
theorem local_unbounded_template :
    ¬ ∃ y : V ℝ, IsOrderUpperBoundInY y upperSequenceSeq := by
  rintro ⟨y, hyub⟩
  rcases hyub with ⟨hyY, hupper⟩
  rcases hyY with ⟨hyZ, hyroot⟩
  have hchild_tendsto :
      Tendsto (fun n : ℕ => y (child root n)) atTop (nhds (0 : ℝ)) := by
    simpa [hyroot] using child_convergence_template (E := ℝ) hyZ root
  rw [Metric.tendsto_atTop] at hchild_tendsto
  rcases hchild_tendsto ((1 : ℝ) / 2) (by norm_num) with ⟨N, hN⟩
  have hnear : dist (y (child root N)) 0 < (1 : ℝ) / 2 := hN N (le_refl N)
  have hupperN : (1 : ℝ) ≤ y (child root N) := by
    have hcoord := hupper N (child root N)
    have hvalue : upperSequenceSeq N (child root N) = (1 : ℝ) := by
      simp [upperSequenceSeq, upperSequence, upperSequenceRaw, child, root]
    simpa [hvalue] using hcoord
  have hlt : y (child root N) < (1 : ℝ) / 2 := by
    have habs : |y (child root N)| < (1 : ℝ) / 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using hnear
    exact (abs_lt.mp habs).2
  linarith

/-- The raw element `u_m^R`: it is `0` while inside `R`, and after the first
exit it is a pasted copy of `a_m`. -/
noncomputable def uUpperRaw (R : Tree) (m : ℕ) : TreeSeq ℝ :=
  fun s => pasteAtFirstExitAux (R : Set Node) (0 : ℝ) (upperSequenceRaw m) root s

/-- Boundedness of the raw pasted sequence `u_m^R`, used before Lemma
`u-upper-in-Y`: inside the tree the value is `0`, and after first exit the
pasted copy of `a_m` still only takes the values `0` and `1`. -/
theorem uUpperRaw_weightedBounded (R : Tree) (m : ℕ) :
    WeightedBounded (uUpperRaw R m) := by
  refine ⟨1, ?_⟩
  have hd_norm : ∀ s : Node, ‖upperSequenceRaw m s‖ ≤ (1 : ℝ) := by
    intro s
    cases s with
    | nil =>
        simp [upperSequenceRaw]
    | cons j rest =>
        by_cases h : j ≤ m
        · simp [upperSequenceRaw, h]
        · simp [upperSequenceRaw, h]
  have hpaste_norm :
      ∀ q r : Node,
        ‖pasteAtFirstExitAux (R : Set Node) (0 : ℝ) (upperSequenceRaw m) q r‖ ≤
          (1 : ℝ) := by
    intro q r
    induction r generalizing q with
    | nil =>
        simp [pasteAtFirstExitAux]
    | cons n rest ih =>
        by_cases h : child q n ∈ (R : Set Node)
        · have hdec : Classical.dec (child q n ∈ (R : Set Node)) = isTrue h :=
            Subsingleton.elim _ _
          simpa [pasteAtFirstExitAux, hdec] using ih (child q n)
        · have hdec : Classical.dec (child q n ∈ (R : Set Node)) = isFalse h :=
            Subsingleton.elim _ _
          simpa [pasteAtFirstExitAux, hdec] using hd_norm rest
  intro s
  calc
    weight s * ‖uUpperRaw R m s‖ ≤ 1 * (1 : ℝ) := by
      exact mul_le_mul (weight_le_one s) (hpaste_norm root s) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The element `u_m^R ∈ V_ℝ`. -/
noncomputable def uUpper (R : Tree) (m : ℕ) : V ℝ :=
  ⟨uUpperRaw R m, uUpperRaw_weightedBounded R m⟩

/-- The increasing sequence `(u_m^R)_m`. -/
noncomputable def uUpperSeq (R : Tree) : ℕ → V ℝ :=
  fun m => uUpper R m

/-- Root-coordinate part of Lemma `u-upper-in-Y`: the pasted sequence
`u_m^R` has value `0` at the root, matching the defining equation for `Y`. -/
theorem uUpper_root (R : Tree) (m : ℕ) :
    uUpper R m root = 0 := by
  simp [uUpper, uUpperRaw, pasteAtFirstExitAux, root]

/-- Membership part of Lemma `u-upper-in-Y`: `u_m^R` lies in the sublattice
`Y`, combining `Z_ℝ` membership from eventual constancy along children with
the root-coordinate calculation. -/
theorem uUpper_mem_Y (R : Tree) (m : ℕ) :
    uUpper R m ∈ Y := by
  have hd_norm : ∀ s : Node, ‖upperSequenceRaw m s‖ ≤ (1 : ℝ) := by
    intro s
    cases s with
    | nil =>
        simp [upperSequenceRaw]
    | cons j rest =>
        by_cases h : j ≤ m
        · simp [upperSequenceRaw, h]
        · simp [upperSequenceRaw, h]
  have hpaste_norm :
      ∀ q r : Node,
        ‖pasteAtFirstExitAux (R : Set Node) (0 : ℝ) (upperSequenceRaw m) q r‖ ≤
          (1 : ℝ) := by
    intro q r
    induction r generalizing q with
    | nil =>
        simp [pasteAtFirstExitAux]
    | cons n rest ih =>
        by_cases h : child q n ∈ (R : Set Node)
        · have hdec : Classical.dec (child q n ∈ (R : Set Node)) = isTrue h :=
            Subsingleton.elim _ _
          simpa [pasteAtFirstExitAux, hdec] using ih (child q n)
        · have hdec : Classical.dec (child q n ∈ (R : Set Node)) = isFalse h :=
            Subsingleton.elim _ _
          simpa [pasteAtFirstExitAux, hdec] using hd_norm rest
  have hraw_event :
      ∀ s : Node, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        upperSequenceRaw m (child s n) = upperSequenceRaw m s := by
    intro s
    cases s with
    | nil =>
        refine ⟨m + 1, ?_⟩
        intro n hn
        have hn_not_le : ¬n ≤ m := by omega
        simp [upperSequenceRaw, child, hn_not_le]
    | cons j rest =>
        refine ⟨0, ?_⟩
        intro n _hn
        simp [upperSequenceRaw, child]
  refine ⟨?_, uUpper_root R m⟩
  apply eventually_constant_template (uUpper R m)
  · refine ⟨1, ?_⟩
    intro s
    change ‖uUpperRaw R m s‖ ≤ (1 : ℝ)
    simpa [uUpperRaw] using hpaste_norm root s
  · intro s
    change ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      uUpperRaw R m (child s n) = uUpperRaw R m s
    simpa [uUpperRaw] using
      pasteAtFirstExitAux_eventuallyChildEq (R : Set Node) (0 : ℝ) (upperSequenceRaw m)
        (by simp [upperSequenceRaw, root]) hraw_event root s

/-- Positivity part of Lemma `u-upper-in-Y`: the pasted sequence has only
nonnegative coordinates, since it is made from `0` and `a_m`. -/
theorem uUpper_coordinate_nonnegative (R : Tree) (m : ℕ) :
    CoordinatewiseNonnegative (uUpper R m) := by
  intro s
  change 0 ≤ uUpperRaw R m s
  have hd : ∀ r : Node, 0 ≤ upperSequenceRaw m r := by
    intro r
    change 0 ≤ upperSequence m r
    exact upperSequence_coordinate_nonnegative m r
  simpa [uUpperRaw] using
    pasteAtFirstExitAux_nonnegative (R : Set Node) (0 : ℝ) (upperSequenceRaw m)
      (by norm_num) hd root s

/-- Monotonicity part of Lemma `u-upper-in-Y`: the first-exit pasting
preserves the coordinatewise inequalities `a_m ≤ a_{m+1}`. -/
theorem uUpper_increasing (R : Tree) :
    ∀ m : ℕ, CoordinatewiseLE (uUpper R m) (uUpper R (m + 1)) := by
  intro m s
  change uUpperRaw R m s ≤ uUpperRaw R (m + 1) s
  have hd : ∀ r : Node, upperSequenceRaw m r ≤ upperSequenceRaw (m + 1) r := by
    intro r
    change upperSequence m r ≤ upperSequence (m + 1) r
    exact upperSequence_increasing m r
  simpa [uUpperRaw] using
    pasteAtFirstExitAux_mono (R : Set Node) (0 : ℝ) (upperSequenceRaw m)
      (upperSequenceRaw (m + 1)) hd root s

end UpperComplete
end WeightedTree
end DSTBL3
