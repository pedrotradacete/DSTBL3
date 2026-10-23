import ThmBC.Tree.Eventual

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

universe u

/-- Coordinatewise comparison of two nodes of the same length. -/
def PointwiseLE : Node → Node → Prop
  | [], [] => True
  | a :: as, b :: bs => a ≤ b ∧ PointwiseLE as bs
  | _, _ => False

/-- Rephrases pointwise comparison of nodes as Mathlib's `List.Forall₂`.
This is the list-level bridge used in the proof of the paper's fattening
lemma, Lemma `fattening`. -/
theorem pointwiseLE_iff_forall₂ {a s : Node} :
    PointwiseLE a s ↔ List.Forall₂ (fun m n : ℕ => m ≤ n) a s := by
  induction a generalizing s with
  | nil =>
      cases s <;> simp [PointwiseLE]
  | cons ah tl ih =>
      cases s <;> simp [PointwiseLE, ih]

/-- Pointwise-comparable nodes have the same length, a basic fact used in
the fattening preservation-of-well-foundedness argument. -/
theorem pointwiseLE_length_eq {a s : Node} (h : PointwiseLE a s) :
    a.length = s.length :=
  (pointwiseLE_iff_forall₂.1 h).length_eq

/-- Reflexivity of pointwise comparison, used when embedding a branch into
its fattened tree in Lemma `fattening`. -/
theorem pointwiseLE_refl (s : Node) :
    PointwiseLE s s := by
  exact pointwiseLE_iff_forall₂.2 <| List.forall₂_refl s

/-- Taking initial segments preserves pointwise comparison. This is the
prefix-closure ingredient for fattened and bounded subtrees. -/
theorem pointwiseLE_take {a s : Node} (n : ℕ) (h : PointwiseLE a s) :
    PointwiseLE (a.take n) (s.take n) := by
  exact pointwiseLE_iff_forall₂.2 <|
    List.forall₂_take n (pointwiseLE_iff_forall₂.1 h)

/-- Extends pointwise comparison by one coordinate, used to follow children
inside the fattening construction of Section 5. -/
theorem pointwiseLE_child {a s : Node} {m n : ℕ}
    (h : PointwiseLE a s) (hmn : m ≤ n) :
    PointwiseLE (child a m) (child s n) := by
  exact pointwiseLE_iff_forall₂.2 <|
    List.rel_append (pointwiseLE_iff_forall₂.1 h)
      (List.Forall₂.cons hmn List.Forall₂.nil)

/-- Recovers the last-coordinate inequality from a pointwise comparison of
children. This bounds the branching in the proof that fattening preserves
well-foundedness. -/
theorem pointwiseLE_child_right {a s : Node} {m n : ℕ}
    (h : PointwiseLE (child a m) (child s n)) :
    m ≤ n := by
  have hf := pointwiseLE_iff_forall₂.1 h
  have hlen : a.length = s.length := by
    have := hf.length_eq
    simp [child] at this
    omega
  have hget := hf.get (i := s.length) (by simp [child, ← hlen]) (by simp [child])
  simpa [child, hlen] using hget

/-- Splits a pointwise comparison against an appended node into a comparison
against the left prefix. This proves downward closure of the fattening
`T hat` in Lemma `fattening`. -/
theorem pointwiseLE_prefix_left {a s u : Node} :
    PointwiseLE a (s ++ u) → ∃ b v : Node, a = b ++ v ∧ PointwiseLE b s := by
  induction s generalizing a with
  | nil =>
      intro _h
      exact ⟨[], a, by simp, trivial⟩
  | cons sh st ih =>
      intro h
      cases a with
      | nil =>
          contradiction
      | cons ah rest =>
          rcases h with ⟨hah, htail⟩
          rcases ih htail with ⟨b, v, hbv, hb⟩
          refine ⟨ah :: b, v, ?_, ⟨hah, hb⟩⟩
          simp [hbv]

/-- The finite set of all nodes pointwise below a given node. It is the finite
control set proving continuity of the fattening map in Lemma `fattening`. -/
def pointwiseLEFinset : Node → Finset Node
  | [] => {[]}
  | n :: ns =>
      (Finset.range (n + 1)).biUnion fun k =>
        (pointwiseLEFinset ns).image fun t => k :: t

/-- Characterizes membership in the finite pointwise-below control set, used
directly in the continuity part of Lemma `fattening`. -/
theorem mem_pointwiseLEFinset {a s : Node} :
    a ∈ pointwiseLEFinset s ↔ PointwiseLE a s := by
  induction s generalizing a with
  | nil =>
      cases a <;> simp [pointwiseLEFinset, PointwiseLE]
  | cons n ns ih =>
      cases a with
      | nil =>
          simp [pointwiseLEFinset, PointwiseLE]
      | cons k ks =>
          simp [pointwiseLEFinset, PointwiseLE, ih]

/-- The fattening `T hat` of a tree. -/
def fatteningSet (T : Set Node) : Set Node :=
  {s : Node | ∃ a : Node, a ∈ T ∧ PointwiseLE a s}

/-- The fattening operation on coded trees. -/
def fatten (T : Tree) : Tree :=
  ⟨fatteningSet (T : Set Node), by
    constructor
    · exact ⟨root, T.2.1, trivial⟩
    · intro s t hst ht
      rcases hst with ⟨u, rfl⟩
      rcases ht with ⟨a, haT, hle⟩
      rcases pointwiseLE_prefix_left hle with ⟨b, v, hbv, hb⟩
      refine ⟨b, ?_, hb⟩
      exact T.2.2 ⟨v, hbv⟩ haT⟩

/-- Initial segment of length `k` of an infinite sequence. -/
def initialSegment (b : ℕ → ℕ) (k : ℕ) : Node :=
  List.ofFn fun i : Fin k => b i

/-- Taking the first `m` coordinates of an initial segment of length `n`
recovers the shorter initial segment. -/
theorem initialSegment_take (b : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (initialSegment b n).take m = initialSegment b m := by
  unfold initialSegment
  apply List.ext_getElem
  · simp [hmn]
  · intro i hi1 hi2
    simp

/-- Successor initial segments are obtained by adding the next child; this
matches the paper notation `s concat n`. -/
theorem initialSegment_succ (b : ℕ → ℕ) (k : ℕ) :
    initialSegment b (k + 1) = child (initialSegment b k) (b k) := by
  unfold initialSegment child
  rw [List.ofFn_succ']
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp

/-- If a node is pointwise below a branch segment, then every prefix has the
same property. This proves bounded subtrees are downward closed. -/
theorem pointwiseLE_initialSegment_prefix {b : ℕ → ℕ} {s t : Node}
    (hst : Prefix s t) (ht : PointwiseLE t (initialSegment b t.length)) :
    PointwiseLE s (initialSegment b s.length) := by
  rcases hst with ⟨u, rfl⟩
  have htake := pointwiseLE_take s.length ht
  have hinit :
      (initialSegment b (s.length + u.length)).take s.length = initialSegment b s.length :=
    initialSegment_take b (m := s.length) (n := s.length + u.length) (by omega)
  simpa [hinit] using htake

/-- Prefix form for the branch cone `L_b`: if an initial segment of `b` is
pointwise below a node, then the corresponding shorter initial segment is
pointwise below every prefix. -/
theorem pointwiseLE_initialSegment_prefix_left {b : ℕ → ℕ} {s t : Node}
    (hst : Prefix s t) (ht : PointwiseLE (initialSegment b t.length) t) :
    PointwiseLE (initialSegment b s.length) s := by
  rcases hst with ⟨u, rfl⟩
  have htake := pointwiseLE_take s.length ht
  have hinit :
      (initialSegment b (s.length + u.length)).take s.length = initialSegment b s.length :=
    initialSegment_take b (m := s.length) (n := s.length + u.length) (by omega)
  simpa [hinit] using htake

/-- An infinite branch through a tree. -/
def IsBranch (T : Set Node) (b : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, initialSegment b k ∈ T

/-- Well-foundedness of a tree, expressed as absence of infinite branches. -/
def WellFoundedTree (T : Set Node) : Prop :=
  ¬ ∃ b : ℕ → ℕ, IsBranch T b

/-- The subtree `L_b` associated to an infinite branch `b`. -/
def BranchCone (b : ℕ → ℕ) : Set Node :=
  {s : Node | PointwiseLE (initialSegment b s.length) s}

/-- The branch cone `L_b` is a tree, as used in the ill-founded cases of the
lower and upper reductions. -/
theorem branchCone_isTree (b : ℕ → ℕ) :
    IsTree (BranchCone b) := by
  constructor
  · simp [BranchCone, initialSegment, root, PointwiseLE]
  · intro s t hst ht
    exact pointwiseLE_initialSegment_prefix_left hst ht

/-- Subtree inclusion, used for `L_b` inside `T hat`. -/
def IsSubtreeOf (A T : Set Node) : Prop :=
  IsTree A ∧ A ⊆ T

/-- Product-topology continuity for maps between coded tree spaces: membership
of each output node depends on finitely many input nodes. -/
def TreeMapContinuous (f : Tree → Tree) : Prop :=
  ∀ s : Node,
    ∃ A : Finset Node,
      ∀ T U : Tree,
        (∀ a : Node, a ∈ A → (a ∈ (T : Set Node) ↔ a ∈ (U : Set Node))) →
          (s ∈ (f T : Set Node) ↔ s ∈ (f U : Set Node))

/-- The bounded subtree used in the proof that fattening preserves
well-foundedness: nodes of `T` which are pointwise bounded by a candidate
branch through `T hat`. -/
def boundedSubtreeSet (T : Set Node) (b : ℕ → ℕ) : Set Node :=
  {s : Node | s ∈ T ∧ PointwiseLE s (initialSegment b s.length)}

/-- The bounded subtree is itself a tree. This is the compactness-style
subtree used inside Lemma `fattening`. -/
theorem boundedSubtree_isTree {T : Set Node} (hT : IsTree T) (b : ℕ → ℕ) :
    IsTree (boundedSubtreeSet T b) := by
  constructor
  · exact ⟨hT.1, by simp [initialSegment, root, PointwiseLE]⟩
  · intro s t hst ht
    exact ⟨hT.2 hst ht.1, pointwiseLE_initialSegment_prefix hst ht.2⟩

/-- Every child in the bounded subtree has index bounded by the corresponding
coordinate of the candidate branch. This finiteness is what lets the
König-style branch extraction go through. -/
theorem boundedSubtree_child_bound {T : Set Node} {b : ℕ → ℕ}
    {p : Node} {n : ℕ} (h : child p n ∈ boundedSubtreeSet T b) :
    n ≤ b p.length := by
  have hle := h.2
  have hlen : (child p n).length = p.length + 1 := by
    simp [child]
  rw [hlen, initialSegment_succ] at hle
  exact pointwiseLE_child_right hle

/-- A node has arbitrarily long extensions in a subtree. This predicate is
the "good node" notion used to extract an actual branch from bounded levels
in Lemma `fattening`. -/
def HasArbitrarilyLongExtensions (B : Set Node) (p : Node) : Prop :=
  p ∈ B ∧ ∀ k : ℕ, ∃ a : Node, a ∈ B ∧ Prefix p a ∧ k ≤ a.length

/-- A good node in the bounded subtree has a good child. The proof uses the
coordinate bound above to rule out all children becoming eventually short. -/
theorem boundedSubtree_good_child {T : Set Node} (hT : IsTree T) (b : ℕ → ℕ)
    {p : Node}
    (hp : HasArbitrarilyLongExtensions (boundedSubtreeSet T b) p) :
    ∃ n : ℕ,
      HasArbitrarilyLongExtensions (boundedSubtreeSet T b) (child p n) := by
  classical
  let B : Set Node := boundedSubtreeSet T b
  have hBtree : IsTree B := boundedSubtree_isTree hT b
  by_contra hnone
  have hcut :
      ∀ n : ℕ, ∃ K : ℕ,
        ∀ a : Node, a ∈ B → Prefix (child p n) a → a.length < K := by
    intro n
    by_cases hnB : child p n ∈ B
    · have hnot_long :
          ¬ ∀ k : ℕ, ∃ a : Node, a ∈ B ∧ Prefix (child p n) a ∧ k ≤ a.length := by
        intro hlong
        exact hnone ⟨n, hnB, hlong⟩
      push Not at hnot_long
      rcases hnot_long with ⟨K, hK⟩
      refine ⟨K, ?_⟩
      intro a ha hpre
      have hnotle := hK a ha hpre
      omega
    · refine ⟨0, ?_⟩
      intro a ha hpre
      exfalso
      exact hnB (hBtree.2 hpre ha)
  let K : ℕ → ℕ := fun n => Classical.choose (hcut n)
  let M : ℕ := (Finset.range (b p.length + 1)).sup K
  let L : ℕ := max (p.length + 1) M
  rcases hp.2 L with ⟨a, haB, hpa, hlen⟩
  rcases hpa with ⟨u, rfl⟩
  cases u with
  | nil =>
      have hL : p.length + 1 ≤ L := le_max_left _ _
      simp at hlen
      omega
  | cons n rest =>
      have hchildPrefix : Prefix (child p n) (p ++ (n :: rest)) := by
        refine ⟨rest, ?_⟩
        simp [child, List.append_assoc]
      have hchildB : child p n ∈ B := hBtree.2 hchildPrefix haB
      have hn_le : n ≤ b p.length :=
        boundedSubtree_child_bound (T := T) (b := b) hchildB
      have hn_mem : n ∈ Finset.range (b p.length + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_of_le hn_le)
      have hKleM : K n ≤ M := Finset.le_sup (f := K) hn_mem
      have hKleLen : K n ≤ (p ++ (n :: rest)).length := by
        exact hKleM.trans ((le_max_right _ _).trans hlen)
      have hshort := (Classical.choose_spec (hcut n)) (p ++ (n :: rest)) haB hchildPrefix
      have hshortK : (p ++ (n :: rest)).length < K n := by
        simpa [K] using hshort
      omega

/-- Branch extraction for the bounded subtree: if it has nodes at every
level, then it has an infinite branch. This is the König-style core of the
well-foundedness part of Lemma `fattening`. -/
theorem boundedSubtree_has_branch {T : Set Node} (hT : IsTree T)
    {b : ℕ → ℕ}
    (hlevels :
      ∀ k : ℕ, ∃ s : Node, s ∈ boundedSubtreeSet T b ∧ s.length = k) :
    ∃ c : ℕ → ℕ, IsBranch (boundedSubtreeSet T b) c := by
  classical
  let B : Set Node := boundedSubtreeSet T b
  let Good : Node → Prop := HasArbitrarilyLongExtensions B
  have hrootGood : Good root := by
    constructor
    · exact (boundedSubtree_isTree hT b).1
    · intro k
      rcases hlevels k with ⟨a, haB, hlen⟩
      refine ⟨a, haB, ?_, ?_⟩
      · exact ⟨a, by simp [root]⟩
      · omega
  have hstep : ∀ p : Node, Good p → ∃ n : ℕ, Good (child p n) := by
    intro p hp
    exact boundedSubtree_good_child hT b hp
  let start : {p : Node // Good p} := ⟨root, hrootGood⟩
  let idx : {p : Node // Good p} → ℕ := fun p => Classical.choose (hstep p.1 p.2)
  let next : {p : Node // Good p} → {p : Node // Good p} := fun p =>
    ⟨child p.1 (idx p), Classical.choose_spec (hstep p.1 p.2)⟩
  let q : ℕ → {p : Node // Good p} := fun n => Nat.rec start (fun _ p => next p) n
  let c : ℕ → ℕ := fun n => idx (q n)
  refine ⟨c, ?_⟩
  have hq_succ : ∀ n : ℕ, (q (n + 1)).1 = child (q n).1 (c n) := by
    intro n
    rfl
  have hinit : ∀ n : ℕ, initialSegment c n = (q n).1 := by
    intro n
    induction n with
    | zero =>
        simp [initialSegment, root, q, start]
    | succ n ih =>
        rw [initialSegment_succ, ih, hq_succ n]
  intro k
  rw [hinit k]
  exact (q k).2.1

/-- Lemma `fattening`: fattening is continuous, preserves well-foundedness, and
turns each branch into a subtree with cofinitely many children at every node. -/
theorem fattening_template :
    TreeMapContinuous fatten ∧
      (∀ T : Tree,
        WellFoundedTree (T : Set Node) ↔
          WellFoundedTree (fatten T : Set Node)) ∧
        (∀ (T : Tree) (b : ℕ → ℕ),
          IsBranch (T : Set Node) b →
            IsSubtreeOf (BranchCone b) (fatten T : Set Node) ∧
              ∀ s : Node,
                s ∈ BranchCone b →
                  ∀ᶠ n in atTop, child s n ∈ BranchCone b) := by
  constructor
  · intro s
    refine ⟨pointwiseLEFinset s, ?_⟩
    intro T U hTU
    change s ∈ fatteningSet (T : Set Node) ↔ s ∈ fatteningSet (U : Set Node)
    constructor
    · rintro ⟨a, haT, has⟩
      exact ⟨a, (hTU a (mem_pointwiseLEFinset.2 has)).1 haT, has⟩
    · rintro ⟨a, haU, has⟩
      exact ⟨a, (hTU a (mem_pointwiseLEFinset.2 has)).2 haU, has⟩
  constructor
  · intro T
    constructor
    · intro hWF hfatBranch
      apply hWF
      rcases hfatBranch with ⟨b, hb⟩
      have hlevels :
          ∀ k : ℕ,
            ∃ s : Node,
              s ∈ boundedSubtreeSet (T : Set Node) b ∧ s.length = k := by
        intro k
        have hbk := hb k
        change initialSegment b k ∈ fatteningSet (T : Set Node) at hbk
        rcases hbk with ⟨a, haT, hab⟩
        have hlen : a.length = k := by
          have := pointwiseLE_length_eq hab
          simpa [initialSegment] using this
        refine ⟨a, ?_, hlen⟩
        exact ⟨haT, by simpa [hlen] using hab⟩
      rcases boundedSubtree_has_branch (T := (T : Set Node)) T.2 hlevels with ⟨c, hc⟩
      exact ⟨c, fun k => (hc k).1⟩
    · intro hWF hbranch
      apply hWF
      rcases hbranch with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      intro k
      change initialSegment b k ∈ fatteningSet (T : Set Node)
      exact ⟨initialSegment b k, hb k, pointwiseLE_refl _⟩
  · intro T b hb
    constructor
    · constructor
      · exact branchCone_isTree b
      · intro s hs
        change s ∈ fatteningSet (T : Set Node)
        exact ⟨initialSegment b s.length, hb s.length, hs⟩
    · intro s hs
      refine eventually_atTop.mpr ⟨b s.length, ?_⟩
      intro n hn
      have hchild :
          PointwiseLE (child (initialSegment b s.length) (b s.length)) (child s n) :=
        pointwiseLE_child hs hn
      simpa [BranchCone, child, initialSegment_succ] using hchild


end WeightedTree
end DSTBL3
