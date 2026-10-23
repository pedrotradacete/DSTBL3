import Mathlib.MeasureTheory.Constructions.Polish.Basic
import ThmBC.Tree.Tree

open Filter
open scoped BigOperators Topology

/-!
# Descriptive-set-theoretic conventions

This file contains the descriptive set theory used by the project, including
the standard topology on the tree space and the proof that well-founded trees
are `Π¹₁`-complete. The definitions follow the boldface convention from
classical descriptive set theory: coanalytic means complement analytic and
reductions are continuous reductions.

For completeness under continuous reductions we use the standard Kechris/Wadge
formulation with Baire space `ℕ → ℕ` as the source coding space. This is the
form in which the classical theorem that `WF` is `Π¹₁`-complete is used: every
coanalytic subset of Baire space continuously reduces to `WF`.
-/

namespace DSTBL3

universe u v w

/-- A coanalytic, or `Π¹₁`, subset of a topological space: its complement is
analytic in the descriptive-set-theoretic sense. Mathlib's `AnalyticSet` is the
boldface analytic pointclass. -/
def CoanalyticSet {α : Type u} [TopologicalSpace α] (A : Set α) : Prop :=
  MeasureTheory.AnalyticSet Aᶜ

/-- Continuous reducibility `C ≤c A`: there is a continuous map whose preimage
of `A` is exactly `C`. -/
def ContinuouslyReducible {Z : Type v} {X : Type u} [TopologicalSpace Z] [TopologicalSpace X]
    (C : Set Z) (A : Set X) : Prop :=
  ∃ f : Z → X, Continuous f ∧ ∀ z : Z, z ∈ C ↔ f z ∈ A

/-- `Π¹₁`-hardness with respect to continuous reductions from coanalytic subsets
of Baire space. This is the Kechris/Wadge coding convention appropriate for the
well-founded-tree complete set. -/
def Pi11Hard {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ C : Set (ℕ → ℕ),
    CoanalyticSet C → ContinuouslyReducible C A

/-- A `Π¹₁`-complete subset of a Polish space: it is coanalytic and hard, under
continuous reductions, for coanalytic subsets of Baire space. -/
def Pi11CompleteSet {X : Type u} [TopologicalSpace X] [PolishSpace X]
    (A : Set X) : Prop :=
  CoanalyticSet A ∧ Pi11Hard A

/-- Predicate-form version of `Pi11CompleteSet` for a subset of a fixed Polish
space. -/
def Pi11Complete {X : Type u} [TopologicalSpace X] [PolishSpace X]
    (P : X → Prop) : Prop :=
  Pi11CompleteSet {x : X | P x}

/-- A standard transfer principle: if a `Π¹₁`-complete set continuously reduces
to a coanalytic set, then the target set is `Π¹₁`-complete. -/
theorem pi11CompleteSet_of_complete_reduction {Y : Type v} {X : Type u}
    [TopologicalSpace Y] [PolishSpace Y] [TopologicalSpace X] [PolishSpace X]
    {B : Set Y} {A : Set X}
    (hB : Pi11CompleteSet B) (hA : CoanalyticSet A)
    (hred : ContinuouslyReducible B A) :
    Pi11CompleteSet A := by
  refine ⟨hA, ?_⟩
  intro C hC
  rcases hB.2 C hC with ⟨g, hg_cont, hg⟩
  rcases hred with ⟨f, hf_cont, hf⟩
  refine ⟨f ∘ g, hf_cont.comp hg_cont, ?_⟩
  intro z
  exact (hg z).trans (hf (g z))

namespace WeightedTree

/-- Code a tree by its characteristic function along the `Encodable` enumeration
of nodes. Values are `0` and `1`, but the codomain is Baire space `ℕ → ℕ`. -/
noncomputable def treeCharacteristicCode (T : Tree) : ℕ → ℕ :=
  fun n =>
    letI : DecidablePred (fun s : Node => s ∈ (T : Set Node)) := Classical.decPred _
    match Encodable.decode₂ Node n with
    | some s => if s ∈ (T : Set Node) then 1 else 0
    | none => 0

/-- The characteristic-code map from coded trees to Baire space is injective.
This lets the standard tree topology be induced from Baire space. -/
theorem treeCharacteristicCode_injective :
    Function.Injective treeCharacteristicCode := by
  intro T U h
  apply Subtype.ext
  ext s
  have hs := congrFun h (Encodable.encode s)
  simp [treeCharacteristicCode] at hs
  constructor
  · intro hT
    by_contra hU
    simp [hT, hU] at hs
  · intro hU
    by_contra hT
    simp [hT, hU] at hs

/-- The closed subset of Baire space consisting of characteristic functions of trees. -/
noncomputable def treeCharacteristicCodeSet : Set (ℕ → ℕ) :=
  {c | (∀ n : ℕ, c n = 0 ∨ c n = 1) ∧
    (∀ n : ℕ, Encodable.decode₂ Node n = none → c n = 0) ∧
    c (Encodable.encode root) = 1 ∧
    ∀ {s t : Node}, Prefix s t → c (Encodable.encode t) = 1 →
      c (Encodable.encode s) = 1}

/-- The set of Baire-space codes for trees is closed; this realizes the tree
space as a closed subspace of Baire space. -/
theorem treeCharacteristicCodeSet_isClosed :
    IsClosed treeCharacteristicCodeSet := by
  unfold treeCharacteristicCodeSet
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · change IsClosed {c : ℕ → ℕ | ∀ n : ℕ, c n = 0 ∨ c n = 1}
    have h_eq :
        {c : ℕ → ℕ | ∀ n : ℕ, c n = 0 ∨ c n = 1} =
          ⋂ n : ℕ, ({c : ℕ → ℕ | c n = 0} ∪ {c : ℕ → ℕ | c n = 1}) := by
      ext c
      simp [Set.mem_iInter]
    rw [h_eq]
    apply isClosed_iInter
    intro n
    have h0 : IsClosed {c : ℕ → ℕ | c n = 0} := by
      have hc : Continuous (fun c : ℕ → ℕ => c n) := continuous_apply n
      simpa only [Set.preimage_ofPred_eq] using
        IsClosed.preimage hc (isClosed_discrete ({m : ℕ | m = 0}))
    have h1 : IsClosed {c : ℕ → ℕ | c n = 1} := by
      have hc : Continuous (fun c : ℕ → ℕ => c n) := continuous_apply n
      simpa only [Set.preimage_ofPred_eq] using
        IsClosed.preimage hc (isClosed_discrete ({m : ℕ | m = 1}))
    exact h0.union h1
  · change IsClosed
      {c : ℕ → ℕ | ∀ n : ℕ, Encodable.decode₂ Node n = none → c n = 0}
    have h_eq :
        {c : ℕ → ℕ | ∀ n : ℕ, Encodable.decode₂ Node n = none → c n = 0} =
          ⋂ n : ℕ, {c : ℕ → ℕ | Encodable.decode₂ Node n = none → c n = 0} := by
      ext c
      simp [Set.mem_iInter]
    rw [h_eq]
    apply isClosed_iInter
    intro n
    by_cases hn : Encodable.decode₂ Node n = none
    · have h0 : IsClosed {c : ℕ → ℕ | c n = 0} := by
        have hc : Continuous (fun c : ℕ → ℕ => c n) := continuous_apply n
        simpa only [Set.preimage_ofPred_eq] using
          IsClosed.preimage hc (isClosed_discrete ({m : ℕ | m = 0}))
      convert h0 using 1
      ext c
      simp [hn]
    · convert isClosed_univ using 1
      ext c
      simp [hn]
  · have h1 : IsClosed {c : ℕ → ℕ | c (Encodable.encode root) = 1} := by
      have hc : Continuous (fun c : ℕ → ℕ => c (Encodable.encode root)) :=
        continuous_apply (Encodable.encode root)
      simpa only [Set.preimage_ofPred_eq] using
        IsClosed.preimage hc (isClosed_discrete ({m : ℕ | m = 1}))
    exact h1
  · change IsClosed {c : ℕ → ℕ |
        ∀ (s t : Node), Prefix s t → c (Encodable.encode t) = 1 →
          c (Encodable.encode s) = 1}
    have hdown_eq :
        {c : ℕ → ℕ | ∀ (s t : Node), Prefix s t →
          c (Encodable.encode t) = 1 → c (Encodable.encode s) = 1} =
          ⋂ s : Node, ⋂ t : Node,
            {c : ℕ → ℕ | Prefix s t → c (Encodable.encode t) = 1 →
              c (Encodable.encode s) = 1} := by
      ext c
      simp
    rw [hdown_eq]
    apply isClosed_iInter
    intro s
    apply isClosed_iInter
    intro t
    by_cases hst : Prefix s t
    · have hnot : IsClosed {c : ℕ → ℕ | c (Encodable.encode t) ≠ 1} := by
        have hc : Continuous (fun c : ℕ → ℕ => c (Encodable.encode t)) :=
          continuous_apply (Encodable.encode t)
        simpa only [Set.preimage_ofPred_eq] using
          IsClosed.preimage hc (isClosed_discrete ({m : ℕ | m ≠ 1}))
      have hyes : IsClosed {c : ℕ → ℕ | c (Encodable.encode s) = 1} := by
        have hc : Continuous (fun c : ℕ → ℕ => c (Encodable.encode s)) :=
          continuous_apply (Encodable.encode s)
        simpa only [Set.preimage_ofPred_eq] using
          IsClosed.preimage hc (isClosed_discrete ({m : ℕ | m = 1}))
      convert hnot.union hyes using 1
      ext c
      simp [hst]
      by_cases ht : c (Encodable.encode t) = 1 <;> simp [ht]
    · convert isClosed_univ using 1
      ext c
      simp [hst]

/-- The range of the characteristic-code map is exactly the closed set of
valid tree codes. -/
theorem treeCharacteristicCode_range_eq :
    Set.range treeCharacteristicCode = treeCharacteristicCodeSet := by
  ext c
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n
      cases hdec : Encodable.decode₂ Node n with
      | none => simp [treeCharacteristicCode, hdec]
      | some s =>
          by_cases hs : s ∈ (T : Set Node) <;> simp [treeCharacteristicCode, hdec, hs]
    · intro n hn
      simp [treeCharacteristicCode, hn]
    · simp [treeCharacteristicCode, T.2.1]
    · intro s t hst ht
      simp [treeCharacteristicCode] at ht ⊢
      exact T.2.2 hst ht
  · intro hc
    refine ⟨⟨{s : Node | c (Encodable.encode s) = 1}, ?_⟩, ?_⟩
    · constructor
      · exact hc.2.2.1
      · intro s t hst ht
        exact hc.2.2.2 hst ht
    · funext n
      cases hdec : Encodable.decode₂ Node n with
      | none =>
          simp [treeCharacteristicCode, hdec, hc.2.1 n hdec]
      | some s =>
          have henc : Encodable.encode s = n := Encodable.decode₂_eq_some.mp hdec
          subst n
          have hval := hc.1 (Encodable.encode s)
          simp [treeCharacteristicCode] at hdec ⊢
          rcases hval with h0 | h1
          · simp [h0]
          · simp [h1]

/-- The usual Polish topology on the space of trees on `ℕ`, realized as the
closed subspace of Baire space consisting of characteristic functions of trees. -/
@[reducible] noncomputable def treeStandardTopology : TopologicalSpace Tree :=
  TopologicalSpace.induced treeCharacteristicCode
    (inferInstance : TopologicalSpace (ℕ → ℕ))

/-- The standard tree topology is Polish because it is induced by a closed
embedding into Baire space. -/
theorem treeStandardPolishSpace : @PolishSpace Tree treeStandardTopology := by
  let : TopologicalSpace Tree := treeStandardTopology
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  have hclosedRange : IsClosed (Set.range treeCharacteristicCode) := by
    rw [treeCharacteristicCode_range_eq]
    exact treeCharacteristicCodeSet_isClosed
  have hclosedEmbedding : Topology.IsClosedEmbedding treeCharacteristicCode := by
    exact ⟨treeCharacteristicCode_injective.isEmbedding_induced, hclosedRange⟩
  exact hclosedEmbedding.polishSpace

/-- Existence package for the standard Polish topology on trees. -/
theorem tree_standard_polishTopology :
    ∃ treeTopology : TopologicalSpace Tree,
      @PolishSpace Tree treeTopology := by
  exact ⟨treeStandardTopology, treeStandardPolishSpace⟩

/-- The closed set of pairs `(T, b)` such that `b` is an infinite branch through
the tree `T`, in the standard coding topology on trees. -/
noncomputable def treeBranchSet : Set (Tree × (ℕ → ℕ)) :=
  {p | IsBranch (p.1 : Set Node) p.2}

/-- The branch relation `{(T,b) | b is a branch through T}` is closed in the
standard tree topology times Baire space. -/
theorem treeBranchSet_isClosed :
    (letI : TopologicalSpace Tree := treeStandardTopology
     letI : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
     IsClosed treeBranchSet) := by
  let : TopologicalSpace Tree := treeStandardTopology
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  let : TopologicalSpace Node := ⊥
  have : DiscreteTopology Node := ⟨rfl⟩
  have hpairClosed : IsClosed {p : Tree × Node | p.2 ∈ (p.1 : Set Node)} := by
    have hcont :
        Continuous (fun p : Tree × Node =>
          treeCharacteristicCode p.1 (Encodable.encode p.2)) := by
      rw [continuous_prod_of_discrete_right]
      intro s
      have hcode : Continuous treeCharacteristicCode := continuous_induced_dom
      exact (continuous_apply (Encodable.encode s)).comp hcode
    have hclosed :
        IsClosed
          {p : Tree × Node | treeCharacteristicCode p.1 (Encodable.encode p.2) = 1} := by
      simpa only [Set.preimage_ofPred_eq] using
        IsClosed.preimage hcont (isClosed_discrete ({m : ℕ | m = 1}))
    convert hclosed using 1
    ext p
    cases p with
    | mk T s => simp [treeCharacteristicCode]
  have h_eq : treeBranchSet =
      ⋂ k : ℕ, {p : Tree × (ℕ → ℕ) | initialSegment p.2 k ∈ (p.1 : Set Node)} := by
    ext p
    simp [treeBranchSet, IsBranch]
  rw [h_eq]
  apply isClosed_iInter
  intro k
  have hinit : @Continuous (ℕ → ℕ) Node inferInstance ⊥
      (fun b : ℕ → ℕ => initialSegment b k) := by
    have hres : Continuous (fun b : ℕ → ℕ => fun i : Fin k => b i) := by
      exact continuous_pi fun i => continuous_apply (i : ℕ)
    have hofFn : @Continuous (Fin k → ℕ) Node inferInstance ⊥
        (fun f : Fin k → ℕ => List.ofFn f) := by
      exact continuous_of_discreteTopology
    exact hofFn.comp hres
  have hF : Continuous (fun p : Tree × (ℕ → ℕ) => (p.1, initialSegment p.2 k)) := by
    exact continuous_fst.prodMk (hinit.comp continuous_snd)
  simpa only [Set.preimage_ofPred_eq] using IsClosed.preimage hF hpairClosed

/-- Standard Kechris theorem: well-founded trees form a coanalytic subset of
the usual Polish tree space. -/
theorem wellFoundedTrees_coanalytic_standard :
    @CoanalyticSet Tree treeStandardTopology
      {T : Tree | WellFoundedTree (T : Set Node)} := by
  let : TopologicalSpace Tree := treeStandardTopology
  let : PolishSpace Tree := treeStandardPolishSpace
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  change MeasureTheory.AnalyticSet ({T : Tree | WellFoundedTree (T : Set Node)}ᶜ)
  have hbranchAnalytic : MeasureTheory.AnalyticSet treeBranchSet :=
    treeBranchSet_isClosed.analyticSet
  have himage : MeasureTheory.AnalyticSet (Prod.fst '' treeBranchSet) :=
    hbranchAnalytic.image_of_continuous continuous_fst
  convert himage using 1
  ext T
  simp [treeBranchSet, WellFoundedTree]

/-- The one-node tree, used for reducing the empty analytic complement. -/
noncomputable def singletonRootTree : Tree :=
  ⟨{root}, by
    constructor
    · simp [root]
    · intro s t hst ht
      rcases ht with rfl
      rcases hst with ⟨u, hsu⟩
      cases s <;> simp [root] at hsu ⊢⟩

/-- The singleton-root tree has no infinite branch. -/
theorem singletonRootTree_wellFounded :
    WellFoundedTree (singletonRootTree : Set Node) := by
  intro hbranch
  rcases hbranch with ⟨b, hb⟩
  have h1 := hb 1
  change initialSegment b 1 ∈ ({root} : Set Node) at h1
  simp [initialSegment, root] at h1

/-- A prefix cannot be longer than the node it prefixes. -/
theorem prefix_length_le {s t : Node} (hst : Prefix s t) : s.length ≤ t.length := by
  rcases hst with ⟨u, rfl⟩
  simp

/-- If a branch initial segment equals a node, then the shorter initial
segment equals every prefix of that node. -/
theorem initialSegment_eq_of_prefix {b : ℕ → ℕ} {s t : Node}
    (hst : Prefix s t) (ht : initialSegment b t.length = t) :
    initialSegment b s.length = s := by
  rcases hst with ⟨u, rfl⟩
  have htake := congrArg (fun l : Node => l.take s.length) ht
  change (initialSegment b (s ++ u).length).take s.length = (s ++ u).take s.length at htake
  have hinit :
      (initialSegment b (s ++ u).length).take s.length = initialSegment b s.length := by
    simpa using initialSegment_take b (m := s.length) (n := (s ++ u).length) (by simp)
  rw [hinit] at htake
  simpa using htake

/-- Equality of long initial segments implies equality of shorter initial
segments. -/
theorem initialSegment_eq_of_length_le {b c : ℕ → ℕ} {m n : ℕ}
    (h : initialSegment b n = initialSegment c n) (hmn : m ≤ n) :
    initialSegment b m = initialSegment c m := by
  have htake := congrArg (fun l : Node => l.take m) h
  simpa [initialSegment_take b hmn, initialSegment_take c hmn] using htake

/-- Equality of initial segments gives equality of individual coordinates
below their common length. -/
theorem apply_eq_of_initialSegment_eq {b c : ℕ → ℕ} {n i : ℕ}
    (h : initialSegment b n = initialSegment c n) (hi : i < n) :
    b i = c i := by
  have hget := congrArg (fun l : Node => l[i]?) h
  simpa [initialSegment, hi] using hget

/-- For `Cᶜ = range f`, the standard Kechris tree of finite attempts to solve
`f y = x`. A node `s` says that some `y` extending `s` has `f y` agreeing with
`x` through level `|s|`. -/
noncomputable def analyticPreimageTreeSet
    (f : (ℕ → ℕ) → (ℕ → ℕ)) (x : ℕ → ℕ) : Set Node :=
  {s | ∃ y : ℕ → ℕ,
    initialSegment y s.length = s ∧
    initialSegment (f y) s.length = initialSegment x s.length}

/-- The analytic-preimage tree is a tree. This is the standard Kechris
construction used to prove hardness of well-founded trees. -/
theorem analyticPreimageTree_isTree
    (f : (ℕ → ℕ) → (ℕ → ℕ)) (x : ℕ → ℕ) :
    IsTree (analyticPreimageTreeSet f x) := by
  constructor
  · refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp [root, initialSegment]
  · intro s t hst ht
    rcases ht with ⟨y, hyt, hfyt⟩
    refine ⟨y, ?_, ?_⟩
    · exact initialSegment_eq_of_prefix hst hyt
    · exact initialSegment_eq_of_length_le hfyt (prefix_length_le hst)

/-- Bundled tree form of the Kechris analytic-preimage tree. -/
noncomputable def analyticPreimageTree
    (f : (ℕ → ℕ) → (ℕ → ℕ)) (x : ℕ → ℕ) : Tree :=
  ⟨analyticPreimageTreeSet f x, analyticPreimageTree_isTree f x⟩

/-- Initial-segment maps from Baire space to finite nodes are continuous in
the discrete topology on nodes. -/
theorem initialSegment_continuous (k : ℕ) :
    (letI : TopologicalSpace Node := ⊥
     Continuous (fun x : ℕ → ℕ => initialSegment x k)) := by
  let : TopologicalSpace Node := ⊥
  have : DiscreteTopology Node := ⟨rfl⟩
  have hres : Continuous (fun x : ℕ → ℕ => fun i : Fin k => x i) := by
    exact continuous_pi fun i => continuous_apply (i : ℕ)
  have hofFn : Continuous (fun g : Fin k → ℕ => List.ofFn g) := by
    exact continuous_of_discreteTopology
  exact hofFn.comp hres

/-- Continuity of the analytic-preimage tree map in the standard tree
topology. -/
theorem analyticPreimageTree_continuous (f : (ℕ → ℕ) → (ℕ → ℕ)) :
    (letI : TopologicalSpace Tree := treeStandardTopology
     Continuous (analyticPreimageTree f)) := by
  let : TopologicalSpace Tree := treeStandardTopology
  rw [continuous_induced_rng]
  apply continuous_pi
  intro n
  cases hdecode : Encodable.decode₂ Node n with
  | none =>
      simpa [treeCharacteristicCode, hdecode] using
        (continuous_const : Continuous fun _ : ℕ → ℕ => 0)
  | some s =>
      classical
      let : TopologicalSpace Node := ⊥
      have : DiscreteTopology Node := ⟨rfl⟩
      let P : Node → Prop := fun a =>
        ∃ y : ℕ → ℕ, initialSegment y s.length = s ∧ initialSegment (f y) s.length = a
      have hdisc : Continuous (fun a : Node => if P a then 1 else 0) := by
        exact continuous_of_discreteTopology
      have hcomp :
          Continuous (fun x : ℕ → ℕ => if P (initialSegment x s.length) then 1 else 0) := by
        exact hdisc.comp (initialSegment_continuous s.length)
      simp only [Function.comp_apply, treeCharacteristicCode, hdecode,
        analyticPreimageTree, analyticPreimageTreeSet, Set.mem_ofPred_eq]
      change Continuous (fun x : ℕ → ℕ =>
        if P (initialSegment x s.length) then 1 else 0)
      exact hcomp

/-- Continuity of `f` gives a finite initial-segment control for each output
coordinate, the cylinder argument used in the Kechris reduction. -/
theorem exists_initialSegment_control_of_continuous_apply
    {f : (ℕ → ℕ) → (ℕ → ℕ)} (hf : Continuous f) (b : ℕ → ℕ) (i : ℕ) :
    ∃ N : ℕ, ∀ y : ℕ → ℕ,
      initialSegment y N = initialSegment b N → f y i = f b i := by
  have hcoord : Continuous (fun y : ℕ → ℕ => f y i) := (continuous_apply i).comp hf
  have hopen : IsOpen {y : ℕ → ℕ | f y i = f b i} := by
    simpa only [Set.preimage_ofPred_eq] using
      IsOpen.preimage hcoord (isOpen_discrete ({m : ℕ | m = f b i}))
  have hbmem : b ∈ {y : ℕ → ℕ | f y i = f b i} := rfl
  rcases isOpen_pi_iff.mp hopen b hbmem with ⟨I, u, hu, hsub⟩
  refine ⟨I.sup id + 1, ?_⟩
  intro y hy
  apply hsub
  intro j hj
  have hjlt : j < I.sup id + 1 := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  have hyj : y j = b j := apply_eq_of_initialSegment_eq hy hjlt
  rw [hyj]
  exact (hu j hj).2

/-- The analytic-preimage tree has a branch exactly when `x` lies in the
range of the continuous map `f`. -/
theorem analyticPreimageTree_hasBranch_iff_range
    {f : (ℕ → ℕ) → (ℕ → ℕ)} (hf : Continuous f) (x : ℕ → ℕ) :
    (∃ b : ℕ → ℕ, IsBranch (analyticPreimageTree f x : Set Node) b) ↔
      x ∈ Set.range f := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    funext i
    rcases exists_initialSegment_control_of_continuous_apply hf b i with ⟨N, hN⟩
    let k : ℕ := max (i + 1) N
    have hi_lt_k : i < k := by
      exact lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
    have hN_le_k : N ≤ k := le_max_right _ _
    have hk := hb k
    change initialSegment b k ∈ analyticPreimageTreeSet f x at hk
    rcases hk with ⟨y, hyb, hfx⟩
    have hyb' : initialSegment y k = initialSegment b k := by
      simpa [initialSegment] using hyb
    have hfx' : initialSegment (f y) k = initialSegment x k := by
      simpa [initialSegment] using hfx
    have hyN : initialSegment y N = initialSegment b N :=
      initialSegment_eq_of_length_le hyb' hN_le_k
    have hfyb : f y i = f b i := hN y hyN
    have hfyx : f y i = x i := apply_eq_of_initialSegment_eq hfx' hi_lt_k
    exact hfyb.symm.trans hfyx
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    intro k
    change initialSegment y k ∈ analyticPreimageTreeSet f x
    refine ⟨y, ?_, ?_⟩
    · simp [initialSegment]
    · simp [hy, initialSegment]

/-- Therefore the analytic-preimage tree is well-founded exactly when `x` is
not in the range of `f`. -/
theorem analyticPreimageTree_wellFounded_iff_not_mem_range
    {f : (ℕ → ℕ) → (ℕ → ℕ)} (hf : Continuous f) (x : ℕ → ℕ) :
    WellFoundedTree (analyticPreimageTree f x : Set Node) ↔ x ∉ Set.range f := by
  rw [WellFoundedTree]
  constructor
  · intro hWF hx
    exact hWF ((analyticPreimageTree_hasBranch_iff_range hf x).2 hx)
  · intro hnotRange hbranch
    exact hnotRange ((analyticPreimageTree_hasBranch_iff_range hf x).1 hbranch)

/-- Standard Kechris theorem: well-founded trees are hard for coanalytic subsets
of Baire space under continuous reductions. -/
theorem wellFoundedTrees_pi11Hard_standard :
    @Pi11Hard Tree treeStandardTopology
      {T : Tree | WellFoundedTree (T : Set Node)} := by
  let : TopologicalSpace Tree := treeStandardTopology
  intro C hC
  rw [CoanalyticSet, MeasureTheory.AnalyticSet] at hC
  rcases hC with hEmpty | ⟨f, hf_continuous, hRange⟩
  · refine ⟨fun _ => singletonRootTree, continuous_const, ?_⟩
    intro x
    constructor
    · intro _hx
      exact singletonRootTree_wellFounded
    · intro _hWF
      by_contra hxC
      have hxCompl : x ∈ Cᶜ := hxC
      simp [hEmpty] at hxCompl
  · refine ⟨analyticPreimageTree f, analyticPreimageTree_continuous f, ?_⟩
    intro x
    change x ∈ C ↔ WellFoundedTree (analyticPreimageTree f x : Set Node)
    rw [analyticPreimageTree_wellFounded_iff_not_mem_range hf_continuous x]
    constructor
    · intro hxC hxRange
      have hxCompl : x ∈ Cᶜ := by
        simpa [hRange] using hxRange
      exact hxCompl hxC
    · intro hxNotRange
      by_contra hxC
      apply hxNotRange
      have hxCompl : x ∈ Cᶜ := hxC
      simpa [hRange] using hxCompl

end WeightedTree

end DSTBL3

/-- The starter executable still prints this value. -/
def hello := "world"
