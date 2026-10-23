import ThmBC.Upper.Reduction

/-!
# The upper complete coanalytic example — completion

This file packages the upper construction in intrinsic Polish spaces and proves the
final Pi11-completeness theorem from Section 7 of the paper.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

open DSTBL3.WeightedTree
open LowerComplete

namespace UpperComplete

/-- The root-zero space as a bundled vector sublattice of `Z_ℝ`. -/
noncomputable abbrev yVectorSublattice : VectorSublattice (ZElement ℝ) :=
  { carrier := {x : ZElement ℝ | (x : V ℝ) root = 0}
    zero_mem' := by rfl
    add_mem' := by
      intro x y hx hy
      change (x : V ℝ) root + (y : V ℝ) root = 0
      rw [hx, hy, add_zero]
    smul_mem' := by
      intro a x hx
      change a * (x : V ℝ) root = 0
      rw [hx, mul_zero]
    sup_mem' := by
      intro x y hx hy
      change (x : V ℝ) root ⊔ (y : V ℝ) root = 0
      rw [hx, hy, sup_idem] }

/-- The root-zero lattice `Y`, intrinsically represented as a vector-sublattice
subtype of `Z_ℝ`. -/
abbrev YElement : Type :=
  yVectorSublattice.toSubmodule

instance : Coe YElement (V ℝ) where
  coe x := (x.1 : V ℝ)

noncomputable instance yElementLattice : Lattice YElement :=
  VectorSublattice.instLatticeSubtype yVectorSublattice

instance yElementIsOrderedAddMonoid : IsOrderedAddMonoid YElement :=
  VectorSublattice.instIsOrderedAddMonoidSubtype yVectorSublattice

instance yElementPosSMulMono : PosSMulMono ℝ YElement :=
  VectorSublattice.instPosSMulMonoSubtype yVectorSublattice

noncomputable instance yElementVectorLattice : VectorLattice YElement :=
  VectorSublattice.instVectorLatticeSubtype yVectorSublattice

noncomputable instance yElementNormedVectorLattice : NormedVectorLattice YElement :=
  VectorSublattice.instNormedVectorLatticeSubtype yVectorSublattice

/-- Intrinsic `Y`-elements are exactly elements of the ambient set `Y`. -/
theorem yElement_mem_Y (x : YElement) : (x : V ℝ) ∈ Y :=
  ⟨x.1.2, x.2⟩

/-- The root-zero condition is closed in the weighted-norm topology on `Z_ℝ`. -/
theorem yElement_rootClosed :
    IsClosed {x : ZElement ℝ | (x : V ℝ) root = 0} := by
  exact isClosed_eq (zElement_coordinate_continuous (E := ℝ) root) continuous_const

noncomputable instance yElementCompleteSpace : CompleteSpace YElement := by
  change CompleteSpace {x : ZElement ℝ // (x : V ℝ) root = 0}
  exact yElement_rootClosed.completeSpace_coe

/-- The intrinsic space `Y` is Polish as a closed subspace of `Z_ℝ`. -/
noncomputable instance yElementPolishSpace : PolishSpace YElement := by
  change PolishSpace {x : ZElement ℝ // (x : V ℝ) root = 0}
  exact yElement_rootClosed.polishSpace

/-- With its inherited norm and pointwise order, `Y` is intrinsically a
separable Banach lattice. -/
noncomputable instance yElementBanachLattice : BanachLattice YElement :=
  BanachLattice.mk

/-- The zero element of the intrinsic `Y` space. -/
noncomputable def zeroYElement : YElement :=
  ⟨(zeroZElement : ZElement ℝ), by
    change (0 : V ℝ) root = 0
    rfl⟩

/-- The Section 7 target sequence space represented intrinsically as `Y^ℕ`. -/
abbrev YSequence : Type :=
  ℕ → YElement

/-- The product Polish topology on sequences in `Y`. -/
noncomputable instance ySequencePolishSpace : PolishSpace YSequence := by
  infer_instance

/-- Forget that a sequence is intrinsically `Y`-valued. -/
def ySequenceToAmbient (u : YSequence) : ℕ → V ℝ :=
  fun n => (u n : V ℝ)

/-- `Y^{\uparrow\infty}` as a predicate on the intrinsic Polish sequence
space `Y^ℕ`. -/
def YUpwardUnboundedY (u : YSequence) : Prop :=
  YUpwardUnbounded (ySequenceToAmbient u)

/-- The zero intrinsic `Y`-sequence. -/
noncomputable def zeroYSequence : YSequence :=
  fun _ => zeroYElement

/-- Evaluation at a node is continuous on the intrinsic `Y` space. -/
theorem yElement_coordinate_continuous (s : Node) :
    Continuous (fun x : YElement => (x : V ℝ) s) :=
  (zElement_coordinate_continuous (E := ℝ) s).comp continuous_subtype_val

/-- A fixed coordinate of a sequence in `Y^ℕ`, evaluated at a tree node, is
continuous. -/
theorem ySequence_coordinate_continuous (m : ℕ) (s : Node) :
    Continuous (fun u : YSequence => (ySequenceToAmbient u m) s) :=
  (yElement_coordinate_continuous s).comp (continuous_apply m)

/-- Failure of coordinatewise positivity is analytic on `Y^ℕ`. -/
theorem badNonnegativeY_analytic :
    MeasureTheory.AnalyticSet
      {u : YSequence | ∃ m : ℕ, ∃ s : Node, ¬ 0 ≤ (ySequenceToAmbient u m) s} := by
  let A : ℕ × Node → Set YSequence :=
    fun p => {u : YSequence | ¬ 0 ≤ (ySequenceToAmbient u p.1) p.2}
  have hA : ∀ p : ℕ × Node, MeasureTheory.AnalyticSet (A p) := by
    intro p
    have hclosed : IsClosed {u : YSequence | 0 ≤ (ySequenceToAmbient u p.1) p.2} := by
      exact isClosed_le continuous_const (ySequence_coordinate_continuous p.1 p.2)
    have hopen : IsOpen (A p) := by
      simpa [A, Set.compl_ofPred] using hclosed.isOpen_compl
    exact analyticSet_of_isOpen hopen
  have hUnion : MeasureTheory.AnalyticSet (⋃ p : ℕ × Node, A p) :=
    MeasureTheory.AnalyticSet.iUnion hA
  convert hUnion using 1
  ext u
  simp [A]

/-- Failure of coordinatewise increase is analytic on `Y^ℕ`. -/
theorem badIncreasingY_analytic :
    MeasureTheory.AnalyticSet
      {u : YSequence | ∃ m : ℕ, ∃ s : Node,
        ¬ (ySequenceToAmbient u m) s ≤ (ySequenceToAmbient u (m + 1)) s} := by
  let A : ℕ × Node → Set YSequence :=
    fun p => {u : YSequence |
      ¬ (ySequenceToAmbient u p.1) p.2 ≤ (ySequenceToAmbient u (p.1 + 1)) p.2}
  have hA : ∀ p : ℕ × Node, MeasureTheory.AnalyticSet (A p) := by
    intro p
    have hclosed : IsClosed
        {u : YSequence |
          (ySequenceToAmbient u p.1) p.2 ≤ (ySequenceToAmbient u (p.1 + 1)) p.2} := by
      exact isClosed_le (ySequence_coordinate_continuous p.1 p.2)
        (ySequence_coordinate_continuous (p.1 + 1) p.2)
    have hopen : IsOpen (A p) := by
      simpa [A, Set.compl_ofPred] using hclosed.isOpen_compl
    exact analyticSet_of_isOpen hopen
  have hUnion : MeasureTheory.AnalyticSet (⋃ p : ℕ × Node, A p) :=
    MeasureTheory.AnalyticSet.iUnion hA
  convert hUnion using 1
  ext u
  simp [A]

/-- Non-positivity/increase of a sequence in `Y^ℕ` is analytic. -/
theorem notPositiveIncreasingY_analytic :
    MeasureTheory.AnalyticSet
      {u : YSequence | ¬ IsPositiveIncreasing (ySequenceToAmbient u)} := by
  have hbad :=
    analyticSet_union badNonnegativeY_analytic badIncreasingY_analytic
  have hEq :
      {u : YSequence | ¬ IsPositiveIncreasing (ySequenceToAmbient u)} =
        {u : YSequence | ∃ m : ℕ, ∃ s : Node,
          ¬ 0 ≤ (ySequenceToAmbient u m) s} ∪
        {u : YSequence | ∃ m : ℕ, ∃ s : Node,
          ¬ (ySequenceToAmbient u m) s ≤ (ySequenceToAmbient u (m + 1)) s} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hnonneg :
          ∀ m : ℕ, CoordinatewiseNonnegative (ySequenceToAmbient u m)
      · right
        have hinc :
            ¬ ∀ m : ℕ, CoordinatewiseLE (ySequenceToAmbient u m)
              (ySequenceToAmbient u (m + 1)) := by
          intro hinc
          exact h ⟨hnonneg, hinc⟩
        push Not at hinc
        rcases hinc with ⟨m, hm⟩
        rw [CoordinatewiseLE] at hm
        push Not at hm
        rcases hm with ⟨s, hs⟩
        exact ⟨m, s, not_le_of_gt hs⟩
      · left
        push Not at hnonneg
        rcases hnonneg with ⟨m, hm⟩
        rw [CoordinatewiseNonnegative] at hm
        push Not at hm
        rcases hm with ⟨s, hs⟩
        exact ⟨m, s, not_le_of_gt hs⟩
    · intro h hpi
      rcases h with hnon | hinc
      · rcases hnon with ⟨m, s, hs⟩
        exact hs (hpi.1 m s)
      · rcases hinc with ⟨m, s, hs⟩
        exact hs (hpi.2 m s)
  rw [hEq]
  exact hbad

/-- The closed relation saying that the first component is an order upper bound
for the intrinsic `Y`-sequence in the second component. -/
def upperBoundRelationY : Set (YElement × YSequence) :=
  {p | ∀ m : ℕ, CoordinatewiseLE (ySequenceToAmbient p.2 m) (p.1 : V ℝ)}

/-- The intrinsic upper-bound relation is closed. -/
theorem upperBoundRelationY_isClosed :
    IsClosed upperBoundRelationY := by
  have hEq :
      upperBoundRelationY =
        ⋂ q : ℕ × Node,
          {p : YElement × YSequence |
            (ySequenceToAmbient p.2 q.1) q.2 ≤ (p.1 : V ℝ) q.2} := by
    ext p
    simp [upperBoundRelationY, CoordinatewiseLE]
  rw [hEq]
  apply isClosed_iInter
  intro q
  exact isClosed_le
    ((ySequence_coordinate_continuous q.1 q.2).comp continuous_snd)
    ((yElement_coordinate_continuous q.2).comp continuous_fst)

/-- Having an order upper bound in `Y` is analytic on `Y^ℕ`. -/
theorem hasUpperBoundY_analytic :
    MeasureTheory.AnalyticSet
      {u : YSequence |
        ∃ y : YElement,
          ∀ m : ℕ, CoordinatewiseLE (ySequenceToAmbient u m) (y : V ℝ)} := by
  let B : Set YSequence := Prod.snd '' upperBoundRelationY
  have hB : MeasureTheory.AnalyticSet B :=
    upperBoundRelationY_isClosed.analyticSet.image_of_continuous continuous_snd
  convert hB using 1
  ext u
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(y, u), hy, rfl⟩
  · intro hu
    rcases hu with ⟨p, hp, hpu⟩
    rcases p with ⟨y, v⟩
    simp at hpu
    subst hpu
    exact ⟨y, hp⟩

/-- The intrinsic upper-unbounded set is coanalytic in `Y^ℕ`. -/
theorem yUpwardUnboundedY_coanalytic :
    @CoanalyticSet YSequence inferInstance {u : YSequence | YUpwardUnboundedY u} := by
  rw [CoanalyticSet]
  have hcompl :
      ({u : YSequence | YUpwardUnboundedY u}ᶜ : Set YSequence) =
        {u : YSequence | ¬ IsPositiveIncreasing (ySequenceToAmbient u)} ∪
          {u : YSequence |
            ∃ y : YElement,
              ∀ m : ℕ, CoordinatewiseLE (ySequenceToAmbient u m) (y : V ℝ)} := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hu
      have hYmem : ∀ m : ℕ, ySequenceToAmbient u m ∈ Y :=
        fun m => yElement_mem_Y (u m)
      have hu' :
          ¬ (IsPositiveIncreasing (ySequenceToAmbient u) ∧
            ¬ ∃ y : V ℝ, IsOrderUpperBoundInY y (ySequenceToAmbient u)) := by
        intro h
        exact hu ⟨hYmem, h.1, h.2⟩
      by_cases hpi : IsPositiveIncreasing (ySequenceToAmbient u)
      · right
        have hex : ∃ y : V ℝ, IsOrderUpperBoundInY y (ySequenceToAmbient u) := by
          by_contra hno
          exact hu' ⟨hpi, hno⟩
        rcases hex with ⟨y, hyY, hyle⟩
        exact ⟨⟨⟨y, hyY.1⟩, hyY.2⟩, hyle⟩
      · left
        exact hpi
    · intro h hu
      rcases h with hbad | ⟨y, hyle⟩
      · exact hbad hu.2.1
      · exact hu.2.2 ⟨(y : V ℝ), yElement_mem_Y y, hyle⟩
  rw [hcompl]
  exact analyticSet_union notPositiveIncreasingY_analytic hasUpperBoundY_analytic

/-- The upper reduction map with codomain the intrinsic sequence space `Y^ℕ`. -/
noncomputable def phiUpperY (T : Tree) : YSequence :=
  fun m =>
    let hY := (phi_upper_increasing_template T).1 m
    ⟨⟨phiUpper T m, hY.1⟩, hY.2⟩

/-- Forgetting the intrinsic codomain of `phiUpperY` recovers `phiUpper`. -/
theorem ySequenceToAmbient_phiUpperY (T : Tree) :
    ySequenceToAmbient (phiUpperY T) = phiUpper T := by
  rfl

/-- The upper reduction map is continuous into the intrinsic Polish target
space `Y^ℕ`. -/
theorem phiUpperY_continuous :
    @Continuous Tree YSequence treeStandardTopology inferInstance phiUpperY := by
  let : TopologicalSpace Tree := treeStandardTopology
  apply continuous_pi
  intro m
  have hcontZ :
      @Continuous Tree (ZElement ℝ) treeStandardTopology inferInstance
        (fun T : Tree =>
          (⟨phiUpper T m, ((phi_upper_increasing_template T).1 m).1⟩ : ZElement ℝ)) :=
    treeToWeightedContinuous_zElement_continuous (phi_upper_continuous_template m)
      (fun T => ((phi_upper_increasing_template T).1 m).1)
  simpa [phiUpperY] using
    (Continuous.subtype_mk hcontZ
      (fun T : Tree => ((phi_upper_increasing_template T).1 m).2))

/-- The intrinsic `Y`-sequence version of the upper tree reduction is
`Π¹₁`-complete. -/
theorem upper_pi11CompleteY_of_tree_reduction :
    @Pi11Complete YSequence inferInstance inferInstance
      (fun u : YSequence => YUpwardUnboundedY u) := by
  let : TopologicalSpace Tree := treeStandardTopology
  let : PolishSpace Tree := treeStandardPolishSpace
  exact DSTBL3.pi11CompleteSet_of_complete_reduction
    (B := {T : Tree | WellFoundedTree (T : Set Node)})
    (A := {u : YSequence | YUpwardUnboundedY u})
    ⟨wellFoundedTrees_coanalytic_standard, wellFoundedTrees_pi11Hard_standard⟩
    yUpwardUnboundedY_coanalytic
    ⟨phiUpperY, phiUpperY_continuous, by
      intro T
      simpa [YUpwardUnboundedY, ySequenceToAmbient_phiUpperY] using
        upper_reduction_template T⟩

/-- A bundled witness for the final theorem of Section 7. -/
structure UpperCompleteWitness where
  [banachLattice : BanachLattice YElement]
  [separableSpace : TopologicalSpace.SeparableSpace YElement]
  [sequenceTopology : TopologicalSpace YSequence]
  [sequencePolish : PolishSpace YSequence]
  complete : @Pi11Complete YSequence sequenceTopology sequencePolish
    (fun u : YSequence => YUpwardUnboundedY u)

/-- Theorem `upper-complete`: there is a separable Banach lattice `Y` for which
`Y^{\uparrow\infty}` is `Π¹₁`-complete.  This is Theorem C from the
introduction and Theorem `upper-complete` in Section 7; it packages the
intrinsic separable Banach lattice `Y`, the continuous reduction `Φ`, and the
well-founded-tree equivalence above. -/
theorem upper_complete_template : Nonempty UpperCompleteWitness := by
  let : TopologicalSpace YSequence := inferInstance
  let : PolishSpace YSequence := inferInstance
  exact ⟨
    { complete := upper_pi11CompleteY_of_tree_reduction }⟩

end UpperComplete
end WeightedTree
end DSTBL3
