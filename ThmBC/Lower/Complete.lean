import ThmBC.Lower.Topology
import BanLat.Examples.Lp.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The lower construction — descriptive-set-theoretic completion

This file proves coanalyticity of the target predicate and packages the continuous
tree reduction into the final Pi11-completeness theorem.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace DSTBL3
namespace WeightedTree
namespace LowerComplete

open DSTBL3.WeightedTree

universe u

/-- The paper's coefficient lattice `L₁[0,1]`, realized on mathlib's unit
interval with its probability measure. -/
noncomputable abbrev PaperL1 :=
  MeasureTheory.Lp ℝ (1 : ENNReal) (volume : MeasureTheory.Measure unitInterval)

instance paperL1ExponentFinite : Fact ((1 : ENNReal) ≠ ∞) := ⟨by norm_num⟩

/-- The normalized constant-one function in `L₁[0,1]`. -/
noncomputable def paperL1Unit : PaperL1 :=
  MeasureTheory.Lp.const (1 : ENNReal) (volume : MeasureTheory.Measure unitInterval) (1 : ℝ)

theorem paperL1Unit_nonnegative : 0 ≤ paperL1Unit := by
  change 0 ≤ MeasureTheory.Lp.const (1 : ENNReal)
    (volume : MeasureTheory.Measure unitInterval) (1 : ℝ)
  rw [← MeasureTheory.Lp.coeFn_nonneg]
  filter_upwards [MeasureTheory.Lp.coeFn_const (p := (1 : ENNReal))
      (μ := (volume : MeasureTheory.Measure unitInterval)) (c := (1 : ℝ))] with x hx
  rw [hx]
  norm_num

theorem paperL1Unit_norm : ‖paperL1Unit‖ = 1 := by
  rw [paperL1Unit, MeasureTheory.Lp.norm_const']
  · norm_num
  · norm_num
  · norm_num

/-- Failure of coordinatewise positivity is analytic. -/
theorem badNonnegativeZ_analytic {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    MeasureTheory.AnalyticSet
      {u : ZSequence E | ∃ m : ℕ, ∃ s : Node, ¬ 0 ≤ (zSequenceToAmbient u m) s} := by
  let A : ℕ × Node → Set (ZSequence E) :=
    fun p => {u : ZSequence E | ¬ 0 ≤ (zSequenceToAmbient u p.1) p.2}
  have hA : ∀ p : ℕ × Node, MeasureTheory.AnalyticSet (A p) := by
    intro p
    have hclosed : IsClosed {u : ZSequence E | 0 ≤ (zSequenceToAmbient u p.1) p.2} := by
      exact isClosed_le continuous_const (zSequence_coordinate_continuous p.1 p.2)
    have hopen : IsOpen (A p) := by
      simpa [A, Set.compl_ofPred] using hclosed.isOpen_compl
    exact analyticSet_of_isOpen hopen
  have hUnion : MeasureTheory.AnalyticSet (⋃ p : ℕ × Node, A p) :=
    MeasureTheory.AnalyticSet.iUnion hA
  convert hUnion using 1
  ext u
  simp [A]

/-- Failure of coordinatewise decrease is analytic. -/
theorem badDecreasingZ_analytic {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    MeasureTheory.AnalyticSet
      {u : ZSequence E | ∃ m : ℕ, ∃ s : Node,
        ¬ (zSequenceToAmbient u (m + 1)) s ≤ (zSequenceToAmbient u m) s} := by
  let A : ℕ × Node → Set (ZSequence E) :=
    fun p => {u : ZSequence E |
      ¬ (zSequenceToAmbient u (p.1 + 1)) p.2 ≤ (zSequenceToAmbient u p.1) p.2}
  have hA : ∀ p : ℕ × Node, MeasureTheory.AnalyticSet (A p) := by
    intro p
    have hclosed : IsClosed
        {u : ZSequence E |
          (zSequenceToAmbient u (p.1 + 1)) p.2 ≤ (zSequenceToAmbient u p.1) p.2} := by
      exact isClosed_le (zSequence_coordinate_continuous (p.1 + 1) p.2)
        (zSequence_coordinate_continuous p.1 p.2)
    have hopen : IsOpen (A p) := by
      simpa [A, Set.compl_ofPred] using hclosed.isOpen_compl
    exact analyticSet_of_isOpen hopen
  have hUnion : MeasureTheory.AnalyticSet (⋃ p : ℕ × Node, A p) :=
    MeasureTheory.AnalyticSet.iUnion hA
  convert hUnion using 1
  ext u
  simp [A]

/-- Non-positivity/decrease of a sequence in `Z_E` is an analytic condition. -/
theorem notPositiveDecreasingZ_analytic {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    MeasureTheory.AnalyticSet
      {u : ZSequence E | ¬ IsPositiveDecreasing (zSequenceToAmbient u)} := by
  have hbad :=
    analyticSet_union (badNonnegativeZ_analytic (E := E)) (badDecreasingZ_analytic (E := E))
  have hEq :
      {u : ZSequence E | ¬ IsPositiveDecreasing (zSequenceToAmbient u)} =
        {u : ZSequence E | ∃ m : ℕ, ∃ s : Node,
          ¬ 0 ≤ (zSequenceToAmbient u m) s} ∪
        {u : ZSequence E | ∃ m : ℕ, ∃ s : Node,
          ¬ (zSequenceToAmbient u (m + 1)) s ≤ (zSequenceToAmbient u m) s} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hnonneg :
          ∀ m : ℕ, CoordinatewiseNonnegative (zSequenceToAmbient u m)
      · right
        have hdec :
            ¬ ∀ m : ℕ, CoordinatewiseLE (zSequenceToAmbient u (m + 1))
              (zSequenceToAmbient u m) := by
          intro hdec
          exact h ⟨hnonneg, hdec⟩
        push Not at hdec
        rcases hdec with ⟨m, hm⟩
        rw [CoordinatewiseLE] at hm
        push Not at hm
        exact ⟨m, hm⟩
      · left
        push Not at hnonneg
        rcases hnonneg with ⟨m, hm⟩
        rw [CoordinatewiseNonnegative] at hm
        push Not at hm
        exact ⟨m, hm⟩
    · intro h hpd
      rcases h with hnon | hdec
      · rcases hnon with ⟨m, s, hs⟩
        exact hs (hpd.1 m s)
      · rcases hdec with ⟨m, s, hs⟩
        exact hs (hpd.2 m s)
  rw [hEq]
  exact hbad

/-- Closed slices of the positive-lower-bound relation, with the lower bound
kept away from zero by `1 / (k + 1)`. -/
def lowerBoundSliceZ {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    (k : ℕ) : Set (ZElement E × ZSequence E) :=
  {p | CoordinatewiseNonnegative (p.1 : V E) ∧
    1 / ((k : ℝ) + 1) ≤ dist p.1 (zeroZElement : ZElement E) ∧
      ∀ m : ℕ, CoordinatewiseLE (p.1 : V E) (zSequenceToAmbient p.2 m)}

/-- Each positive-lower-bound slice is closed. -/
theorem lowerBoundSliceZ_isClosed {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] (k : ℕ) :
    IsClosed (lowerBoundSliceZ (E := E) k) := by
  have hnonneg : IsClosed
      {p : ZElement E × ZSequence E | CoordinatewiseNonnegative (p.1 : V E)} := by
    have hEq :
        {p : ZElement E × ZSequence E | CoordinatewiseNonnegative (p.1 : V E)} =
          ⋂ s : Node, {p : ZElement E × ZSequence E | 0 ≤ (p.1 : V E) s} := by
      ext p
      simp [CoordinatewiseNonnegative]
    rw [hEq]
    apply isClosed_iInter
    intro s
    exact isClosed_le continuous_const
      ((zElement_coordinate_continuous (E := E) s).comp continuous_fst)
  have hnorm : IsClosed
      {p : ZElement E × ZSequence E |
        1 / ((k : ℝ) + 1) ≤ dist p.1 (zeroZElement : ZElement E)} := by
    exact isClosed_le continuous_const
      ((continuous_fst.dist continuous_const))
  have hle : IsClosed
      {p : ZElement E × ZSequence E |
        ∀ m : ℕ, CoordinatewiseLE (p.1 : V E) (zSequenceToAmbient p.2 m)} := by
    have hEq :
        {p : ZElement E × ZSequence E |
          ∀ m : ℕ, CoordinatewiseLE (p.1 : V E) (zSequenceToAmbient p.2 m)} =
            ⋂ q : ℕ × Node,
              {p : ZElement E × ZSequence E |
                (p.1 : V E) q.2 ≤ (zSequenceToAmbient p.2 q.1) q.2} := by
      ext p
      simp [CoordinatewiseLE]
    rw [hEq]
    apply isClosed_iInter
    intro q
    exact isClosed_le
      ((zElement_coordinate_continuous (E := E) q.2).comp continuous_fst)
      ((zSequence_coordinate_continuous (E := E) q.1 q.2).comp continuous_snd)
  simpa [lowerBoundSliceZ, Set.ofPred_and] using hnonneg.inter (hnorm.inter hle)

/-- Having a nonzero positive lower bound in `Z_E` is analytic. -/
theorem hasPositiveLowerBoundZ_analytic {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    MeasureTheory.AnalyticSet
      {u : ZSequence E |
        ∃ y : ZElement E,
          CoordinatewiseNonnegative (y : V E) ∧ (y : V E) ≠ 0 ∧
            ∀ m : ℕ, CoordinatewiseLE (y : V E) (zSequenceToAmbient u m)} := by
  let B : ℕ → Set (ZSequence E) :=
    fun k => Prod.snd '' lowerBoundSliceZ (E := E) k
  have hB : ∀ k : ℕ, MeasureTheory.AnalyticSet (B k) := by
    intro k
    exact (lowerBoundSliceZ_isClosed (E := E) k).analyticSet.image_of_continuous continuous_snd
  have hUnion : MeasureTheory.AnalyticSet (⋃ k : ℕ, B k) :=
    MeasureTheory.AnalyticSet.iUnion hB
  have hEq :
      (⋃ k : ℕ, B k) =
        {u : ZSequence E |
          ∃ y : ZElement E,
            CoordinatewiseNonnegative (y : V E) ∧ (y : V E) ≠ 0 ∧
              ∀ m : ℕ, CoordinatewiseLE (y : V E) (zSequenceToAmbient u m)} := by
    ext u
    constructor
    · intro hu
      rcases Set.mem_iUnion.mp hu with ⟨k, hk⟩
      rcases hk with ⟨p, hp, hpu⟩
      rcases p with ⟨y, v⟩
      simp at hpu
      subst hpu
      rcases hp with ⟨hyNonneg, hdist, hyle⟩
      refine ⟨y, hyNonneg, ?_, hyle⟩
      intro hyzero
      have hyzeroZ : y = (zeroZElement : ZElement E) := by
        apply Subtype.ext
        exact hyzero
      have hdist_zero : dist y (zeroZElement : ZElement E) = 0 := by
        simp [hyzeroZ]
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · rintro ⟨y, hyNonneg, hyne, hyle⟩
      have hyneZ : y ≠ (zeroZElement : ZElement E) := by
        intro h
        apply hyne
        exact congrArg (fun z : ZElement E => (z : V E)) h
      have hdist_pos : 0 < dist y (zeroZElement : ZElement E) := dist_pos.mpr hyneZ
      rcases exists_nat_one_div_lt hdist_pos with ⟨k, hk⟩
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      refine ⟨(y, u), ?_, rfl⟩
      exact ⟨hyNonneg, le_of_lt hk, hyle⟩
  rw [← hEq]
  exact hUnion

/-- Standard descriptive-set-theoretic fact for the intrinsic Polish target:
`X_{\downarrow 0}` is coanalytic in `(Z_E)^ℕ`. -/
theorem xDownarrowZeroZ_coanalytic {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    @CoanalyticSet (ZSequence E) inferInstance {u : ZSequence E | XDownarrowZeroZ u} := by
  rw [CoanalyticSet]
  have hcompl :
      ({u : ZSequence E | XDownarrowZeroZ u}ᶜ : Set (ZSequence E)) =
        {u : ZSequence E | ¬ IsPositiveDecreasing (zSequenceToAmbient u)} ∪
          {u : ZSequence E |
            ∃ y : ZElement E,
              CoordinatewiseNonnegative (y : V E) ∧ (y : V E) ≠ 0 ∧
                ∀ m : ℕ, CoordinatewiseLE (y : V E) (zSequenceToAmbient u m)} := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hu
      have hu' :
          ¬ (IsPositiveDecreasing (zSequenceToAmbient u) ∧
            ¬ ∃ y : V E, IsNonzeroPositiveLowerBoundInZ y (zSequenceToAmbient u)) := by
        simpa [XDownarrowZeroZ, HasInfimumZeroInZ] using hu
      by_cases hpd : IsPositiveDecreasing (zSequenceToAmbient u)
      · right
        have hex : ∃ y : V E, IsNonzeroPositiveLowerBoundInZ y (zSequenceToAmbient u) := by
          by_contra hno
          exact hu' ⟨hpd, hno⟩
        rcases hex with ⟨y, hyZ, hyNonneg, hyne, hyle⟩
        exact ⟨⟨y, hyZ⟩, hyNonneg, hyne, hyle⟩
      · left
        exact hpd
    · intro h huX
      have hpd : IsPositiveDecreasing (zSequenceToAmbient u) := huX.1
      have hzero :
          ¬ ∃ y : V E, IsNonzeroPositiveLowerBoundInZ y (zSequenceToAmbient u) := by
        simpa [HasInfimumZeroInZ] using huX.2
      rcases h with hbad | ⟨y, hyNonneg, hyne, hyle⟩
      · exact hbad hpd
      · exact hzero ⟨(y : V E), y.2, hyNonneg, hyne, hyle⟩
  rw [hcompl]
  exact analyticSet_union (notPositiveDecreasingZ_analytic (E := E))
    (hasPositiveLowerBoundZ_analytic (E := E))

/-- The standard target-side descriptive-set-theoretic data for the lower
construction.  This packages the remaining external Section 6 facts about the
chosen Polish topology on the target sequence space. -/
structure LowerSequenceSpaceStandardData {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e) where
  sequenceTopology : TopologicalSpace (ZSequence E)
  sequencePolish : @PolishSpace (ZSequence E) sequenceTopology
  xDownarrowZero_coanalytic :
    @CoanalyticSet (ZSequence E) sequenceTopology {u : ZSequence E | XDownarrowZeroZ u}
  thetaLower_continuous :
    @Continuous Tree (ZSequence E) treeStandardTopology sequenceTopology (thetaLowerZ he)

/-- Standard target-side Polish topology from Section 6.  This is the remaining
descriptive-set-theoretic input: choose a Polish topology on the ambient sequence
space for which `X_{\downarrow 0}` is coanalytic and the already-proved finite
coordinate continuity of `thetaLower` gives actual continuity. -/
theorem lowerSequenceSpace_standardTopology_exists {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    (hcontinuous : TreeToSequenceContinuous (thetaLower e)) :
    ∃ sequenceTopology : TopologicalSpace (ZSequence E),
      ∃ _ : @PolishSpace (ZSequence E) sequenceTopology,
        @CoanalyticSet (ZSequence E) sequenceTopology
            {u : ZSequence E | XDownarrowZeroZ u} ∧
          @Continuous Tree (ZSequence E) treeStandardTopology sequenceTopology (thetaLowerZ he) := by
  exact ⟨inferInstance, inferInstance, xDownarrowZeroZ_coanalytic,
    thetaLowerZ_continuous he hcontinuous⟩

/-- Standard target-side data for the lower sequence space.  The finite
coordinate control proved for `thetaLower` supplies the continuity component of
this package once the standard Polish topology on the sequence space is in
place. -/
theorem lower_sequence_space_standard_data {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (_he : UnitPositiveElement e)
    (hcontinuous : TreeToSequenceContinuous (thetaLower e)) :
    Nonempty (LowerSequenceSpaceStandardData _he) := by
  rcases lowerSequenceSpace_standardTopology_exists _he hcontinuous with
    ⟨sequenceTopology, sequencePolish, hcoanalytic, htheta_continuous⟩
  refine ⟨
    { sequenceTopology := sequenceTopology
      sequencePolish := sequencePolish
      xDownarrowZero_coanalytic := hcoanalytic
      thetaLower_continuous := htheta_continuous }⟩

/-- Standard descriptive-set-theoretic/topological data for the target sequence
space: `X_{\downarrow 0}` is coanalytic, and the finite-agreement continuity
proved for `thetaLower` is continuity for the chosen Polish topology. -/
theorem lower_sequence_space_standard_dst_data {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (_he : UnitPositiveElement e)
    (_hcontinuous : TreeToSequenceContinuous (thetaLower e)) :
    ∃ sequenceTopology : TopologicalSpace (ZSequence E),
      ∃ _ : @PolishSpace (ZSequence E) sequenceTopology,
        @CoanalyticSet (ZSequence E) sequenceTopology
            {u : ZSequence E | XDownarrowZeroZ u} ∧
          @Continuous Tree (ZSequence E) treeStandardTopology sequenceTopology (thetaLowerZ _he) := by
  rcases lower_sequence_space_standard_data _he _hcontinuous with
    ⟨⟨sequenceTopology, sequencePolish, hcoanalytic, htheta_continuous⟩⟩
  exact ⟨sequenceTopology, sequencePolish, hcoanalytic, htheta_continuous⟩

/-- The standard Section 6 sequence-space data, stated for the standard Polish
tree topology. -/
theorem lower_sequence_standard_dst_data {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (_he : UnitPositiveElement e)
    (_hcontinuous : TreeToSequenceContinuous (thetaLower e)) :
    ∃ sequenceTopology : TopologicalSpace (ZSequence E),
      ∃ _ : @PolishSpace (ZSequence E) sequenceTopology,
        @CoanalyticSet (ZSequence E) sequenceTopology
            {u : ZSequence E | XDownarrowZeroZ u} ∧
          @Continuous Tree (ZSequence E) treeStandardTopology sequenceTopology (thetaLowerZ _he) := by
  exact lower_sequence_space_standard_dst_data _he _hcontinuous

/-- The standard descriptive-set-theoretic data behind Section 6: the Polish
topology on trees, the Polish topology on the target sequence space, the
`Π¹₁`-completeness of `WF`, coanalyticity of `X_{\downarrow 0}`, and the fact
that the local finite-agreement continuity predicate gives an honest continuous
map between those Polish spaces. -/
theorem lower_standard_dst_data {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (_he : UnitPositiveElement e)
    (_hcontinuous : TreeToSequenceContinuous (thetaLower e)) :
    ∃ treeTopology : TopologicalSpace Tree,
      ∃ treePolish : @PolishSpace Tree treeTopology,
        ∃ sequenceTopology : TopologicalSpace (ZSequence E),
          ∃ _ : @PolishSpace (ZSequence E) sequenceTopology,
            @Pi11Complete Tree treeTopology treePolish
                (fun T : Tree => WellFoundedTree (T : Set Node)) ∧
              @CoanalyticSet (ZSequence E) sequenceTopology
                {u : ZSequence E | XDownarrowZeroZ u} ∧
              @Continuous Tree (ZSequence E) treeTopology sequenceTopology (thetaLowerZ _he) := by
  rcases lower_sequence_standard_dst_data _he _hcontinuous with
    ⟨sequenceTopology, sequencePolish, hcoanalytic, hcontinuous'⟩
  exact ⟨treeStandardTopology, treeStandardPolishSpace, sequenceTopology, sequencePolish,
    ⟨wellFoundedTrees_coanalytic_standard, wellFoundedTrees_pi11Hard_standard⟩,
    hcoanalytic, hcontinuous'⟩

/-- Descriptive-set-theoretic transfer principle used in the final theorem. -/
theorem lower_pi11Complete_of_tree_reduction {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    (hcontinuous : TreeToSequenceContinuous (thetaLower e))
    (hreduction :
      ∀ T : Tree, WellFoundedTree (T : Set Node) ↔ XDownarrowZero (thetaLower e T)) :
    ∃ sequenceTopology : TopologicalSpace (ZSequence E),
      ∃ sequencePolish : @PolishSpace (ZSequence E) sequenceTopology,
        @Pi11Complete (ZSequence E) sequenceTopology sequencePolish
          (fun u : ZSequence E => XDownarrowZeroZ u) := by
  rcases lower_standard_dst_data he hcontinuous with
    ⟨treeTopology, treePolish, sequenceTopology, sequencePolish,
      hWFcomplete, hcoanalytic, htheta_continuous⟩
  refine ⟨sequenceTopology, sequencePolish, ?_⟩
  let : TopologicalSpace Tree := treeTopology
  let : PolishSpace Tree := treePolish
  let : TopologicalSpace (ZSequence E) := sequenceTopology
  let : PolishSpace (ZSequence E) := sequencePolish
  exact DSTBL3.pi11CompleteSet_of_complete_reduction
    (B := {T : Tree | WellFoundedTree (T : Set Node)})
    (A := {u : ZSequence E | XDownarrowZeroZ u})
    hWFcomplete hcoanalytic
    ⟨thetaLowerZ he, htheta_continuous, by
      intro T
      exact (hreduction T).trans (xDownarrowZeroZ_thetaLowerZ_iff he T).symm⟩

/-- A bundled witness for the final theorem of Section 6.  The actual Banach
lattice in the conclusion is `ZElement E`; the coefficient lattice `E` and its
instances are retained so that this construction remains inspectable. -/
structure LowerCompleteWitness where
  E : Type
  [normed : NormedAddCommGroup E]
  [lattice : Lattice E]
  [orderedAdd : IsOrderedAddMonoid E]
  [banachLattice : BanachLattice E]
  [separable : TopologicalSpace.SeparableSpace E]
  [xBanachLattice : BanachLattice (ZElement E)]
  [xSeparable : TopologicalSpace.SeparableSpace (ZElement E)]
  [sequenceTopology : TopologicalSpace (ZSequence E)]
  [sequencePolish : PolishSpace (ZSequence E)]
  complete : @Pi11Complete (ZSequence E) sequenceTopology sequencePolish
    (fun u : ZSequence E => XDownarrowZeroZ u)

attribute [instance] LowerCompleteWitness.normed LowerCompleteWitness.lattice
  LowerCompleteWitness.orderedAdd LowerCompleteWitness.banachLattice LowerCompleteWitness.separable
  LowerCompleteWitness.xBanachLattice LowerCompleteWitness.xSeparable
  LowerCompleteWitness.sequenceTopology LowerCompleteWitness.sequencePolish

/-- Theorem `lower-complete`: there is a separable Banach lattice `X` for which
`X_{\downarrow 0}` is `Π¹₁`-complete. -/
theorem lower_complete_template : Nonempty LowerCompleteWitness := by
  let e : PaperL1 := paperL1Unit
  have he : UnitPositiveElement e :=
    ⟨paperL1Unit_nonnegative, paperL1Unit_norm⟩
  have hcontinuous : TreeToSequenceContinuous (thetaLower e) :=
    (theta_lower_template he).1
  have hreduction :
      ∀ T : Tree, WellFoundedTree (T : Set Node) ↔ XDownarrowZero (thetaLower e T) := by
    intro T
    exact lower_reduction_template he T
  rcases lower_pi11Complete_of_tree_reduction he hcontinuous hreduction with
    ⟨sequenceTopology, sequencePolish, hcomplete⟩
  let : TopologicalSpace (ZSequence PaperL1) := sequenceTopology
  let : PolishSpace (ZSequence PaperL1) := sequencePolish
  exact ⟨{ E := PaperL1, complete := hcomplete }⟩

end LowerComplete
end WeightedTree
end DSTBL3
