import ThmBC.Lower.Reduction
import ThmBC.Tree.Intrinsic
import BanLat.Substructures.Sublattice

/-!
# The lower construction — topology and Polish spaces

This file proves continuity of the tree reduction and constructs the intrinsic Polish
spaces of elements of `Z_E` and their sequences.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree
namespace LowerComplete

open DSTBL3.WeightedTree

universe u

/-- A finite agreement cylinder around a tree is open in the standard tree
topology. -/
theorem treeFiniteAgreement_isOpen (T : Tree) (A : Finset Node) :
    @IsOpen Tree treeStandardTopology
      {U : Tree | ∀ s : Node, s ∈ A → (s ∈ (T : Set Node) ↔ s ∈ (U : Set Node))} := by
  let : TopologicalSpace Tree := treeStandardTopology
  have hcoord :
      ∀ s ∈ A,
        IsOpen {U : Tree | s ∈ (T : Set Node) ↔ s ∈ (U : Set Node)} := by
    intro s _hs
    have hcont :
        Continuous (fun U : Tree => treeCharacteristicCode U (Encodable.encode s)) := by
      have hcode : Continuous treeCharacteristicCode := continuous_induced_dom
      exact (continuous_apply (Encodable.encode s)).comp hcode
    have hpre :
        {U : Tree | s ∈ (T : Set Node) ↔ s ∈ (U : Set Node)} =
          (fun U : Tree => treeCharacteristicCode U (Encodable.encode s)) ⁻¹'
            {treeCharacteristicCode T (Encodable.encode s)} := by
      ext U
      by_cases hT : s ∈ (T : Set Node) <;>
        by_cases hU : s ∈ (U : Set Node) <;>
          simp [treeCharacteristicCode, hT, hU]
    rw [hpre]
    exact IsOpen.preimage hcont (isOpen_discrete _)
  have heq :
      {U : Tree | ∀ s : Node, s ∈ A → (s ∈ (T : Set Node) ↔ s ∈ (U : Set Node))} =
        ⋂ s ∈ A, {U : Tree | s ∈ (T : Set Node) ↔ s ∈ (U : Set Node)} := by
    ext U
    simp [Set.mem_iInter]
  rw [heq]
  exact isOpen_biInter_finset (s := A)
    (f := fun s : Node => {U : Tree | s ∈ (T : Set Node) ↔ s ∈ (U : Set Node)})
    hcoord

/-- Weighted finite-agreement continuity of a map into `V_E` implies ordinary
continuity of each fixed tree coordinate. -/
theorem treeToWeightedContinuous_coordinate_continuous {E : Type u}
    [NormedAddCommGroup E] {F : Tree → V E}
    (hF : TreeToWeightedContinuous F) (s : Node) :
    @Continuous Tree E treeStandardTopology inferInstance (fun T : Tree => F T s) := by
  let : TopologicalSpace Tree := treeStandardTopology
  rw [continuous_iff_continuousAt]
  intro T
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hweighted_pos : 0 < ε * weight s := mul_pos hε (weight_pos s)
  rcases hF T (ε * weight s) hweighted_pos with ⟨A, hA⟩
  let cylinder : Set Tree :=
    {U : Tree | ∀ r : Node, r ∈ A → (r ∈ (T : Set Node) ↔ r ∈ (U : Set Node))}
  have hcyl_open : IsOpen cylinder := by
    simpa [cylinder] using treeFiniteAgreement_isOpen T A
  have hT_mem : T ∈ cylinder := by
    intro r _hr
    rfl
  refine Filter.mem_of_superset (hcyl_open.mem_nhds hT_mem) ?_
  intro U hU
  have hweighted_TU : ‖F T - F U‖ < ε * weight s := hA U hU
  have hweighted_UT : ‖F U - F T‖ < ε * weight s := by
    simpa [weightedNorm_sub_rev (F T) (F U)] using hweighted_TU
  have hcoord : ‖F U s - F T s‖ ≤ ‖F U - F T‖ / weight s := by
    simpa using coordinate_norm_le_div_weight (F U - F T) s
  have hdiv : ‖F U - F T‖ / weight s < ε :=
    (div_lt_iff₀ (weight_pos s)).mpr hweighted_UT
  calc
    dist (F U s) (F T s) = ‖F U s - F T s‖ := dist_eq_norm _ _
    _ ≤ ‖F U - F T‖ / weight s := hcoord
    _ < ε := hdiv

/-- Coordinate coding for the target sequence space used in the lower
construction.  It records the `Node`-coordinates of each term of the sequence. -/
def lowerSequenceCoordinateCode {E : Type u} [Norm E] (u : ℕ → V E) :
    (ℕ × Node) → E :=
  fun p => u p.1 p.2

/-- The coordinate topology on the ambient lower sequence space, induced from the
countable product of the topology of `E`. -/
@[reducible] noncomputable def lowerSequenceCoordinateTopology {E : Type u}
    [Norm E] [TopologicalSpace E] : TopologicalSpace (ℕ → V E) :=
  TopologicalSpace.induced (lowerSequenceCoordinateCode (E := E))
    (inferInstance : TopologicalSpace ((ℕ × Node) → E))

/-- The finite-coordinate continuity predicate for `thetaLower` gives ordinary
continuity into the coordinate topology on the target sequence space. -/
theorem thetaLower_continuous_coordinateTopology {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (hcontinuous : TreeToSequenceContinuous (thetaLower e)) :
    @Continuous Tree (ℕ → V E) treeStandardTopology
      (lowerSequenceCoordinateTopology (E := E)) (thetaLower e) := by
  let : TopologicalSpace Tree := treeStandardTopology
  let : TopologicalSpace (ℕ → V E) := lowerSequenceCoordinateTopology (E := E)
  rw [continuous_induced_rng]
  apply continuous_pi
  intro p
  simpa [Function.comp, lowerSequenceCoordinateCode] using
    treeToWeightedContinuous_coordinate_continuous (hcontinuous p.1) p.2

/-- The closed vector sublattice `Z_E` as a bundled subobject of `V_E`. -/
noncomputable abbrev zVectorSublattice (E : Type u)
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    VectorSublattice (V E) :=
  { carrier := Z E
    zero_mem' := (Z_isVectorSubLattice (E := E)).1
    add_mem' := fun hx hy => (Z_isVectorSubLattice (E := E)).2.1 _ hx _ hy
    smul_mem' := fun a _ hx => (Z_isVectorSubLattice (E := E)).2.2.2.1 a _ hx
    sup_mem' := fun hx hy => (Z_isVectorSubLattice (E := E)).2.2.2.2.1 _ hx _ hy }

/-- The separable Banach lattice `Z_E`, intrinsically represented as the
subtype of the bundled closed vector sublattice above. -/
abbrev ZElement (E : Type u)
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] : Type u :=
  (zVectorSublattice E).toSubmodule

noncomputable instance zElementLattice {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    Lattice (ZElement E) :=
  VectorSublattice.instLatticeSubtype (zVectorSublattice E)

instance zElementIsOrderedAddMonoid {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    IsOrderedAddMonoid (ZElement E) :=
  VectorSublattice.instIsOrderedAddMonoidSubtype (zVectorSublattice E)

instance zElementPosSMulMono {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    PosSMulMono ℝ (ZElement E) :=
  VectorSublattice.instPosSMulMonoSubtype (zVectorSublattice E)

noncomputable instance zElementVectorLattice {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    VectorLattice (ZElement E) :=
  VectorSublattice.instVectorLatticeSubtype (zVectorSublattice E)

noncomputable instance zElementNormedVectorLattice {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    NormedVectorLattice (ZElement E) :=
  VectorSublattice.instNormedVectorLatticeSubtype (zVectorSublattice E)

@[simp] theorem zElement_dist_eq {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    (x y : ZElement E) : dist x y = ‖(x : V E) - (y : V E)‖ := rfl

/-- The project-level sequential completeness of `Z_E` gives the usual complete
metric-space typeclass for the associated weighted-norm metric. -/
noncomputable instance zElementCompleteSpace {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    CompleteSpace (ZElement E) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hweighted : WeightedCauchy fun n : ℕ => (u n : V E) := by
    rw [Metric.cauchySeq_iff] at hu
    intro ε hε
    rcases hu ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m n hm hn
    simpa using hN m hm n hn
  rcases Z_isCompleteForWeightedNorm
      (u := fun n : ℕ => (u n : V E))
      (by intro n; exact (u n).2) hweighted with ⟨x, hxZ, hxlim⟩
  refine ⟨⟨x, hxZ⟩, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases hxlim ε hε with ⟨N, hN⟩
  exact eventually_atTop.2 ⟨N, by
    intro n hn
    simpa using hN n hn⟩

/-- The intrinsic closed sublattice `Z_E` is a Banach lattice. -/
noncomputable instance zElementBanachLattice {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    BanachLattice (ZElement E) := BanachLattice.mk

/-- The project-level separability of `Z_E` gives the usual separability
typeclass for the associated weighted-norm metric. -/
noncomputable instance zElementSeparableSpace {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (ZElement E) := by
  rcases Z_isSeparableForWeightedNorm (E := E) with ⟨D, hDcount, hDsub, hDense⟩
  let ι : Type u := D
  have : Countable ι := hDcount.to_subtype
  let d : ι → ZElement E := fun y => ⟨y.1, hDsub y.2⟩
  refine TopologicalSpace.SeparableSpace.of_denseRange d ?_
  rw [Metric.denseRange_iff]
  intro x ε hε
  rcases hDense (x : V E) x.2 ε hε with ⟨y, hyD, hxy⟩
  exact ⟨⟨y, hyD⟩, by simpa [d] using hxy⟩

/-- The Polish space associated to the separable complete weighted-norm space
`Z_E`. -/
noncomputable instance zElementPolishSpace {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    PolishSpace (ZElement E) := by
  infer_instance

/-- The Section 6 target space when it is represented intrinsically as
sequences in `Z_E`. -/
abbrev ZSequence (E : Type u)
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] : Type u :=
  ℕ → ZElement E

/-- The product Polish topology on sequences in the Polish space `Z_E`. -/
noncomputable instance zSequencePolishSpace {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    PolishSpace (ZSequence E) := by
  infer_instance

/-- Forget that a sequence is valued in `Z_E`, viewing it as an ambient sequence
in `V_E`. -/
def zSequenceToAmbient {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    (u : ZSequence E) : ℕ → V E :=
  fun n => (u n : V E)

/-- `X_{\downarrow 0}` as a predicate on the intrinsic Polish sequence space
`(Z_E)^ℕ`. -/
def XDownarrowZeroZ {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    (u : ZSequence E) : Prop :=
  IsPositiveDecreasing (zSequenceToAmbient u) ∧ HasInfimumZeroInZ (zSequenceToAmbient u)

/-- The lower reduction map, with codomain the intrinsic `Z_E` sequence space. -/
noncomputable def thetaLowerZ {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E]
    {e : E} (he : UnitPositiveElement e) (T : Tree) : ZSequence E :=
  fun m => ⟨thetaLower e T m, ((theta_lower_template he).2 T).1 m⟩

/-- Weighted finite-agreement continuity gives ordinary continuity into the
weighted-norm Polish space `Z_E`, provided the map is `Z_E`-valued. -/
theorem treeToWeightedContinuous_zElement_continuous {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {F : Tree → V E} (hF : TreeToWeightedContinuous F) (hFZ : ∀ T : Tree, F T ∈ Z E) :
    @Continuous Tree (ZElement E) treeStandardTopology inferInstance
      (fun T : Tree => (⟨F T, hFZ T⟩ : ZElement E)) := by
  let : TopologicalSpace Tree := treeStandardTopology
  rw [continuous_iff_continuousAt]
  intro T
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  rcases hF T ε hε with ⟨A, hA⟩
  let cylinder : Set Tree :=
    {U : Tree | ∀ r : Node, r ∈ A → (r ∈ (T : Set Node) ↔ r ∈ (U : Set Node))}
  have hcyl_open : IsOpen cylinder := by
    simpa [cylinder] using treeFiniteAgreement_isOpen T A
  have hT_mem : T ∈ cylinder := by
    intro r _hr
    rfl
  refine Filter.mem_of_superset (hcyl_open.mem_nhds hT_mem) ?_
  intro U hU
  have hTU : ‖F T - F U‖ < ε := hA U hU
  have hUT : ‖F U - F T‖ < ε := by
    simpa [weightedNorm_sub_rev (F T) (F U)] using hTU
  simpa using hUT

/-- The lower reduction map is continuous when viewed as a map into the Polish
sequence space `(Z_E)^ℕ`. -/
theorem thetaLowerZ_continuous {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    (hcontinuous : TreeToSequenceContinuous (thetaLower e)) :
    @Continuous Tree (ZSequence E) treeStandardTopology inferInstance (thetaLowerZ he) := by
  let : TopologicalSpace Tree := treeStandardTopology
  apply continuous_pi
  intro m
  exact treeToWeightedContinuous_zElement_continuous (hcontinuous m)
    (fun T => ((theta_lower_template he).2 T).1 m)

/-- On the range of `thetaLowerZ`, the intrinsic `Z_E` predicate is the same as
the previous ambient predicate. -/
theorem xDownarrowZeroZ_thetaLowerZ_iff {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e) (T : Tree) :
    XDownarrowZeroZ (thetaLowerZ he T) ↔ XDownarrowZero (thetaLower e T) := by
  have hZ : ∀ m : ℕ, thetaLower e T m ∈ Z E := ((theta_lower_template he).2 T).1
  constructor
  · intro h
    exact ⟨hZ, h⟩
  · intro h
    exact h.2

/-- Open subsets of Polish spaces are analytic. -/
theorem analyticSet_of_isOpen {α : Type u} [TopologicalSpace α] [PolishSpace α]
    {s : Set α} (hs : IsOpen s) :
    MeasureTheory.AnalyticSet s := by
  simpa using (hs.analyticSet_image (f := id) continuous_id)

/-- Analytic sets are closed under binary unions. -/
theorem analyticSet_union {α : Type u} [TopologicalSpace α] {s t : Set α}
    (hs : MeasureTheory.AnalyticSet s) (ht : MeasureTheory.AnalyticSet t) :
    MeasureTheory.AnalyticSet (s ∪ t) := by
  have h :
      MeasureTheory.AnalyticSet (⋃ b : Bool, if b then s else t) :=
    MeasureTheory.AnalyticSet.iUnion (fun b => by
      cases b
      · simpa using ht
      · simpa using hs)
  convert h using 1
  ext x
  simp
  tauto

/-- The zero element of the Polish space associated to `Z_E`. -/
noncomputable def zeroZElement {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    ZElement E :=
  ⟨0, Z_isVectorSubLattice.1⟩

/-- Evaluation at a node is continuous on `Z_E` for the weighted-norm topology. -/
theorem zElement_coordinate_continuous {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    (s : Node) :
    Continuous (fun x : ZElement E => (x : V E) s) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hweighted_pos : 0 < ε * weight s := mul_pos hε (weight_pos s)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hweighted_pos) ?_
  intro y hy
  have hdist : dist y x < ε * weight s := by
    simpa [Metric.ball] using hy
  have hcoord : ‖(y : V E) s - (x : V E) s‖ ≤ dist y x / weight s := by
    simpa using coordinate_norm_le_div_weight ((y : V E) - (x : V E)) s
  have hdiv : dist y x / weight s < ε :=
    (div_lt_iff₀ (weight_pos s)).mpr hdist
  calc
    dist ((y : V E) s) ((x : V E) s) = ‖(y : V E) s - (x : V E) s‖ := dist_eq_norm _ _
    _ ≤ dist y x / weight s := hcoord
    _ < ε := hdiv

/-- A fixed coordinate of a sequence in `(Z_E)^ℕ`, evaluated at a tree node, is
continuous. -/
theorem zSequence_coordinate_continuous {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    (m : ℕ) (s : Node) :
    Continuous (fun u : ZSequence E => (zSequenceToAmbient u m) s) :=
  (zElement_coordinate_continuous (E := E) s).comp (continuous_apply m)

end LowerComplete
end WeightedTree
end DSTBL3
