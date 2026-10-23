import Mathlib
import BanLat.Normed

/-!
# Theorem B (`lower-complete`)

This standalone showcase records the definitions appearing in the statement of
Theorem B.  The implementation in `ThmBC.Lower.Complete` is not imported here.
-/

open scoped Topology

namespace TheoremB

universe u v

/-! ## Descriptive-set-theoretic conventions -/

/-- A set is coanalytic when its complement is analytic. -/
def CoanalyticSet {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  MeasureTheory.AnalyticSet Aᶜ

/-- Continuous reducibility: `C ≤c A` when `C` is the preimage of `A` under
a continuous map. -/
def ContinuouslyReducible {Y : Type v} {X : Type u}
    [TopologicalSpace Y] [TopologicalSpace X] (C : Set Y) (A : Set X) : Prop :=
  ∃ f : Y → X, Continuous f ∧ ∀ y : Y, y ∈ C ↔ f y ∈ A

/-- `Π¹₁`-hardness with respect to continuous reductions from coanalytic
subsets of Baire space. -/
def Pi11Hard {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ C : Set (ℕ → ℕ), CoanalyticSet C → ContinuouslyReducible C A

/-- A `Π¹₁`-complete subset of a Polish space. -/
def Pi11CompleteSet {X : Type u} [TopologicalSpace X] [PolishSpace X]
    (A : Set X) : Prop :=
  CoanalyticSet A ∧ Pi11Hard A

/-- Predicate form of `Pi11CompleteSet`. -/
def Pi11Complete {X : Type u} [TopologicalSpace X] [PolishSpace X]
    (P : X → Prop) : Prop :=
  Pi11CompleteSet {x : X | P x}

/-! ## The weighted tree space -/

/-- Nodes of `ℕ^{<ℕ}` are finite lists of natural numbers. -/
abbrev Node : Type := List ℕ

/-- The root of the tree. -/
def root : Node := []

/-- The child obtained by appending one coordinate. -/
def child (s : Node) (n : ℕ) : Node :=
  s ++ [n]

/-- The constant `γ = 1/10` used in the node weights. -/
noncomputable def gamma : ℝ :=
  (10 : ℝ)⁻¹

/-- The coordinate decay factors `λₙ = 2⁻ⁿ`. -/
noncomputable def lambda (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹

/-- The product of the decay factors attached to all but the last coordinate. -/
noncomputable def lambdaPrefixProduct : Node → ℝ
  | [] => 1
  | _ :: [] => 1
  | n :: m :: ns => lambda n * lambdaPrefixProduct (m :: ns)

/-- The weight `ω(s)` attached to a tree node. -/
noncomputable def weight (s : Node) : ℝ :=
  gamma ^ s.length * lambdaPrefixProduct s

theorem gamma_nonneg : 0 ≤ gamma := by
  norm_num [gamma]

theorem lambda_nonneg (n : ℕ) : 0 ≤ lambda n :=
  inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)

theorem lambdaPrefixProduct_nonneg (s : Node) : 0 ≤ lambdaPrefixProduct s := by
  induction s with
  | nil =>
      simp [lambdaPrefixProduct]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [lambdaPrefixProduct]
      | cons b bs =>
          simp [lambdaPrefixProduct]
          exact mul_nonneg (lambda_nonneg a) ih

theorem weight_nonneg (s : Node) : 0 ≤ weight s := by
  exact mul_nonneg (pow_nonneg gamma_nonneg s.length) (lambdaPrefixProduct_nonneg s)

/-- A tree-indexed sequence with values in `E`. -/
abbrev TreeSeq (E : Type u) : Type u :=
  Node → E

/-- Weighted boundedness of a tree-indexed sequence. -/
def WeightedBounded {E : Type u} [Norm E] (x : TreeSeq E) : Prop :=
  ∃ C : ℝ, ∀ s : Node, weight s * ‖x s‖ ≤ C

/-- The weighted supremum norm. -/
noncomputable def weightedNorm {E : Type u} [Norm E] (x : TreeSeq E) : ℝ :=
  sSup (Set.range fun s : Node => weight s * ‖x s‖)

/-- The ambient space `V_E` of weighted-bounded tree-indexed sequences. -/
def V (E : Type u) [Norm E] : Type u :=
  {x : TreeSeq E // WeightedBounded x}

instance {E : Type u} [Norm E] : CoeFun (V E) (fun _ => Node → E) where
  coe x := x.1

noncomputable instance {E : Type u} [Norm E] : Norm (V E) where
  norm x := weightedNorm (x : TreeSeq E)

instance {E : Type u} [SeminormedAddCommGroup E] : Zero (V E) where
  zero := ⟨fun _ => 0, by
    refine ⟨0, ?_⟩
    intro s
    simp⟩

instance {E : Type u} [SeminormedAddCommGroup E] : Sub (V E) where
  sub x y := ⟨fun s => x s - y s, by
    rcases x.2 with ⟨Cx, hx⟩
    rcases y.2 with ⟨Cy, hy⟩
    refine ⟨Cx + Cy, ?_⟩
    intro s
    calc
      weight s * ‖x s - y s‖ ≤ weight s * (‖x s‖ + ‖y s‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le (x s) (y s)) (weight_nonneg s)
      _ = weight s * ‖x s‖ + weight s * ‖y s‖ := by ring
      _ ≤ Cx + Cy := add_le_add (hx s) (hy s)⟩

/-- `s` is an initial segment of `t`. -/
def Prefix (s t : Node) : Prop :=
  ∃ u : Node, t = s ++ u

/-- A set of nodes is downward closed. -/
def DownwardClosed (T : Set Node) : Prop :=
  ∀ ⦃s t : Node⦄, Prefix s t → t ∈ T → s ∈ T

/-- A tree contains the root and is downward closed. -/
def IsTree (T : Set Node) : Prop :=
  root ∈ T ∧ DownwardClosed T

/-- A finite downward-closed tree containing the root. -/
def IsFiniteDownwardClosedTree (F : Set Node) : Prop :=
  F.Finite ∧ IsTree F

/-- Finite-rank elements of `V_E`. -/
def FiniteRank {E : Type u} [Norm E] (x : V E) : Prop :=
  ∃ F : Set Node,
    IsFiniteDownwardClosedTree F ∧
      ∀ s : Node, ∀ n : ℕ,
        s ∈ F → child s n ∉ F → ∀ t : Node, x (child s n ++ t) = x s

/-- Membership in `Z_E`, the weighted-norm closure of the finite-rank elements. -/
def InZ {E : Type u} [SeminormedAddCommGroup E] (x : V E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ u : V E, FiniteRank u ∧ ‖x - u‖ < ε

/-- The closed space `Z_E`. -/
def Z (E : Type u) [SeminormedAddCommGroup E] : Set (V E) :=
  {x | InZ x}

/-! ## Decreasing sequences with infimum zero -/

/-- Coordinatewise order on the ambient weighted space. -/
def CoordinatewiseLE {E : Type u} [Norm E] [LE E] (x y : V E) : Prop :=
  ∀ s : Node, x s ≤ y s

/-- Coordinatewise positivity on the ambient weighted space. -/
def CoordinatewiseNonnegative {E : Type u} [Norm E] [Zero E] [LE E]
    (x : V E) : Prop :=
  ∀ s : Node, 0 ≤ x s

/-- A positive decreasing sequence in the coordinatewise order. -/
def IsPositiveDecreasing {E : Type u} [SeminormedAddCommGroup E] [LE E]
    (u : ℕ → V E) : Prop :=
  (∀ m : ℕ, CoordinatewiseNonnegative (u m)) ∧
    ∀ m : ℕ, CoordinatewiseLE (u (m + 1)) (u m)

/-- A nonzero positive lower bound in `Z_E`. -/
def IsNonzeroPositiveLowerBoundInZ {E : Type u}
    [SeminormedAddCommGroup E] [LE E] (y : V E) (u : ℕ → V E) : Prop :=
  y ∈ Z E ∧ CoordinatewiseNonnegative y ∧ y ≠ 0 ∧
    ∀ m : ℕ, CoordinatewiseLE y (u m)

/-- A sequence has infimum zero in `Z_E` when it has no nonzero positive lower
bound in `Z_E`. -/
def HasInfimumZeroInZ {E : Type u} [SeminormedAddCommGroup E] [LE E]
    (u : ℕ → V E) : Prop :=
  ¬ ∃ y : V E, IsNonzeroPositiveLowerBoundInZ y u

/-- The intrinsic type corresponding to the lattice `Z_E`. -/
def ZElement (E : Type u) [SeminormedAddCommGroup E] : Type u :=
  {x : V E // x ∈ Z E}

instance {E : Type u} [SeminormedAddCommGroup E] : Coe (ZElement E) (V E) where
  coe x := x.1

/-- The intrinsic sequence space `(Z_E)^ℕ`. -/
abbrev ZSequence (E : Type u) [SeminormedAddCommGroup E] : Type u :=
  ℕ → ZElement E

/-- View an intrinsic `Z_E`-valued sequence in the ambient space. -/
def zSequenceToAmbient {E : Type u} [SeminormedAddCommGroup E]
    (u : ZSequence E) : ℕ → V E :=
  fun n => (u n : V E)

/-- The set `X_{↓0}` on the intrinsic sequence space `(Z_E)^ℕ`. -/
def XDownarrowZeroZ {E : Type u} [NormedAddCommGroup E] [LE E]
    (u : ZSequence E) : Prop :=
  IsPositiveDecreasing (zSequenceToAmbient u) ∧
    HasInfimumZeroInZ (zSequenceToAmbient u)

/-! ## Theorem B -/

/-- A bundled witness for Theorem B. -/
structure LowerCompleteWitness where
  E : Type u
  [normed : NormedAddCommGroup E]
  [lattice : Lattice E]
  [orderedAdd : IsOrderedAddMonoid E]
  [banachLattice : BanachLattice E]
  [separable : TopologicalSpace.SeparableSpace E]
  [sequenceTopology : TopologicalSpace (ZSequence E)]
  [sequencePolish : PolishSpace (ZSequence E)]
  complete : @Pi11Complete (ZSequence E) sequenceTopology sequencePolish
    (fun u : ZSequence E => XDownarrowZeroZ u)

/-- **Theorem B (`lower-complete`).** There is a separable Banach lattice for
which the set of positive decreasing sequences with infimum zero is
`Π¹₁`-complete. -/
theorem lower_complete_template : Nonempty LowerCompleteWitness := by
  sorry

end TheoremB
