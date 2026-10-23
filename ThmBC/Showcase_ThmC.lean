import Mathlib
import BanLat.Normed

/-!
# Theorem C (`upper-complete`)

This standalone showcase records the definitions appearing in the statement of
Theorem C. The implementation in `ThmBC.Upper.Upper` is not imported here.
-/

open scoped Topology

namespace TheoremC

universe u v

/-! ## Descriptive-set-theoretic conventions -/

/-- A set is coanalytic when its complement is analytic. -/
def CoanalyticSet {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  MeasureTheory.AnalyticSet Aᶜ

/-- Continuous reducibility: `C ≤c A` when `C` is the preimage of `A` under
a continuous map. -/
def ContinuouslyReducible {W : Type v} {X : Type u}
    [TopologicalSpace W] [TopologicalSpace X] (C : Set W) (A : Set X) : Prop :=
  ∃ f : W → X, Continuous f ∧ ∀ w : W, w ∈ C ↔ f w ∈ A

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

instance {E : Type u} [SeminormedAddCommGroup E] : Add (V E) where
  add x y := ⟨fun s => x s + y s, by
    rcases x.2 with ⟨Cx, hx⟩
    rcases y.2 with ⟨Cy, hy⟩
    refine ⟨Cx + Cy, ?_⟩
    intro s
    calc
      weight s * ‖x s + y s‖ ≤ weight s * (‖x s‖ + ‖y s‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le (x s) (y s)) (weight_nonneg s)
      _ = weight s * ‖x s‖ + weight s * ‖y s‖ := by ring
      _ ≤ Cx + Cy := add_le_add (hx s) (hy s)⟩

instance {E : Type u} [SeminormedAddCommGroup E] : Neg (V E) where
  neg x := ⟨fun s => -x s, by
    rcases x.2 with ⟨C, hx⟩
    refine ⟨C, ?_⟩
    intro s
    simpa using hx s⟩

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

instance {E : Type u} [NormedAddCommGroup E] [SMul ℝ E] [NormSMulClass ℝ E] :
    SMul ℝ (V E) where
  smul a x := ⟨fun s => a • x s, by
    rcases x.2 with ⟨C, hx⟩
    refine ⟨‖a‖ * C, ?_⟩
    intro s
    calc
      weight s * ‖a • x s‖ = ‖a‖ * (weight s * ‖x s‖) := by
        rw [norm_smul]
        ring
      _ ≤ ‖a‖ * C := mul_le_mul_of_nonneg_left (hx s) (norm_nonneg a)⟩

instance {E : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [HasSolidNorm E] : Max (V E) where
  max x y := ⟨fun s => x s ⊔ y s, by
    rcases x.2 with ⟨Cx, hx⟩
    rcases y.2 with ⟨Cy, hy⟩
    refine ⟨Cx + Cy, ?_⟩
    intro s
    calc
      weight s * ‖x s ⊔ y s‖ ≤ weight s * (‖x s‖ + ‖y s‖) :=
        mul_le_mul_of_nonneg_left (norm_sup_le_add (x s) (y s)) (weight_nonneg s)
      _ = weight s * ‖x s‖ + weight s * ‖y s‖ := by ring
      _ ≤ Cx + Cy := add_le_add (hx s) (hy s)⟩

instance {E : Type u} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [HasSolidNorm E] : Min (V E) where
  min x y := ⟨fun s => x s ⊓ y s, by
    rcases x.2 with ⟨Cx, hx⟩
    rcases y.2 with ⟨Cy, hy⟩
    refine ⟨Cx + Cy, ?_⟩
    intro s
    calc
      weight s * ‖x s ⊓ y s‖ ≤ weight s * (‖x s‖ + ‖y s‖) :=
        mul_le_mul_of_nonneg_left (norm_inf_le_add (x s) (y s)) (weight_nonneg s)
      _ = weight s * ‖x s‖ + weight s * ‖y s‖ := by ring
      _ ≤ Cx + Cy := add_le_add (hx s) (hy s)⟩

/-! ## The closed finite-rank space -/

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

/-- Metric convergence for the weighted norm. -/
def WeightedConvergesTo {E : Type u} [SeminormedAddCommGroup E]
    (u : ℕ → V E) (x : V E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n - x‖ < ε

/-- Cauchy sequences for the weighted norm. -/
def WeightedCauchy {E : Type u} [SeminormedAddCommGroup E]
    (u : ℕ → V E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → ‖u m - u n‖ < ε

/-- A lightweight vector-sublattice predicate for subsets of `V_E`. -/
def IsVectorSubLattice {E : Type u}
    [NormedAddCommGroup E] [SMul ℝ E] [NormSMulClass ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E] (A : Set (V E)) : Prop :=
  0 ∈ A ∧
    (∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) ∧
    (∀ x ∈ A, -x ∈ A) ∧
    (∀ a : ℝ, ∀ x ∈ A, a • x ∈ A) ∧
    (∀ x ∈ A, ∀ y ∈ A, x ⊔ y ∈ A) ∧
    (∀ x ∈ A, ∀ y ∈ A, x ⊓ y ∈ A)

/-- Sequential completeness for the weighted norm. -/
def IsCompleteForWeightedNorm {E : Type u} [SeminormedAddCommGroup E]
    (A : Set (V E)) : Prop :=
  ∀ u : ℕ → V E,
    (∀ n : ℕ, u n ∈ A) → WeightedCauchy u →
      ∃ x : V E, x ∈ A ∧ WeightedConvergesTo u x

/-- Closedness for the weighted norm. -/
def IsClosedForWeightedNorm {E : Type u} [SeminormedAddCommGroup E]
    (A : Set (V E)) : Prop :=
  ∀ x : V E,
    (∀ ε : ℝ, 0 < ε → ∃ y : V E, y ∈ A ∧ ‖x - y‖ < ε) → x ∈ A

/-- The project-level meaning of a closed Banach sublattice. -/
def IsClosedBanachSubLattice {E : Type u}
    [NormedAddCommGroup E] [SMul ℝ E] [NormSMulClass ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E] (A : Set (V E)) : Prop :=
  IsVectorSubLattice A ∧ IsClosedForWeightedNorm A ∧ IsCompleteForWeightedNorm A

/-- Separability for the weighted norm. -/
def IsSeparableForWeightedNorm {E : Type u} [SeminormedAddCommGroup E]
    (A : Set (V E)) : Prop :=
  ∃ D : Set (V E),
    Set.Countable D ∧ D ⊆ A ∧
      ∀ x : V E, x ∈ A →
        ∀ ε : ℝ, 0 < ε → ∃ y : V E, y ∈ D ∧ ‖x - y‖ < ε

/-! ## Positive increasing sequences in the root-zero lattice -/

/-- Coordinatewise order on the ambient weighted space. -/
def CoordinatewiseLE {E : Type u} [Norm E] [LE E] (x y : V E) : Prop :=
  ∀ s : Node, x s ≤ y s

/-- Coordinatewise positivity on the ambient weighted space. -/
def CoordinatewiseNonnegative {E : Type u} [Norm E] [Zero E] [LE E]
    (x : V E) : Prop :=
  ∀ s : Node, 0 ≤ x s

/-- The root-zero sublattice `Y = {y ∈ Z_ℝ | y_root = 0}`. -/
def Y : Set (V ℝ) :=
  {y : V ℝ | y ∈ Z ℝ ∧ y root = 0}

/-- An order upper bound in `Y`. -/
def IsOrderUpperBoundInY (y : V ℝ) (u : ℕ → V ℝ) : Prop :=
  y ∈ Y ∧ ∀ m : ℕ, CoordinatewiseLE (u m) y

/-- A positive increasing sequence in the coordinatewise order. -/
def IsPositiveIncreasing (u : ℕ → V ℝ) : Prop :=
  (∀ m : ℕ, CoordinatewiseNonnegative (u m)) ∧
    ∀ m : ℕ, CoordinatewiseLE (u m) (u (m + 1))

/-- `Y^{↑∞}`: positive increasing `Y`-valued sequences with no order upper
bound in `Y`. -/
def YUpwardUnbounded (u : ℕ → V ℝ) : Prop :=
  (∀ m : ℕ, u m ∈ Y) ∧
    IsPositiveIncreasing u ∧
      ¬ ∃ y : V ℝ, IsOrderUpperBoundInY y u

/-- The intrinsic type corresponding to `Z_E`. -/
def ZElement (E : Type u) [SeminormedAddCommGroup E] : Type u :=
  {x : V E // x ∈ Z E}

instance {E : Type u} [SeminormedAddCommGroup E] : Coe (ZElement E) (V E) where
  coe x := x.1

/-- The root-zero lattice `Y` represented as an intrinsic subtype of `Z_ℝ`. -/
def YElement : Type :=
  {x : ZElement ℝ // (x : V ℝ) root = 0}

instance : Coe YElement (V ℝ) where
  coe x := (x.1 : V ℝ)

/-- The intrinsic sequence space `Y^ℕ`. -/
abbrev YSequence : Type :=
  ℕ → YElement

/-- View an intrinsic `Y`-valued sequence in the ambient weighted space. -/
def ySequenceToAmbient (u : YSequence) : ℕ → V ℝ :=
  fun n => (u n : V ℝ)

/-- `Y^{↑∞}` as a predicate on the intrinsic sequence space. -/
def YUpwardUnboundedY (u : YSequence) : Prop :=
  YUpwardUnbounded (ySequenceToAmbient u)

/-! ## Theorem C -/

/-- A bundled witness for Theorem C. -/
structure UpperCompleteWitness where
  [sequenceTopology : TopologicalSpace YSequence]
  [sequencePolish : PolishSpace YSequence]
  closed : IsClosedBanachSubLattice Y
  separable : IsSeparableForWeightedNorm Y
  complete : @Pi11Complete YSequence sequenceTopology sequencePolish
    (fun u : YSequence => YUpwardUnboundedY u)

/-- **Theorem C (`upper-complete`).** There is a separable Banach lattice `Y`
for which the positive increasing sequences without an order upper bound form
a `Π¹₁`-complete set. -/
theorem upper_complete_template : Nonempty UpperCompleteWitness := by
  sorry

end TheoremC
