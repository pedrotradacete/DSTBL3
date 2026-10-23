import BanLat.Normed

/-!
# Generalities on the weighted tree construction

This file formalizes the definitions and lemma statements from Section 5 of
`paper.tex`: the weighted ambient sequence space, finite-rank elements, the
closed space `Z_E`, and the fattening operation on trees.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

universe u

/-- Nodes of the tree `N^{<N}` are represented by finite lists of naturals. -/
abbrev Node : Type := List ℕ

/-- The empty string. -/
def root : Node := []

/-- Concatenation of finite strings. -/
def concat (s t : Node) : Node :=
  s ++ t

/-- The child `s concat n`. -/
def child (s : Node) (n : ℕ) : Node :=
  s ++ [n]

/-- The length `|s|` of a finite string. -/
def nodeLength (s : Node) : ℕ :=
  s.length

/-- The last coordinate of a non-empty node, with value `0` at the root. -/
def lastD : Node → ℕ
  | [] => 0
  | n :: [] => n
  | _ :: ns => lastD ns

/-- The constant `gamma = 1 / 10`. -/
noncomputable def gamma : ℝ :=
  (10 : ℝ)⁻¹

/-- The constants `lambda_n = 2^{-n}` in zero-based indexing. -/
noncomputable def lambda (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹

/-- The product of the `lambda` factors attached to all but the last coordinate. -/
noncomputable def lambdaPrefixProduct : Node → ℝ
  | [] => 1
  | _ :: [] => 1
  | n :: m :: ns => lambda n * lambdaPrefixProduct (m :: ns)

/-- The weight `omega(s)` from Section 5. -/
noncomputable def weight (s : Node) : ℝ :=
  gamma ^ s.length * lambdaPrefixProduct s

/-- Section 5 normalization: the root has weight `1`. -/
theorem weight_root :
    weight root = 1 := by
  simp [weight, root, gamma, lambdaPrefixProduct]

/-- Section 5 computation for first-level nodes: every child of the root has
weight `gamma`. -/
theorem weight_child_root (n : ℕ) :
    weight (child root n) = gamma := by
  simp [weight, root, child, gamma, lambdaPrefixProduct]

/-- Positivity side lemma for the Section 5 weight constant `gamma`. -/
theorem gamma_nonneg : 0 ≤ gamma := by
  norm_num [gamma]

/-- Strict positivity of the Section 5 weight constant `gamma`. -/
theorem gamma_pos : 0 < gamma := by
  norm_num [gamma]

/-- Nonnegativity of the Section 5 decay factors `lambda_n`. -/
theorem lambda_nonneg (n : ℕ) : 0 ≤ lambda n :=
  inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)

/-- Strict positivity of the Section 5 decay factors `lambda_n`. -/
theorem lambda_pos (n : ℕ) : 0 < lambda n :=
  inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) n)

/-- Nonnegativity of the product of the `lambda` factors in the Section 5
weight formula. -/
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

/-- Strict positivity of the product of the `lambda` factors in the Section 5
weight formula. -/
theorem lambdaPrefixProduct_pos (s : Node) : 0 < lambdaPrefixProduct s := by
  induction s with
  | nil =>
      simp [lambdaPrefixProduct]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [lambdaPrefixProduct]
      | cons b bs =>
          simp [lambdaPrefixProduct]
          exact mul_pos (lambda_pos a) ih

/-- Nonnegativity of the Section 5 node weight `omega(s)`. -/
theorem weight_nonneg (s : Node) : 0 ≤ weight s := by
  unfold weight
  exact mul_nonneg (pow_nonneg gamma_nonneg s.length) (lambdaPrefixProduct_nonneg s)

/-- Strict positivity of the Section 5 node weight `omega(s)`. -/
theorem weight_pos (s : Node) : 0 < weight s := by
  unfold weight
  exact mul_pos (pow_pos gamma_pos s.length) (lambdaPrefixProduct_pos s)

/-- The fixed Section 5 constant `gamma = 1/10` is at most `1`. -/
theorem gamma_le_one : gamma ≤ 1 := by
  norm_num [gamma]

/-- Each Section 5 decay factor `lambda_n = 2^{-n}` is at most `1`. -/
theorem lambda_le_one (n : ℕ) : lambda n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- The product of `lambda` factors in the weight formula is at most `1`. -/
theorem lambdaPrefixProduct_le_one (s : Node) :
    lambdaPrefixProduct s ≤ 1 := by
  induction s with
  | nil =>
      simp [lambdaPrefixProduct]
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [lambdaPrefixProduct]
      | cons b bs =>
          simp [lambdaPrefixProduct]
          calc
            lambda a * lambdaPrefixProduct (b :: bs)
                ≤ 1 * lambdaPrefixProduct (b :: bs) :=
              mul_le_mul_of_nonneg_right (lambda_le_one a)
                (lambdaPrefixProduct_nonneg (b :: bs))
            _ ≤ 1 := by simpa using ih

/-- Basic Section 5 estimate: every node weight is bounded by the root weight
`1`. -/
theorem weight_le_one (s : Node) : weight s ≤ 1 := by
  unfold weight
  calc
    gamma ^ s.length * lambdaPrefixProduct s ≤ 1 * lambdaPrefixProduct s :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ gamma_nonneg gamma_le_one)
        (lambdaPrefixProduct_nonneg s)
    _ ≤ 1 := by simpa using lambdaPrefixProduct_le_one s

/-- Recursive formula for the `lambda` part of the weight after adding a
child below a non-root node. This is the product calculation behind Section
4's proper-extension weight estimates. -/
theorem lambdaPrefixProduct_child_nonroot {s : Node} (hs : s ≠ root) (n : ℕ) :
    lambdaPrefixProduct (child s n) = lambdaPrefixProduct s * lambda (lastD s) := by
  induction s with
  | nil =>
      contradiction
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [child, lambdaPrefixProduct, lastD]
      | cons b bs =>
          have h := ih (by simp [root])
          calc
            lambdaPrefixProduct (child (a :: b :: bs) n)
                = lambda a * lambdaPrefixProduct (child (b :: bs) n) := by
                    simp [child, lambdaPrefixProduct]
            _ = lambda a * (lambdaPrefixProduct (b :: bs) * lambda (lastD (b :: bs))) := by
                    rw [h]
            _ = lambdaPrefixProduct (a :: b :: bs) * lambda (lastD (a :: b :: bs)) := by
                    simp [lambdaPrefixProduct, lastD, mul_assoc]

/-- Weight recursion below a non-root node: a child weight is obtained by
multiplying by `gamma * lambda(lastD s)`. This is used throughout the
Section 5 controlled-tree and continuity estimates. -/
theorem weight_child_nonroot {s : Node} (hs : s ≠ root) (n : ℕ) :
    weight (child s n) = gamma * lambda (lastD s) * weight s := by
  have hprod := lambdaPrefixProduct_child_nonroot hs n
  rw [weight, hprod]
  simp [child, weight]
  ring

/-- A coordinatewise indexed sequence over the tree. -/
abbrev TreeSeq (E : Type u) : Type u :=
  Node → E

/-- The weighted boundedness condition defining `V_E`. -/
def WeightedBounded {E : Type u} [Norm E] (x : TreeSeq E) : Prop :=
  ∃ C : ℝ, ∀ s : Node, weight s * ‖x s‖ ≤ C

/-- The norm formula used on the ambient weighted sequence space. -/
noncomputable def weightedNorm {E : Type u} [Norm E] (x : TreeSeq E) : ℝ :=
  sSup (Set.range fun s : Node => weight s * ‖x s‖)

/-- The Banach lattice `V_E` of weighted-bounded indexed sequences. -/
def V (E : Type u) [Norm E] : Type u :=
  {x : TreeSeq E // WeightedBounded x}

instance {E : Type u} [Norm E] : CoeFun (V E) (fun _ => Node → E) where
  coe x := x.1

noncomputable instance {E : Type u} [Norm E] : Norm (V E) where
  norm x := weightedNorm (x : TreeSeq E)

/-- The weighted norm supremum is bounded above for every element of `V_E`;
this unfolds the boundedness condition in Section 5. -/
theorem weightedNorm_bddAbove {E : Type u} [SeminormedAddCommGroup E]
    (x : V E) :
    BddAbove (Set.range fun s : Node => weight s * ‖x s‖) := by
  rcases x.2 with ⟨C, hC⟩
  exact ⟨C, by
    rintro _ ⟨s, rfl⟩
    exact hC s⟩

/-- Nonnegativity of the weighted norm on the ambient space `V_E` from
Section 5. -/
theorem weightedNorm_nonneg {E : Type u} [SeminormedAddCommGroup E]
    (x : V E) :
    0 ≤ ‖x‖ := by
  change 0 ≤ weightedNorm (x : TreeSeq E)
  unfold weightedNorm
  have hroot : 0 ≤ weight root * ‖x root‖ :=
    mul_nonneg (weight_nonneg root) (norm_nonneg _)
  exact hroot.trans (le_csSup (weightedNorm_bddAbove x) ⟨root, rfl⟩)

/-- Supremum-introduction principle for the Section 5 weighted norm: a
coordinatewise weighted bound gives a norm bound. -/
theorem weightedNorm_le_of_forall {E : Type u} [SeminormedAddCommGroup E]
    {x : V E} {C : ℝ} (hC : ∀ s : Node, weight s * ‖x s‖ ≤ C) :
    ‖x‖ ≤ C := by
  change weightedNorm (x : TreeSeq E) ≤ C
  unfold weightedNorm
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨s, rfl⟩
    exact hC s

/-- Each weighted coordinate is bounded by the weighted norm, exactly as in
the supremum norm formula of Section 5. -/
theorem weighted_coordinate_le_norm {E : Type u} [SeminormedAddCommGroup E]
    (x : V E) (s : Node) :
    weight s * ‖x s‖ ≤ ‖x‖ := by
  change weight s * ‖x s‖ ≤ weightedNorm (x : TreeSeq E)
  unfold weightedNorm
  apply le_csSup
  · rcases x.2 with ⟨C, hC⟩
    exact ⟨C, by
      rintro _ ⟨t, rfl⟩
      exact hC t⟩
  · exact ⟨s, rfl⟩

/-- Converts a weighted-norm bound into an unweighted coordinate bound by
dividing by the positive weight. -/
theorem coordinate_norm_le_div_weight {E : Type u} [SeminormedAddCommGroup E]
    (x : V E) (s : Node) :
    ‖x s‖ ≤ ‖x‖ / weight s := by
  have h := weighted_coordinate_le_norm x s
  rw [mul_comm] at h
  exact (le_div_iff₀ (weight_pos s)).mpr h

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
    simpa [norm_neg] using hx s⟩

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

@[simp] theorem v_sub_apply {E : Type u} [SeminormedAddCommGroup E]
    (x y : V E) (s : Node) : (x - y) s = x s - y s := rfl

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

/-- The zero element has weighted norm zero in the ambient space of Section
4. -/
theorem weightedNorm_zero {E : Type u} [SeminormedAddCommGroup E] :
    ‖(0 : V E)‖ = 0 := by
  apply le_antisymm
  · apply weightedNorm_le_of_forall
    intro s
    change weight s * ‖(0 : E)‖ ≤ 0
    simp
  · exact weightedNorm_nonneg 0

/-- Triangle inequality for the Section 5 weighted norm. -/
theorem weightedNorm_add_le {E : Type u} [SeminormedAddCommGroup E]
    (x y : V E) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  apply weightedNorm_le_of_forall
  intro s
  calc
    weight s * ‖(x + y : V E) s‖ = weight s * ‖x s + y s‖ := rfl
    _ ≤ weight s * (‖x s‖ + ‖y s‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le (x s) (y s)) (weight_nonneg s)
    _ = weight s * ‖x s‖ + weight s * ‖y s‖ := by ring
    _ ≤ ‖x‖ + ‖y‖ :=
      add_le_add (weighted_coordinate_le_norm x s) (weighted_coordinate_le_norm y s)

/-- Triangle inequality in three-point form for the metric induced by the
Section 5 weighted norm. -/
theorem weightedNorm_sub_le {E : Type u} [SeminormedAddCommGroup E]
    (x y z : V E) :
    ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  apply weightedNorm_le_of_forall
  intro s
  calc
    weight s * ‖(x - z : V E) s‖ = weight s * ‖x s - z s‖ := rfl
    _ ≤ weight s * (‖x s - y s‖ + ‖y s - z s‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg s)
      calc
        ‖x s - z s‖ = ‖(x s - y s) + (y s - z s)‖ := by
          congr 1
          abel
        _ ≤ ‖x s - y s‖ + ‖y s - z s‖ := norm_add_le _ _
    _ = weight s * (‖(x - y : V E) s‖ + ‖(y - z : V E) s‖) := rfl
    _ = weight s * ‖(x - y : V E) s‖ + weight s * ‖(y - z : V E) s‖ := by ring
    _ ≤ ‖x - y‖ + ‖y - z‖ :=
      add_le_add (weighted_coordinate_le_norm (x - y) s)
        (weighted_coordinate_le_norm (y - z) s)

/-- Lipschitz estimate for addition in the weighted norm, used later for
closure of the finite-rank and `Z_E` sublattices. -/
theorem weightedNorm_add_sub_add_le {E : Type u} [SeminormedAddCommGroup E]
    (x y u v : V E) :
    ‖(x + y) - (u + v)‖ ≤ ‖x - u‖ + ‖y - v‖ := by
  have h :
      (x + y) - (u + v) = (x - u) + (y - v) := by
    apply Subtype.ext
    funext s
    change (x s + y s) - (u s + v s) = (x s - u s) + (y s - v s)
    abel
  calc
    ‖(x + y) - (u + v)‖ = ‖(x - u) + (y - v)‖ := by rw [h]
    _ ≤ ‖x - u‖ + ‖y - v‖ := weightedNorm_add_le (x - u) (y - v)

/-- Negation is nonexpansive for the weighted norm; this supports the
vector-space closure arguments around `S_E` and `Z_E` in Section 5. -/
theorem weightedNorm_neg_sub_neg_le {E : Type u} [SeminormedAddCommGroup E]
    (x u : V E) :
    ‖(-x) - (-u)‖ ≤ ‖x - u‖ := by
  apply weightedNorm_le_of_forall
  intro s
  calc
    weight s * ‖((-x) - (-u) : V E) s‖ =
        weight s * ‖-(x s) - -(u s)‖ := rfl
    _ = weight s * ‖x s - u s‖ := by
      have h : -(x s) - -(u s) = -(x s - u s) := by abel
      rw [h, norm_neg]
    _ = weight s * ‖(x - u : V E) s‖ := rfl
    _ ≤ ‖x - u‖ := weighted_coordinate_le_norm (x - u) s

/-- Scalar multiplication is Lipschitz with constant `‖a‖` in the weighted
norm, one of the algebraic estimates behind Section 5's Banach-lattice
scaffold. -/
theorem weightedNorm_smul_sub_smul_le {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ℝ) (x u : V E) :
    ‖(a • x) - (a • u)‖ ≤ ‖a‖ * ‖x - u‖ := by
  apply weightedNorm_le_of_forall
  intro s
  calc
    weight s * ‖((a • x) - (a • u) : V E) s‖ =
        weight s * ‖a • x s - a • u s‖ := rfl
    _ = weight s * ‖a • (x s - u s)‖ := by rw [← smul_sub]
    _ = ‖a‖ * (weight s * ‖x s - u s‖) := by
      rw [norm_smul]
      ring
    _ = ‖a‖ * (weight s * ‖(x - u : V E) s‖) := rfl
    _ ≤ ‖a‖ * ‖x - u‖ :=
      mul_le_mul_of_nonneg_left (weighted_coordinate_le_norm (x - u) s) (norm_nonneg a)

/-- Supremum is jointly Lipschitz in the weighted norm, used to show the
finite-rank and closed spaces are sublattices as in Section 5. -/
theorem weightedNorm_sup_sub_sup_le {E : Type u} [NormedAddCommGroup E]
    [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E] (x y u v : V E) :
    ‖(x ⊔ y) - (u ⊔ v)‖ ≤ ‖x - u‖ + ‖y - v‖ := by
  apply weightedNorm_le_of_forall
  intro s
  calc
    weight s * ‖((x ⊔ y) - (u ⊔ v) : V E) s‖ =
        weight s * ‖x s ⊔ y s - (u s ⊔ v s)‖ := rfl
    _ ≤ weight s * (‖x s - u s‖ + ‖y s - v s‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sup_sub_sup_le_add_norm (x s) (y s) (u s) (v s)) (weight_nonneg s)
    _ = weight s * (‖(x - u : V E) s‖ + ‖(y - v : V E) s‖) := rfl
    _ = weight s * ‖(x - u : V E) s‖ + weight s * ‖(y - v : V E) s‖ := by ring
    _ ≤ ‖x - u‖ + ‖y - v‖ :=
      add_le_add (weighted_coordinate_le_norm (x - u) s)
        (weighted_coordinate_le_norm (y - v) s)

/-- Infimum is jointly Lipschitz in the weighted norm, parallel to the
supremum estimate used in the Section 5 sublattice proofs. -/
theorem weightedNorm_inf_sub_inf_le {E : Type u} [NormedAddCommGroup E]
    [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E] (x y u v : V E) :
    ‖(x ⊓ y) - (u ⊓ v)‖ ≤ ‖x - u‖ + ‖y - v‖ := by
  apply weightedNorm_le_of_forall
  intro s
  calc
    weight s * ‖((x ⊓ y) - (u ⊓ v) : V E) s‖ =
        weight s * ‖x s ⊓ y s - (u s ⊓ v s)‖ := rfl
    _ ≤ weight s * (‖x s - u s‖ + ‖y s - v s‖) :=
      mul_le_mul_of_nonneg_left
        (norm_inf_sub_inf_le_add_norm (x s) (y s) (u s) (v s)) (weight_nonneg s)
    _ = weight s * (‖(x - u : V E) s‖ + ‖(y - v : V E) s‖) := rfl
    _ = weight s * ‖(x - u : V E) s‖ + weight s * ‖(y - v : V E) s‖ := by ring
    _ ≤ ‖x - u‖ + ‖y - v‖ :=
      add_le_add (weighted_coordinate_le_norm (x - u) s)
        (weighted_coordinate_le_norm (y - v) s)

/-- `s` is an initial segment of `t`. -/
def Prefix (s t : Node) : Prop :=
  ∃ u : Node, t = s ++ u

/-- A set of nodes is downward closed. -/
def DownwardClosed (T : Set Node) : Prop :=
  ∀ {s t : Node}, Prefix s t → t ∈ T → s ∈ T

/-- A tree on `N`: a downward closed set of nodes containing the root. -/
def IsTree (T : Set Node) : Prop :=
  root ∈ T ∧ DownwardClosed T

/-- The coded space `Tr` of trees on `N`. -/
def Tree : Type :=
  {T : Set Node // IsTree T}

instance : Coe (Tree) (Set Node) where
  coe T := T.1

end WeightedTree
end DSTBL3
