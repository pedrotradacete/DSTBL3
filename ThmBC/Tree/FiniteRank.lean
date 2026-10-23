import ThmBC.Tree.Basic

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

universe u

/-- A finite downward closed tree containing the root. -/
def IsFiniteDownwardClosedTree (F : Set Node) : Prop :=
  F.Finite ∧ IsTree F

/-- Finite-rank elements of `V_E`. -/
def FiniteRank {E : Type u} [Norm E] (x : V E) : Prop :=
  ∃ F : Set Node,
    IsFiniteDownwardClosedTree F ∧
      ∀ s : Node, ∀ n : ℕ,
        s ∈ F →
          child s n ∉ F →
            ∀ t : Node, x (child s n ++ t) = x s

/-- The set `S_E` of finite-rank elements. -/
def S (E : Type u) [Norm E] : Set (V E) :=
  {x | FiniteRank x}

/-- Propagates the finite-rank witness condition below the first point where
an appended tail leaves the finite tree. This is the main local constancy
lemma behind Section 5's definition of finite rank. -/
theorem finiteRank_constant_subtree_from_witness {E : Type u} [Norm E]
    {F : Set Node} {x : V E}
    (hW : ∀ s : Node, ∀ n : ℕ,
      s ∈ F → child s n ∉ F → ∀ t : Node, x (child s n ++ t) = x s) :
    ∀ {p r : Node}, p ∈ F → p ++ r ∉ F →
      ∀ t : Node, x ((p ++ r) ++ t) = x (p ++ r) := by
  intro p r hp hpr
  induction r generalizing p with
  | nil =>
      exact False.elim (hpr (by simpa using hp))
  | cons n r ih =>
      by_cases hc : child p n ∈ F
      · have hnot : child p n ++ r ∉ F := by
          intro hmem
          exact hpr (by simpa [child, List.append_assoc] using hmem)
        intro t
        simpa [child, List.append_assoc] using ih hc hnot t
      · intro t
        have h1 := hW p n hp hc (r ++ t)
        have h2 := hW p n hp hc r
        calc
          x ((p ++ (n :: r)) ++ t) = x (child p n ++ (r ++ t)) := by
            simp [child, List.append_assoc]
          _ = x p := h1
          _ = x (child p n ++ r) := h2.symm
          _ = x (p ++ (n :: r)) := by
            simp [child, List.append_assoc]

/-- Once a node is outside the finite witness tree, a finite-rank element is
constant on the entire subtree above it. -/
theorem finiteRank_constant_subtree_of_not_mem {E : Type u} [Norm E]
    {F : Set Node} {x : V E} (hF : IsFiniteDownwardClosedTree F)
    (hW : ∀ s : Node, ∀ n : ℕ,
      s ∈ F → child s n ∉ F → ∀ t : Node, x (child s n ++ t) = x s)
    {r : Node} (hr : r ∉ F) :
    ∀ t : Node, x (r ++ t) = x r := by
  have h := finiteRank_constant_subtree_from_witness hW hF.2.1 hr
  simpa [root] using h

/-- Enlarging the finite witness tree preserves the boundary-constancy
condition for a finite-rank element. -/
theorem finiteRank_witness_mono {E : Type u} [Norm E] {F H : Set Node}
    {x : V E} (hF : IsFiniteDownwardClosedTree F)
    (hW : ∀ s : Node, ∀ n : ℕ,
      s ∈ F → child s n ∉ F → ∀ t : Node, x (child s n ++ t) = x s)
    (hFH : F ⊆ H) :
    ∀ s : Node, ∀ n : ℕ,
      s ∈ H → child s n ∉ H → ∀ t : Node, x (child s n ++ t) = x s := by
  intro s n _hsH hchildH t
  by_cases hsF : s ∈ F
  · have hchildF : child s n ∉ F := by
      intro h
      exact hchildH (hFH h)
    exact hW s n hsF hchildF t
  · have hconst := finiteRank_constant_subtree_of_not_mem hF hW hsF
    simpa [child, List.append_assoc] using hconst ([n] ++ t)

/-- The singleton root tree is the smallest finite downward closed tree and
serves as the witness for the zero finite-rank element. -/
theorem isFiniteDownwardClosedTree_singleton_root :
    IsFiniteDownwardClosedTree ({root} : Set Node) := by
  constructor
  · exact Set.finite_singleton root
  · constructor
    · simp
    · intro s t hst ht
      simp at ht
      subst t
      rcases hst with ⟨u, h⟩
      simp [root] at h
      rcases h with ⟨rfl, rfl⟩
      simp [root]

/-- Finite downward closed trees are closed under union, allowing common
witnesses for algebraic operations on finite-rank elements. -/
theorem isFiniteDownwardClosedTree_union {F G : Set Node}
    (hF : IsFiniteDownwardClosedTree F) (hG : IsFiniteDownwardClosedTree G) :
    IsFiniteDownwardClosedTree (F ∪ G) := by
  constructor
  · exact hF.1.union hG.1
  · constructor
    · exact Or.inl hF.2.1
    · intro s t hst ht
      cases ht with
      | inl htF =>
          exact Or.inl (hF.2.2 hst htF)
      | inr htG =>
          exact Or.inr (hG.2.2 hst htG)

/-- The zero element is finite-rank, one component of the Section 5 claim that
`S_E` is a vector sublattice. -/
theorem finiteRank_zero {E : Type u} [SeminormedAddCommGroup E] :
    FiniteRank (0 : V E) := by
  refine ⟨{root}, isFiniteDownwardClosedTree_singleton_root, ?_⟩
  intro _s _n _hs _hchild _t
  rfl

/-- Finite-rank elements are closed under addition, using the union of their
finite witness trees. -/
theorem finiteRank_add {E : Type u} [SeminormedAddCommGroup E] {x y : V E}
    (hx : FiniteRank x) (hy : FiniteRank y) :
    FiniteRank (x + y) := by
  rcases hx with ⟨F, hF, hWx⟩
  rcases hy with ⟨G, hG, hWy⟩
  let H : Set Node := F ∪ G
  have hH : IsFiniteDownwardClosedTree H := isFiniteDownwardClosedTree_union hF hG
  have hFx : F ⊆ H := fun _ hs => Or.inl hs
  have hGy : G ⊆ H := fun _ hs => Or.inr hs
  have hWxH := finiteRank_witness_mono hF hWx hFx
  have hWyH := finiteRank_witness_mono hG hWy hGy
  refine ⟨H, hH, ?_⟩
  intro s n hs hchild t
  change x (child s n ++ t) + y (child s n ++ t) = x s + y s
  rw [hWxH s n hs hchild t, hWyH s n hs hchild t]

/-- Finite-rank elements are closed under negation. -/
theorem finiteRank_neg {E : Type u} [SeminormedAddCommGroup E] {x : V E}
    (hx : FiniteRank x) :
    FiniteRank (-x) := by
  rcases hx with ⟨F, hF, hWx⟩
  refine ⟨F, hF, ?_⟩
  intro s n hs hchild t
  change -x (child s n ++ t) = -x s
  rw [hWx s n hs hchild t]

/-- Finite-rank elements are closed under scalar multiplication. -/
theorem finiteRank_smul {E : Type u} [NormedAddCommGroup E] [SMul ℝ E]
    [NormSMulClass ℝ E] (a : ℝ) {x : V E} (hx : FiniteRank x) :
    FiniteRank (a • x) := by
  rcases hx with ⟨F, hF, hWx⟩
  refine ⟨F, hF, ?_⟩
  intro s n hs hchild t
  change a • x (child s n ++ t) = a • x s
  rw [hWx s n hs hchild t]

/-- Finite-rank elements are closed under lattice supremum, part of the
Section 5 proof that `S_E` is a vector sublattice. -/
theorem finiteRank_sup {E : Type u} [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [HasSolidNorm E] {x y : V E}
    (hx : FiniteRank x) (hy : FiniteRank y) :
    FiniteRank (x ⊔ y) := by
  rcases hx with ⟨F, hF, hWx⟩
  rcases hy with ⟨G, hG, hWy⟩
  let H : Set Node := F ∪ G
  have hH : IsFiniteDownwardClosedTree H := isFiniteDownwardClosedTree_union hF hG
  have hFx : F ⊆ H := fun _ hs => Or.inl hs
  have hGy : G ⊆ H := fun _ hs => Or.inr hs
  have hWxH := finiteRank_witness_mono hF hWx hFx
  have hWyH := finiteRank_witness_mono hG hWy hGy
  refine ⟨H, hH, ?_⟩
  intro s n hs hchild t
  change x (child s n ++ t) ⊔ y (child s n ++ t) = x s ⊔ y s
  rw [hWxH s n hs hchild t, hWyH s n hs hchild t]

/-- Finite-rank elements are closed under lattice infimum, parallel to the
supremum closure lemma. -/
theorem finiteRank_inf {E : Type u} [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [HasSolidNorm E] {x y : V E}
    (hx : FiniteRank x) (hy : FiniteRank y) :
    FiniteRank (x ⊓ y) := by
  rcases hx with ⟨F, hF, hWx⟩
  rcases hy with ⟨G, hG, hWy⟩
  let H : Set Node := F ∪ G
  have hH : IsFiniteDownwardClosedTree H := isFiniteDownwardClosedTree_union hF hG
  have hFx : F ⊆ H := fun _ hs => Or.inl hs
  have hGy : G ⊆ H := fun _ hs => Or.inr hs
  have hWxH := finiteRank_witness_mono hF hWx hFx
  have hWyH := finiteRank_witness_mono hG hWy hGy
  refine ⟨H, hH, ?_⟩
  intro s n hs hchild t
  change x (child s n ++ t) ⊓ y (child s n ++ t) = x s ⊓ y s
  rw [hWxH s n hs hchild t, hWyH s n hs hchild t]

/-- Metric convergence for the weighted norm on `V_E`. -/
def WeightedConvergesTo {E : Type u} [SeminormedAddCommGroup E]
    (u : ℕ → V E) (x : V E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖u n - x‖ < ε

/-- Cauchy sequences for the weighted norm on `V_E`. -/
def WeightedCauchy {E : Type u} [SeminormedAddCommGroup E]
    (u : ℕ → V E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → ‖u m - u n‖ < ε

/-- Membership in `Z_E`, the weighted-norm closure of finite-rank elements. -/
def InZ {E : Type u} [SeminormedAddCommGroup E] (x : V E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ u : V E, FiniteRank u ∧ ‖x - u‖ < ε

/-- The space `Z_E`, the closure of `S_E` in `V_E`. -/
def Z (E : Type u) [SeminormedAddCommGroup E] : Set (V E) :=
  {x | InZ x}

/-- A lightweight predicate for vector sublattices in the ambient sequence space. -/
def IsVectorSubLattice {E : Type u} [NormedAddCommGroup E] [SMul ℝ E] [NormSMulClass ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E] (A : Set (V E)) : Prop :=
  0 ∈ A ∧
    (∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) ∧
    (∀ x ∈ A, -x ∈ A) ∧
    (∀ a : ℝ, ∀ x ∈ A, a • x ∈ A) ∧
    (∀ x ∈ A, ∀ y ∈ A, x ⊔ y ∈ A) ∧
    (∀ x ∈ A, ∀ y ∈ A, x ⊓ y ∈ A)

/-- The finite-rank set `S_E` is a vector sublattice, matching the first part
of the paper's Section 5 `S-template`. -/
theorem finiteRank_isVectorSubLattice {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    IsVectorSubLattice (S E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteRank_zero
  · intro x hx y hy
    exact finiteRank_add hx hy
  · intro x hx
    exact finiteRank_neg hx
  · intro a x hx
    exact finiteRank_smul a hx
  · intro x hx y hy
    exact finiteRank_sup hx hy
  · intro x hx y hy
    exact finiteRank_inf hx hy

/-- Completeness for the weighted norm, stated sequentially for this scaffold. -/
def IsCompleteForWeightedNorm {E : Type u} [SeminormedAddCommGroup E]
    (A : Set (V E)) : Prop :=
  ∀ u : ℕ → V E,
    (∀ n : ℕ, u n ∈ A) →
      WeightedCauchy u →
        ∃ x : V E, x ∈ A ∧ WeightedConvergesTo u x

/-- Closedness for the weighted norm. -/
def IsClosedForWeightedNorm {E : Type u} [SeminormedAddCommGroup E]
    (A : Set (V E)) : Prop :=
  ∀ x : V E,
    (∀ ε : ℝ, 0 < ε → ∃ y : V E, y ∈ A ∧ ‖x - y‖ < ε) → x ∈ A

/-- The local meaning of "closed Banach sublattice" used in the Section 5 scaffold. -/
def IsClosedBanachSubLattice {E : Type u} [NormedAddCommGroup E] [SMul ℝ E]
    [NormSMulClass ℝ E] [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
    (A : Set (V E)) : Prop :=
  IsVectorSubLattice A ∧ IsClosedForWeightedNorm A ∧ IsCompleteForWeightedNorm A

/-- Separability for the weighted norm, stated through a countable dense subset. -/
def IsSeparableForWeightedNorm {E : Type u} [SeminormedAddCommGroup E]
    (A : Set (V E)) : Prop :=
  ∃ D : Set (V E),
    Set.Countable D ∧
      D ⊆ A ∧
        ∀ x : V E, x ∈ A →
          ∀ ε : ℝ, 0 < ε → ∃ y : V E, y ∈ D ∧ ‖x - y‖ < ε

/-- A weighted-Cauchy sequence is Cauchy in each coordinate, since every
coordinate seminorm is dominated by the weighted norm. -/
theorem weightedCauchy_coordinate_cauchy {E : Type u} [NormedAddCommGroup E]
    (u : ℕ → V E) (hu : WeightedCauchy u) (s : Node) :
    CauchySeq (fun n : ℕ => u n s) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hεw : 0 < ε * weight s := mul_pos hε (weight_pos s)
  rcases hu (ε * weight s) hεw with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  have hmul : weight s * ‖u m s - u n s‖ < ε * weight s := by
    calc
      weight s * ‖u m s - u n s‖ =
          weight s * ‖(u m - u n : V E) s‖ := rfl
      _ ≤ ‖u m - u n‖ := weighted_coordinate_le_norm (u m - u n) s
      _ < ε * weight s := hN m n hm hn
  have hmul' : weight s * ‖u m s - u n s‖ < weight s * ε := by
    simpa [mul_comm] using hmul
  exact lt_of_mul_lt_mul_left hmul' (weight_nonneg s)

/-- Coordinatewise completeness supplies a limit for each coordinate of a
weighted-Cauchy sequence. -/
theorem weightedCauchy_coordinate_tendsto_exists {E : Type u}
    [NormedAddCommGroup E] [CompleteSpace E] (u : ℕ → V E)
    (hu : WeightedCauchy u) (s : Node) :
    ∃ x : E, Tendsto (fun n : ℕ => u n s) atTop (nhds x) :=
  cauchySeq_tendsto_of_complete (weightedCauchy_coordinate_cauchy u hu s)

/-- Passing a uniform weighted-Cauchy bound to the coordinatewise limit gives
a weighted coordinate distance estimate. -/
theorem weightedLimit_coordinate_distance_le {E : Type u} [NormedAddCommGroup E]
    {u : ℕ → V E} {x : TreeSeq E}
    (hx : ∀ s : Node, Tendsto (fun n : ℕ => u n s) atTop (nhds (x s)))
    {C : ℝ} {N n : ℕ} (_hn : N ≤ n)
    (hC : ∀ m : ℕ, N ≤ m → ‖u n - u m‖ < C) (s : Node) :
    weight s * ‖u n s - x s‖ ≤ C := by
  have hlim_sub :
      Tendsto (fun m : ℕ => u n s - u m s) atTop (nhds (u n s - x s)) :=
    tendsto_const_nhds.sub (hx s)
  have hlim :
      Tendsto (fun m : ℕ => weight s * ‖u n s - u m s‖) atTop
        (nhds (weight s * ‖u n s - x s‖)) :=
    hlim_sub.norm.const_mul (weight s)
  apply le_of_tendsto hlim
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro m hm
  exact le_of_lt <| by
    calc
      weight s * ‖u n s - u m s‖ =
          weight s * ‖(u n - u m : V E) s‖ := rfl
      _ ≤ ‖u n - u m‖ := weighted_coordinate_le_norm (u n - u m) s
      _ < C := hC m hm

/-- The coordinatewise limit of a weighted-Cauchy sequence is still
weighted-bounded, so it belongs to the ambient space `V_E`. -/
theorem weightedLimit_weightedBounded {E : Type u} [NormedAddCommGroup E]
    {u : ℕ → V E} (hu : WeightedCauchy u) {x : TreeSeq E}
    (hx : ∀ s : Node, Tendsto (fun n : ℕ => u n s) atTop (nhds (x s))) :
    WeightedBounded x := by
  rcases hu 1 (by norm_num) with ⟨N, hN⟩
  refine ⟨‖u N‖ + 1, ?_⟩
  intro s
  have hdist : weight s * ‖x s - u N s‖ ≤ 1 := by
    have h := weightedLimit_coordinate_distance_le hx (le_refl N)
      (fun m hm => hN N m (le_refl N) hm) s
    simpa [norm_sub_rev] using h
  calc
    weight s * ‖x s‖ ≤ weight s * (‖u N s‖ + ‖x s - u N s‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg s)
      calc
        ‖x s‖ = ‖u N s + (x s - u N s)‖ := by
          congr 1
          abel
        _ ≤ ‖u N s‖ + ‖x s - u N s‖ := norm_add_le _ _
    _ = weight s * ‖u N s‖ + weight s * ‖x s - u N s‖ := by ring
    _ ≤ ‖u N‖ + 1 :=
      add_le_add (weighted_coordinate_le_norm (u N) s) hdist

/-- Sequential completeness of the ambient weighted space `V_E`, proved by
taking coordinatewise limits and then using the weighted norm estimates. -/
theorem weightedCauchy_exists_limit {E : Type u}
    [NormedAddCommGroup E] [CompleteSpace E] (u : ℕ → V E)
    (hu : WeightedCauchy u) :
    ∃ x : V E, WeightedConvergesTo u x := by
  classical
  choose x hx using fun s : Node => weightedCauchy_coordinate_tendsto_exists u hu s
  let xV : V E := ⟨x, weightedLimit_weightedBounded hu hx⟩
  refine ⟨xV, ?_⟩
  intro ε hε
  have hδ : 0 < ε / 2 := half_pos hε
  rcases hu (ε / 2) hδ with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hcoords : ∀ s : Node, weight s * ‖(u n - xV : V E) s‖ ≤ ε / 2 := by
    intro s
    change weight s * ‖u n s - x s‖ ≤ ε / 2
    exact weightedLimit_coordinate_distance_le hx hn (fun m hm => hN n m hn hm) s
  exact lt_of_le_of_lt (weightedNorm_le_of_forall hcoords) (half_lt_self hε)

/-- Symmetry of the weighted-norm distance. This is the version used in the
closure and completeness arguments for `Z_E`. -/
theorem weightedNorm_sub_rev {E : Type u} [SeminormedAddCommGroup E]
    (x y : V E) :
    ‖x - y‖ = ‖y - x‖ := by
  apply le_antisymm
  · apply weightedNorm_le_of_forall
    intro s
    change weight s * ‖x s - y s‖ ≤ ‖y - x‖
    rw [norm_sub_rev]
    exact weighted_coordinate_le_norm (y - x) s
  · apply weightedNorm_le_of_forall
    intro s
    change weight s * ‖y s - x s‖ ≤ ‖x - y‖
    rw [norm_sub_rev]
    exact weighted_coordinate_le_norm (x - y) s

/-- The closed space `Z_E`, defined as the closure of `S_E`, is a vector
sublattice. This is the sublattice part of Section 5's `S-template`. -/
theorem Z_isVectorSubLattice {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    IsVectorSubLattice (Z E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    refine ⟨0, finiteRank_zero, ?_⟩
    have hle : ‖(0 : V E) - (0 : V E)‖ ≤ 0 := by
      apply weightedNorm_le_of_forall
      intro s
      change weight s * ‖(0 : E) - (0 : E)‖ ≤ 0
      simp
    exact lt_of_le_of_lt hle hε
  · intro x hx y hy ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    rcases hx (ε / 2) hhalf with ⟨u, hu, hxu⟩
    rcases hy (ε / 2) hhalf with ⟨v, hv, hyv⟩
    refine ⟨u + v, finiteRank_add hu hv, ?_⟩
    have hdist := weightedNorm_add_sub_add_le x y u v
    have hsum : ‖x - u‖ + ‖y - v‖ < ε := by linarith
    exact lt_of_le_of_lt hdist hsum
  · intro x hx ε hε
    rcases hx ε hε with ⟨u, hu, hxu⟩
    refine ⟨-u, finiteRank_neg hu, ?_⟩
    exact lt_of_le_of_lt (weightedNorm_neg_sub_neg_le x u) hxu
  · intro a x hx ε hε
    have hden_pos : 0 < ‖a‖ + 1 :=
      add_pos_of_nonneg_of_pos (norm_nonneg a) (by norm_num)
    have hδ : 0 < ε / (‖a‖ + 1) := div_pos hε hden_pos
    rcases hx (ε / (‖a‖ + 1)) hδ with ⟨u, hu, hxu⟩
    refine ⟨a • u, finiteRank_smul a hu, ?_⟩
    have hdist := weightedNorm_smul_sub_smul_le a x u
    have hscale : ‖a‖ * ‖x - u‖ < ε := by
      have hnorm_le : ‖a‖ ≤ ‖a‖ + 1 := by linarith [norm_nonneg a]
      have hmul :
          ‖a‖ * ‖x - u‖ < (‖a‖ + 1) * (ε / (‖a‖ + 1)) :=
        mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hnorm_le hxu
          (weightedNorm_nonneg (x - u)) hden_pos
      have hcancel : (‖a‖ + 1) * (ε / (‖a‖ + 1)) = ε := by
        exact mul_div_cancel₀ ε (ne_of_gt hden_pos)
      rw [hcancel] at hmul
      exact hmul
    exact lt_of_le_of_lt hdist hscale
  · intro x hx y hy ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    rcases hx (ε / 2) hhalf with ⟨u, hu, hxu⟩
    rcases hy (ε / 2) hhalf with ⟨v, hv, hyv⟩
    refine ⟨u ⊔ v, finiteRank_sup hu hv, ?_⟩
    have hdist := weightedNorm_sup_sub_sup_le x y u v
    have hsum : ‖x - u‖ + ‖y - v‖ < ε := by linarith
    exact lt_of_le_of_lt hdist hsum
  · intro x hx y hy ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    rcases hx (ε / 2) hhalf with ⟨u, hu, hxu⟩
    rcases hy (ε / 2) hhalf with ⟨v, hv, hyv⟩
    refine ⟨u ⊓ v, finiteRank_inf hu hv, ?_⟩
    have hdist := weightedNorm_inf_sub_inf_le x y u v
    have hsum : ‖x - u‖ + ‖y - v‖ < ε := by linarith
    exact lt_of_le_of_lt hdist hsum

/-- `Z_E` is closed for the weighted norm, by the usual two-approximation
argument inside the closure of `S_E`. -/
theorem Z_isClosedForWeightedNorm {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    IsClosedForWeightedNorm (Z E) := by
  intro x hx ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases hx (ε / 2) hhalf with ⟨y, hyZ, hxy⟩
  rcases hyZ (ε / 2) hhalf with ⟨u, hu, hyu⟩
  refine ⟨u, hu, ?_⟩
  have hdist := weightedNorm_sub_le x y u
  have hsum : ‖x - y‖ + ‖y - u‖ < ε := by linarith
  exact lt_of_le_of_lt hdist hsum

/-- `Z_E` is complete for the weighted norm: take the ambient weighted limit
and use closedness of `Z_E`. -/
theorem Z_isCompleteForWeightedNorm {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    IsCompleteForWeightedNorm (Z E) := by
  intro u huZ huC
  rcases weightedCauchy_exists_limit u huC with ⟨x, hux⟩
  refine ⟨x, ?_, hux⟩
  apply Z_isClosedForWeightedNorm
  intro ε hε
  rcases hux ε hε with ⟨N, hN⟩
  refine ⟨u N, huZ N, ?_⟩
  simpa [weightedNorm_sub_rev] using hN N (le_refl N)

/-- Bundles the Section 5 conclusions that `Z_E` is a closed Banach
sublattice of the ambient weighted space. -/
theorem Z_isClosedBanachSubLattice {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E] :
    IsClosedBanachSubLattice (Z E) := by
  exact ⟨Z_isVectorSubLattice, Z_isClosedForWeightedNorm, Z_isCompleteForWeightedNorm⟩


end WeightedTree
end DSTBL3
