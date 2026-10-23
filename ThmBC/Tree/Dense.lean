import ThmBC.Tree.FiniteRank

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

universe u

/-- Codes for finite trees whose nodes are labelled by indices into a fixed
dense sequence. -/
def FiniteTreeCode : Type :=
  Σ F : {F : Finset Node // IsFiniteDownwardClosedTree (F : Set Node)},
    ({s : Node // s ∈ F.1} → ℕ)

instance finiteTreeCode_countable : Countable FiniteTreeCode := by
  dsimp [FiniteTreeCode]
  infer_instance

/-- Recursively evaluate a finite-tree labelling, freezing at the last node in
the finite tree once a branch leaves it. -/
noncomputable def finiteTreeApproxAux {E : Type u} (F : Set Node)
    [DecidablePred (· ∈ F)] (a : {s : Node // s ∈ F} → E) :
    Node → (p : Node) → p ∈ F → E
  | [], p, hp => a ⟨p, hp⟩
  | n :: rest, p, hp =>
      if hchild : child p n ∈ F then
        finiteTreeApproxAux F a rest (child p n) hchild
      else
        a ⟨p, hp⟩

/-- A crude norm bound for finite-tree approximants, summing the norms of
all labels. This makes the approximants weighted-bounded. -/
noncomputable def finiteTreeApproxBound {E : Type u} [Norm E]
    (F : Finset Node) (a : {s : Node // s ∈ (F : Set Node)} → E) : ℝ :=
  ∑ q : {q : Node // q ∈ F}, ‖a ⟨q.1, by
    simp⟩‖

/-- Each label is bounded by the finite sum defining
`finiteTreeApproxBound`. -/
theorem finiteTreeApproxBound_one {E : Type u} [SeminormedAddCommGroup E]
    (F : Finset Node) (a : {s : Node // s ∈ (F : Set Node)} → E)
    {p : Node} (hp : p ∈ (F : Set Node)) :
    ‖a ⟨p, hp⟩‖ ≤ finiteTreeApproxBound F a := by
  let pp : {q : Node // q ∈ F} := ⟨p, by
    simpa using hp⟩
  have hsingle :
      (fun q : {q : Node // q ∈ F} => ‖a ⟨q.1, by
        simp⟩‖) pp ≤
        ∑ q : {q : Node // q ∈ F}, ‖a ⟨q.1, by
          simp⟩‖ := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun q : {q : Node // q ∈ F} => ‖a ⟨q.1, by
        simp⟩‖)
      (fun q _ => norm_nonneg (a ⟨q.1, by
        simp⟩)) (by simp)
  simpa [finiteTreeApproxBound, pp] using hsingle

/-- Every value of the recursive finite-tree approximation is bounded by the
finite label sum. -/
theorem finiteTreeApproxAux_norm_le_bound {E : Type u} [SeminormedAddCommGroup E]
    (F : Finset Node) (a : {s : Node // s ∈ (F : Set Node)} → E)
    (r p : Node) (hp : p ∈ (F : Set Node)) :
    ‖finiteTreeApproxAux (F : Set Node) a r p hp‖ ≤ finiteTreeApproxBound F a := by
  induction r generalizing p with
  | nil =>
      simpa [finiteTreeApproxAux] using finiteTreeApproxBound_one F a hp
  | cons n rest ih =>
      by_cases hchild : child p n ∈ (F : Set Node)
      · simp [finiteTreeApproxAux, hchild]
        exact ih (child p n) hchild
      · simp [finiteTreeApproxAux, hchild]
        exact finiteTreeApproxBound_one F a hp

/-- If an appended path stays inside the finite tree, recursive evaluation can
be shifted from the root to the endpoint. -/
theorem finiteTreeApproxAux_append_of_mem {E : Type u} {F : Set Node}
    [DecidablePred (· ∈ F)] (a : {s : Node // s ∈ F} → E)
    (hdown : DownwardClosed F) {p r : Node}
    (hp : p ∈ F) (hpr : p ++ r ∈ F) (t : Node) :
    finiteTreeApproxAux F a (r ++ t) p hp =
      finiteTreeApproxAux F a t (p ++ r) hpr := by
  induction r generalizing p with
  | nil =>
      simp
  | cons n rest ih =>
      have hchild : child p n ∈ F := by
        apply hdown (s := child p n) (t := p ++ n :: rest)
        · exact ⟨rest, by simp [child, List.append_assoc]⟩
        · exact hpr
      simp [finiteTreeApproxAux, hchild]
      have hpr' : child p n ++ rest ∈ F := by
        simpa [child, List.append_assoc] using hpr
      simpa [child, List.append_assoc] using ih hchild hpr'

/-- The finite-tree approximant in `V_E`, used to build the countable dense
subset in Section 5's separability argument for `Z_E`. -/
noncomputable def finiteTreeApprox {E : Type u} [SeminormedAddCommGroup E]
    (F : Finset Node) (hF : IsFiniteDownwardClosedTree (F : Set Node))
    (a : {s : Node // s ∈ (F : Set Node)} → E) : V E :=
  ⟨fun s => finiteTreeApproxAux (F : Set Node) a s root hF.2.1, by
    refine ⟨finiteTreeApproxBound F a, ?_⟩
    intro s
    calc
      weight s * ‖finiteTreeApproxAux (F : Set Node) a s root hF.2.1‖ ≤
          1 * ‖finiteTreeApproxAux (F : Set Node) a s root hF.2.1‖ := by
        exact mul_le_mul_of_nonneg_right (weight_le_one s) (norm_nonneg _)
      _ = ‖finiteTreeApproxAux (F : Set Node) a s root hF.2.1‖ := by ring
      _ ≤ finiteTreeApproxBound F a :=
        finiteTreeApproxAux_norm_le_bound F a s root hF.2.1⟩

/-- A finite-tree approximant is finite-rank, with the same finite tree as
witness. -/
theorem finiteTreeApprox_finiteRank {E : Type u} [SeminormedAddCommGroup E]
    (F : Finset Node) (hF : IsFiniteDownwardClosedTree (F : Set Node))
    (a : {s : Node // s ∈ (F : Set Node)} → E) :
    FiniteRank (finiteTreeApprox F hF a) := by
  refine ⟨(F : Set Node), hF, ?_⟩
  intro s n hs hchild t
  change finiteTreeApproxAux (F : Set Node) a (child s n ++ t) root hF.2.1 =
    finiteTreeApproxAux (F : Set Node) a s root hF.2.1
  calc
    finiteTreeApproxAux (F : Set Node) a (child s n ++ t) root hF.2.1 =
        finiteTreeApproxAux (F : Set Node) a (n :: t) s hs := by
      simpa [root, child, List.append_assoc] using
        finiteTreeApproxAux_append_of_mem (F := (F : Set Node)) a hF.2.2
          hF.2.1 (by simpa [root] using hs) (n :: t)
    _ = a ⟨s, hs⟩ := by
      simp [finiteTreeApproxAux, hchild]
    _ = finiteTreeApproxAux (F : Set Node) a [] s hs := by
      simp [finiteTreeApproxAux]
    _ = finiteTreeApproxAux (F : Set Node) a s root hF.2.1 := by
      symm
      simpa [root] using
        finiteTreeApproxAux_append_of_mem (F := (F : Set Node)) a hF.2.2
          hF.2.1 (by simpa [root] using hs) []

/-- Pointwise closeness of finite-tree labels propagates to pointwise
closeness of the corresponding approximant, using the finite-rank witness
outside the tree. -/
theorem finiteTreeApproxAux_close_of_witness {E : Type u} [SeminormedAddCommGroup E]
    {F : Set Node} [DecidablePred (· ∈ F)] {x : V E}
    (hW : ∀ s : Node, ∀ n : ℕ,
      s ∈ F → child s n ∉ F → ∀ t : Node, x (child s n ++ t) = x s)
    (a : {s : Node // s ∈ F} → E) {δ : ℝ}
    (hclose : ∀ p : {s : Node // s ∈ F}, ‖x p.1 - a p‖ < δ)
    (r p : Node) (hp : p ∈ F) :
    ‖x (p ++ r) - finiteTreeApproxAux F a r p hp‖ < δ := by
  induction r generalizing p with
  | nil =>
      simpa [finiteTreeApproxAux] using hclose ⟨p, hp⟩
  | cons n rest ih =>
      by_cases hchild : child p n ∈ F
      · simp [finiteTreeApproxAux, hchild]
        simpa [child, List.append_assoc] using ih (child p n) hchild
      · have hxconst : x (p ++ n :: rest) = x p := by
          simpa [child, List.append_assoc] using hW p n hp hchild rest
        simp [finiteTreeApproxAux, hchild, hxconst]
        simpa using hclose ⟨p, hp⟩

/-- A canonical finite-rank element coded by a finite tree and labels chosen
from a fixed dense sequence in `E`. -/
noncomputable def finiteTreeDenseElement {E : Type u} [SeminormedAddCommGroup E]
    [TopologicalSpace.SeparableSpace E] (c : FiniteTreeCode) : V E :=
  finiteTreeApprox c.1.1 c.1.2 fun p =>
    TopologicalSpace.denseSeq E (c.2 ⟨p.1, by simp⟩)

/-- The countable family of finite-tree dense elements used to prove
separability of `Z_E` in Section 5. -/
noncomputable def finiteTreeDenseSet (E : Type u) [SeminormedAddCommGroup E]
    [TopologicalSpace.SeparableSpace E] : Set (V E) :=
  Set.range (finiteTreeDenseElement (E := E))

/-- The finite-tree dense family is countable because finite trees and
natural-number labels are countable. -/
theorem finiteTreeDenseSet_countable {E : Type u} [SeminormedAddCommGroup E]
    [TopologicalSpace.SeparableSpace E] :
    Set.Countable (finiteTreeDenseSet E) := by
  exact Set.countable_range (finiteTreeDenseElement (E := E))

/-- Every coded finite-tree dense element is finite-rank. -/
theorem finiteTreeDenseElement_finiteRank {E : Type u} [SeminormedAddCommGroup E]
    [TopologicalSpace.SeparableSpace E] (c : FiniteTreeCode) :
    FiniteRank (finiteTreeDenseElement (E := E) c) := by
  exact finiteTreeApprox_finiteRank c.1.1 c.1.2 _

/-- Finite-rank elements belong to `Z_E` by taking themselves as arbitrarily
close finite-rank approximants. -/
theorem finiteRank_mem_Z {E : Type u} [SeminormedAddCommGroup E] {x : V E}
    (hx : FiniteRank x) :
    x ∈ Z E := by
  intro ε hε
  refine ⟨x, hx, ?_⟩
  have hle : ‖x - x‖ ≤ 0 := by
    apply weightedNorm_le_of_forall
    intro s
    change weight s * ‖x s - x s‖ ≤ 0
    simp
  exact lt_of_le_of_lt hle hε

/-- The finite-tree dense family is a subset of `Z_E`. -/
theorem finiteTreeDenseSet_subset_Z {E : Type u} [SeminormedAddCommGroup E]
    [TopologicalSpace.SeparableSpace E] :
    finiteTreeDenseSet E ⊆ Z E := by
  rintro y ⟨c, rfl⟩
  exact finiteRank_mem_Z (finiteTreeDenseElement_finiteRank (E := E) c)

/-- Every finite-rank element is approximated in weighted norm by the
countable finite-tree dense family. This is the key separability step for
Section 5's `S-template`. -/
theorem finiteRank_approximated_by_finiteTreeDenseSet {E : Type u}
    [NormedAddCommGroup E] [TopologicalSpace.SeparableSpace E]
    {x : V E} (hx : FiniteRank x) :
    ∀ η : ℝ, 0 < η →
      ∃ y : V E, y ∈ finiteTreeDenseSet E ∧ ‖x - y‖ < η := by
  intro η hη
  rcases hx with ⟨F, hF, hW⟩
  let Ffin : Finset Node := hF.1.toFinset
  have hFfin_coe : (Ffin : Set Node) = F := by
    exact hF.1.coe_toFinset
  have hFfin : IsFiniteDownwardClosedTree (Ffin : Set Node) := by
    simpa [Ffin, hFfin_coe] using hF
  let δ : ℝ := η / 2
  have hδ : 0 < δ := half_pos hη
  have hδ_lt : δ < η := half_lt_self hη
  have hnear :
      ∀ p : {s : Node // s ∈ Ffin},
        ∃ k : ℕ, dist (x p.1) (TopologicalSpace.denseSeq E k) < δ := by
    intro p
    exact (TopologicalSpace.denseRange_denseSeq E).exists_dist_lt (x p.1) hδ
  choose k hk using hnear
  let c : FiniteTreeCode := ⟨⟨Ffin, hFfin⟩, k⟩
  let y : V E := finiteTreeDenseElement (E := E) c
  refine ⟨y, ⟨c, rfl⟩, ?_⟩
  have hWfin : ∀ s : Node, ∀ n : ℕ,
      s ∈ (Ffin : Set Node) → child s n ∉ (Ffin : Set Node) →
        ∀ t : Node, x (child s n ++ t) = x s := by
    intro s n hs hchild t
    apply hW s n
    · simpa [hFfin_coe] using hs
    · intro hmem
      exact hchild (by simpa [hFfin_coe] using hmem)
  have hclose :
      ∀ p : {s : Node // s ∈ (Ffin : Set Node)},
        ‖x p.1 -
          TopologicalSpace.denseSeq E (k ⟨p.1, by simp⟩)‖ < δ := by
    intro p
    have hp := hk ⟨p.1, by simp⟩
    simpa [dist_eq_norm] using hp
  have hpoint : ∀ s : Node, ‖x s - y s‖ < δ := by
    intro s
    change ‖x s -
      finiteTreeApproxAux (Ffin : Set Node)
        (fun p : {s : Node // s ∈ (Ffin : Set Node)} =>
          TopologicalSpace.denseSeq E (k ⟨p.1, by simp⟩))
        s root hFfin.2.1‖ < δ
    simpa [root] using
      finiteTreeApproxAux_close_of_witness (F := (Ffin : Set Node)) hWfin
        (fun p : {s : Node // s ∈ (Ffin : Set Node)} =>
          TopologicalSpace.denseSeq E (k ⟨p.1, by simp⟩))
        hclose s root hFfin.2.1
  have hcoords : ∀ s : Node, weight s * ‖(x - y : V E) s‖ ≤ δ := by
    intro s
    change weight s * ‖x s - y s‖ ≤ δ
    exact le_of_lt <| by
      calc
        weight s * ‖x s - y s‖ ≤ 1 * ‖x s - y s‖ := by
          exact mul_le_mul_of_nonneg_right (weight_le_one s) (norm_nonneg _)
        _ = ‖x s - y s‖ := by ring
        _ < δ := hpoint s
  exact lt_of_le_of_lt (weightedNorm_le_of_forall hcoords) hδ_lt

/-- The space `Z_E` is separable for the weighted norm, completing the
separability assertion in Section 5's `S-template`. -/
theorem Z_isSeparableForWeightedNorm {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    IsSeparableForWeightedNorm (Z E) := by
  refine ⟨finiteTreeDenseSet E, finiteTreeDenseSet_countable, finiteTreeDenseSet_subset_Z, ?_⟩
  intro x hx ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases hx (ε / 2) hhalf with ⟨u, hu, hxu⟩
  rcases finiteRank_approximated_by_finiteTreeDenseSet hu (ε / 2) hhalf with
    ⟨y, hyD, huy⟩
  refine ⟨y, hyD, ?_⟩
  have hdist := weightedNorm_sub_le x u y
  have hsum : ‖x - u‖ + ‖u - y‖ < ε := by linarith
  exact lt_of_le_of_lt hdist hsum

/-- Lemma `S-template`: `S_E` is a vector sublattice, and `Z_E` is closed,
Banach, and separable. -/
theorem finiteRank_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] :
    IsVectorSubLattice (S E) ∧
      IsClosedBanachSubLattice (Z E) ∧
        IsSeparableForWeightedNorm (Z E) := by
  exact ⟨finiteRank_isVectorSubLattice, Z_isClosedBanachSubLattice,
    Z_isSeparableForWeightedNorm⟩

/-- A finite set of nodes misses all sufficiently large children of any fixed
node. This is the finitary input for eventual child constancy of finite-rank
elements. -/
theorem finite_set_eventually_child_not_mem {F : Set Node} (hF : F.Finite) (s : Node) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → child s n ∉ F := by
  let A : Set ℕ := {n | child s n ∈ F}
  have hA : A.Finite := by
    have hinj : Set.InjOn (fun n : ℕ => child s n)
        ((fun n : ℕ => child s n) ⁻¹' F) := by
      intro a _ha b _hb h
      have hlist : [a] = [b] := (List.append_right_inj s).mp h
      simpa using hlist
    change ((fun n : ℕ => child s n) ⁻¹' F).Finite
    exact hF.preimage hinj
  rcases hA.exists_le with ⟨M, hM⟩
  refine ⟨M + 1, ?_⟩
  intro n hn hmem
  have hnle : n ≤ M := hM n hmem
  have hlt : M < n := Nat.lt_of_succ_le hn
  exact (not_lt_of_ge hnle) hlt

/-- Finite-rank elements are eventually constant along every family of
children, a fact used in Lemma `child-convergence-template`. -/
theorem finiteRank_eventually_child_eq {E : Type u} [Norm E]
    {u : V E} (hu : FiniteRank u) (s : Node) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → u (child s n) = u s := by
  rcases hu with ⟨F, hF, hW⟩
  by_cases hs : s ∈ F
  · rcases finite_set_eventually_child_not_mem hF.1 s with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    simpa using hW s n hs (hN n hn) []
  · refine ⟨0, ?_⟩
    intro n _hn
    have hconst := finiteRank_constant_subtree_of_not_mem hF hW hs
    simpa [child] using hconst [n]

/-- The weights of all children of a fixed node are equal to one positive
constant. This supplies a uniform lower weight in the child-convergence
argument. -/
theorem child_weight_constant (s : Node) :
    ∃ w : ℝ, 0 < w ∧ ∀ n : ℕ, weight (child s n) = w := by
  by_cases hs : s = root
  · refine ⟨gamma, gamma_pos, ?_⟩
    intro n
    simpa [hs] using weight_child_root n
  · refine ⟨gamma * lambda (lastD s) * weight s, ?_, ?_⟩
    · exact mul_pos (mul_pos gamma_pos (lambda_pos (lastD s))) (weight_pos s)
    · intro n
      exact weight_child_nonroot hs n

/-- A weighted-norm estimate gives an unweighted coordinate estimate whenever
the coordinate weight has a positive lower bound. -/
theorem coordinate_sub_lt_of_weight_lower {E : Type u} [NormedAddCommGroup E]
    {x u : V E} {r : Node} {m η : ℝ}
    (hm_pos : 0 < m) (hm_le : m ≤ weight r)
    (hxu : ‖x - u‖ < (η / 3) * m) :
    ‖x r - u r‖ < η / 3 := by
  have hmul : m * ‖x r - u r‖ < (η / 3) * m := by
    calc
      m * ‖x r - u r‖ ≤ weight r * ‖x r - u r‖ :=
        mul_le_mul_of_nonneg_right hm_le (norm_nonneg _)
      _ = weight r * ‖(x - u : V E) r‖ := rfl
      _ ≤ ‖x - u‖ := weighted_coordinate_le_norm (x - u) r
      _ < (η / 3) * m := hxu
  have hmul' : m * ‖x r - u r‖ < m * (η / 3) := by
    rw [mul_comm (η / 3) m] at hmul
    exact hmul
  exact lt_of_mul_lt_mul_left hmul' (le_of_lt hm_pos)

/-- Lemma `child-convergence-template`: coordinates of elements of `Z_E`
converge along children. -/
theorem child_convergence_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {x : V E}
    (hx : x ∈ Z E) (s : Node) :
    Tendsto (fun n : ℕ => x (child s n)) atTop (nhds (x s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases child_weight_constant s with ⟨w, hw_pos, hw⟩
  let m : ℝ := min (weight s) w
  have hm_pos : 0 < m := lt_min (weight_pos s) hw_pos
  have hm_le_s : m ≤ weight s := min_le_left _ _
  have hm_le_child : ∀ n : ℕ, m ≤ weight (child s n) := by
    intro n
    rw [hw n]
    exact min_le_right _ _
  have hthird : 0 < ε / 3 := by positivity
  have hδ : 0 < (ε / 3) * m := mul_pos hthird hm_pos
  rcases hx ((ε / 3) * m) hδ with ⟨u, hu, hxu⟩
  rcases finiteRank_eventually_child_eq hu s with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [dist_eq_norm]
  have hchilderr : ‖x (child s n) - u (child s n)‖ < ε / 3 :=
    coordinate_sub_lt_of_weight_lower hm_pos (hm_le_child n) hxu
  have hserr : ‖x s - u s‖ < ε / 3 :=
    coordinate_sub_lt_of_weight_lower hm_pos hm_le_s hxu
  have hus : u (child s n) = u s := hN n hn
  calc
    ‖x (child s n) - x s‖ =
        ‖(x (child s n) - u (child s n)) + (u s - x s)‖ := by
      rw [hus]
      congr 1
      abel
    _ ≤ ‖x (child s n) - u (child s n)‖ + ‖u s - x s‖ := norm_add_le _ _
    _ < ε := by
      rw [norm_sub_rev (u s) (x s)]
      linarith


end WeightedTree
end DSTBL3
