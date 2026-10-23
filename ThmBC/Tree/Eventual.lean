import ThmBC.Tree.Dense

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

universe u

/-- Uniform boundedness in the unweighted coordinate norm. -/
def UnweightedBounded {E : Type u} [Norm E] (u : V E) : Prop :=
  ∃ M : ℝ, ∀ s : Node, ‖u s‖ ≤ M

/-- Eventual constancy along every family of children. -/
def EventuallyConstantAlongChildren {E : Type u} [Norm E] (u : V E) : Prop :=
  ∀ s : Node, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → u (child s n) = u s

/-- The bound `B(r)` on weights strictly below a non-root node. -/
noncomputable def properExtensionWeightBound (r : Node) : ℝ :=
  gamma * lambda (lastD r) * weight r

/-- The finite controlled tree generated from child cutoffs `N`. It is the
approximating finite tree used in Lemma `eventually-constant-template`. -/
def controlledTree (N : Node → ℕ) : ℕ → Finset Node
  | 0 => {root}
  | k + 1 =>
      controlledTree N k ∪
        (controlledTree N k).biUnion fun s =>
          (Finset.range (N s)).image fun n => child s n

/-- Controlled trees increase with the depth parameter. -/
theorem controlledTree_mono (N : Node → ℕ) (k : ℕ) :
    (controlledTree N k : Set Node) ⊆ controlledTree N (k + 1) := by
  intro s hs
  simp [controlledTree, hs]

/-- The root belongs to every controlled tree, matching the finite-tree
witness requirement in Section 5. -/
theorem controlledTree_root_mem (N : Node → ℕ) (k : ℕ) :
    root ∈ controlledTree N k := by
  induction k with
  | zero =>
      simp [controlledTree]
  | succ k ih =>
      exact controlledTree_mono N k ih

/-- Nodes in the `k`th controlled tree have length at most `k`. -/
theorem controlledTree_length_le (N : Node → ℕ) {k : ℕ} {s : Node}
    (hs : s ∈ controlledTree N k) :
    s.length ≤ k := by
  induction k generalizing s with
  | zero =>
      simp [controlledTree] at hs
      simp [hs, root]
  | succ k ih =>
      simp [controlledTree] at hs
      rcases hs with hs | hs
      · exact Nat.le_trans (ih hs) (Nat.le_succ k)
      · rcases hs with ⟨p, hp, n, _hn, rfl⟩
        simpa [child] using ih hp

/-- A child whose index is below the local cutoff enters the next controlled
tree. -/
theorem controlledTree_child_mem_next {N : Node → ℕ} {k : ℕ}
    {s : Node} {n : ℕ} (hs : s ∈ controlledTree N k) (hn : n < N s) :
    child s n ∈ controlledTree N (k + 1) := by
  simp [controlledTree]
  exact Or.inr ⟨s, hs, n, hn, rfl⟩

/-- If a controlled node is not at the maximal depth, allowed children already
belong to the same controlled tree. -/
theorem controlledTree_child_mem_of_length_lt {N : Node → ℕ} {L : ℕ}
    {s : Node} {n : ℕ} (hs : s ∈ controlledTree N L)
    (hlen : s.length < L) (hn : n < N s) :
    child s n ∈ controlledTree N L := by
  induction L generalizing s n with
  | zero =>
      omega
  | succ k ih =>
      simp [controlledTree] at hs
      rcases hs with hs_old | hs_new
      · exact controlledTree_child_mem_next hs_old hn
      · rcases hs_new with ⟨p, hp, m, hm, hpm⟩
        subst hpm
        have hp_len : p.length < k := by
          simp [child] at hlen
          omega
        have hs_in_k : child p m ∈ controlledTree N k := ih hp hp_len hm
        exact controlledTree_child_mem_next hs_in_k hn

/-- Parent-closure of controlled trees, a step toward downward closedness. -/
theorem controlledTree_parent_mem (N : Node → ℕ) {k : ℕ} {s : Node} {n : ℕ}
    (hchild : child s n ∈ controlledTree N k) :
    s ∈ controlledTree N k := by
  induction k generalizing s n with
  | zero =>
      simp [controlledTree] at hchild
      have hlen := congrArg List.length hchild
      simp [child, root] at hlen
  | succ k ih =>
      simp [controlledTree] at hchild
      rcases hchild with hchild_old | hchild_new
      · exact controlledTree_mono N k (ih hchild_old)
      · rcases hchild_new with ⟨p, hp, m, _hm, hpm⟩
        have hlen : p.length = s.length := by
          have hlen_eq := congrArg List.length hpm
          simp [child] at hlen_eq
          omega
        have hp_eq : p = s := List.append_inj_left hpm hlen
        subst hp_eq
        exact controlledTree_mono N k hp

/-- Controlled trees are downward closed, as required of finite-rank witness
trees in Section 5. -/
theorem controlledTree_downwardClosed (N : Node → ℕ) (k : ℕ) :
    DownwardClosed (controlledTree N k : Set Node) := by
  intro s t hst ht
  rcases hst with ⟨u, rfl⟩
  induction u using List.reverseRecOn generalizing s with
  | nil =>
      simpa using ht
  | append_singleton u n ih =>
      have hchild : child (s ++ u) n ∈ controlledTree N k := by
        simpa [child, List.append_assoc] using ht
      have hparent : s ++ u ∈ controlledTree N k :=
        controlledTree_parent_mem N hchild
      exact ih hparent

/-- Each controlled tree is a finite downward closed tree containing the root,
so it can serve as a finite-rank witness. -/
theorem controlledTree_isFiniteDownwardClosedTree (N : Node → ℕ) (k : ℕ) :
    IsFiniteDownwardClosedTree (controlledTree N k : Set Node) := by
  constructor
  · exact (controlledTree N k).finite_toSet
  · exact ⟨controlledTree_root_mem N k, controlledTree_downwardClosed N k⟩

/-- The chosen Section 5 constant `gamma = 1/10` is at most `1/2`, allowing
comparison with the powers defining `lambda`. -/
theorem gamma_le_half : gamma ≤ (2 : ℝ)⁻¹ := by
  norm_num [gamma]

/-- Powers of `gamma` are dominated by the corresponding `lambda` factors.
This is the main decay estimate behind `weight_le_lambda_length`. -/
theorem gamma_pow_le_lambda (n : ℕ) :
    gamma ^ n ≤ lambda n := by
  have h := pow_le_pow_left₀ gamma_nonneg gamma_le_half n
  simpa [lambda, inv_pow] using h

/-- Section 5 decay estimate: the weight of a node is bounded by
`lambda` of its length. -/
theorem weight_le_lambda_length (s : Node) :
    weight s ≤ lambda s.length := by
  unfold weight
  calc
    gamma ^ s.length * lambdaPrefixProduct s ≤ gamma ^ s.length * 1 :=
      mul_le_mul_of_nonneg_left (lambdaPrefixProduct_le_one s)
        (pow_nonneg gamma_nonneg s.length)
    _ = gamma ^ s.length := by ring
    _ ≤ lambda s.length := gamma_pow_le_lambda s.length

/-- The sequence `lambda_n` tends to zero, expressed in the eventual form
used to choose finite approximation depths. -/
theorem lambda_eventually_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → lambda n < δ := by
  rcases pow_unbounded_of_one_lt (δ⁻¹) (by norm_num : (1 : ℝ) < 2) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  unfold lambda
  have hpow_le : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hlt : δ⁻¹ < (2 : ℝ) ^ n := lt_of_lt_of_le hN hpow_le
  exact (inv_lt_comm₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n) hδ).mpr hlt

/-- Child weights never exceed parent weights. This monotonicity is repeatedly
used in Section 5 weighted-norm estimates. -/
theorem weight_child_le (s : Node) (n : ℕ) :
    weight (child s n) ≤ weight s := by
  by_cases hs : s = root
  · subst hs
    rw [weight_child_root, weight_root]
    exact gamma_le_one
  · rw [weight_child_nonroot hs n]
    calc
      gamma * lambda (lastD s) * weight s ≤ 1 * weight s := by
        refine mul_le_mul_of_nonneg_right ?_ (weight_nonneg s)
        calc
          gamma * lambda (lastD s) ≤ 1 * lambda (lastD s) :=
            mul_le_mul_of_nonneg_right gamma_le_one (lambda_nonneg (lastD s))
          _ ≤ 1 := by simpa using lambda_le_one (lastD s)
      _ = weight s := by ring

/-- Appending a tail to a node can only decrease the Section 5 weight. -/
theorem weight_append_le_left (s t : Node) :
    weight (s ++ t) ≤ weight s := by
  induction t generalizing s with
  | nil =>
      simp
  | cons n rest ih =>
      calc
        weight (s ++ (n :: rest)) = weight (child s n ++ rest) := by
          simp [child, List.append_assoc]
        _ ≤ weight (child s n) := ih (child s n)
        _ ≤ weight s := weight_child_le s n

/-- The last coordinate of a child is the child index. -/
theorem lastD_child (s : Node) (n : ℕ) :
    lastD (child s n) = n := by
  induction s with
  | nil =>
      simp [child, lastD]
  | cons _ rest ih =>
      cases rest with
      | nil =>
          simp [child, lastD]
      | cons b bs =>
          change lastD (child (b :: bs) n) = n
          exact ih

/-- A two-step descendant after `child s n` has weight at most `lambda n`.
This is the estimate used to make first-exit discrepancies small. -/
theorem weight_child_cons_append_le_lambda (s : Node) (n m : ℕ) (t : Node) :
    weight (child s n ++ (m :: t)) ≤ lambda n := by
  let q := child s n
  have hq : q ≠ root := by
    intro h
    have hlen := congrArg List.length h
    simp [q, child, root] at hlen
  calc
    weight (child s n ++ (m :: t)) = weight (child q m ++ t) := by
      simp [q, child, List.append_assoc]
    _ ≤ weight (child q m) := weight_append_le_left (child q m) t
    _ = gamma * lambda n * weight q := by
      rw [weight_child_nonroot hq m, lastD_child]
    _ ≤ lambda n := by
      calc
        gamma * lambda n * weight q ≤ 1 * lambda n * 1 := by
          refine mul_le_mul
            (mul_le_mul gamma_le_one (le_refl _) (lambda_nonneg n) zero_le_one)
            (weight_le_one q) (weight_nonneg q) ?_
          exact mul_nonneg zero_le_one (lambda_nonneg n)
        _ = lambda n := by ring

/-- Lemma `eventually-constant-template`: uniformly bounded indexed sequences
which are eventually constant along children belong to `Z_E`. -/
theorem eventually_constant_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] (u : V E)
    (hbounded : UnweightedBounded u)
    (heventually : EventuallyConstantAlongChildren u) :
    u ∈ Z E := by
  intro ε hε
  rcases hbounded with ⟨M, hM⟩
  let B : ℝ := M + 1
  have hM_nonneg : 0 ≤ M := (norm_nonneg (u root)).trans (hM root)
  have hBpos : 0 < B := by
    dsimp [B]
    linarith
  have hB : ∀ s : Node, ‖u s‖ ≤ B := by
    intro s
    dsimp [B]
    linarith [hM s]
  let C : ℝ := 2 * B
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  let δ : ℝ := ρ / C
  have hδ : 0 < δ := div_pos hρ hCpos
  have hδC : δ * C = ρ := by
    dsimp [δ]
    exact div_mul_cancel₀ ρ (ne_of_gt hCpos)
  rcases lambda_eventually_lt hδ with ⟨L, hL⟩
  choose Nevent hNevent using heventually
  let T : Node → ℕ := fun s => max (Nevent s) L
  have hT_event : ∀ s : Node, ∀ n : ℕ, T s ≤ n → u (child s n) = u s := by
    intro s n hn
    exact hNevent s n ((le_max_left (Nevent s) L).trans hn)
  have hT_large : ∀ s : Node, L ≤ T s := by
    intro s
    exact le_max_right (Nevent s) L
  let F : Finset Node := controlledTree T L
  have hF : IsFiniteDownwardClosedTree (F : Set Node) := by
    exact controlledTree_isFiniteDownwardClosedTree T L
  let v : V E := finiteTreeApprox F hF fun p => u p.1
  have hnormdiff : ∀ a b : Node, ‖u a - u b‖ ≤ C := by
    intro a b
    calc
      ‖u a - u b‖ ≤ ‖u a‖ + ‖u b‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB a) (hB b)
      _ = C := by
        dsimp [C]
        ring
  have hsmall_weight :
      ∀ {q p : Node}, weight q < δ → weight q * ‖u q - u p‖ < ρ := by
    intro q p hw
    calc
      weight q * ‖u q - u p‖ ≤ weight q * C :=
        mul_le_mul_of_nonneg_left (hnormdiff q p) (weight_nonneg q)
      _ < δ * C :=
        mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hw (le_refl C) (weight_nonneg q) hCpos
      _ = ρ := hδC
  have herror :
      ∀ p r : Node, ∀ hp : p ∈ (F : Set Node),
        weight (p ++ r) *
            ‖u (p ++ r) -
              finiteTreeApproxAux (F : Set Node) (fun q : {s : Node // s ∈ (F : Set Node)} =>
                u q.1) r p hp‖ < ρ := by
    intro p r
    induction r generalizing p with
    | nil =>
        intro hp
        simp [finiteTreeApproxAux, hρ]
    | cons n rest ih =>
        intro hp
        by_cases hchild : child p n ∈ (F : Set Node)
        · have hrec := ih (child p n) hchild
          have hpn : p ++ n :: rest = child p n ++ rest := by
            simp [child, List.append_assoc]
          rw [hpn]
          rw [finiteTreeApproxAux, dite_eq_left hchild]
          exact hrec
        · have hpn : p ++ n :: rest = child p n ++ rest := by
            simp [child, List.append_assoc]
          rw [hpn]
          rw [finiteTreeApproxAux, dite_eq_right hchild]
          change weight (child p n ++ rest) * ‖u (child p n ++ rest) - u p‖ < ρ
          by_cases hplen : p.length < L
          · have hn_ge : T p ≤ n := by
              exact le_of_not_gt fun hnlt =>
                hchild (controlledTree_child_mem_of_length_lt hp hplen hnlt)
            cases rest with
            | nil =>
                have hz : weight (child p n) * ‖u (child p n) - u p‖ < ρ := by
                  rw [hT_event p n hn_ge]
                  simp [hρ]
                simpa using hz
            | cons m tail =>
                have hlambda_n : lambda n < δ := hL n ((hT_large p).trans hn_ge)
                have hw : weight (child p n ++ (m :: tail)) < δ := by
                  have hle : weight (child p n ++ (m :: tail)) ≤ lambda n :=
                    weight_child_cons_append_le_lambda p n m tail
                  exact lt_of_le_of_lt hle hlambda_n
                simpa using (hsmall_weight (q := child p n ++ (m :: tail)) (p := p) hw)
          · have hlen : L ≤ (child p n ++ rest).length := by
              have hpL : L ≤ p.length := le_of_not_gt hplen
              simp [child]
              omega
            have hw : weight (child p n ++ rest) < δ :=
              lt_of_le_of_lt (weight_le_lambda_length (child p n ++ rest))
                (hL (child p n ++ rest).length hlen)
            simpa using (hsmall_weight (q := child p n ++ rest) (p := p) hw)
  refine ⟨v, finiteTreeApprox_finiteRank F hF _, ?_⟩
  have hcoords : ∀ s : Node, weight s * ‖(u - v : V E) s‖ ≤ ρ := by
    intro s
    change weight s *
        ‖u s -
          finiteTreeApproxAux (F : Set Node) (fun q : {s : Node // s ∈ (F : Set Node)} =>
            u q.1) s root hF.2.1‖ ≤ ρ
    simpa [root] using le_of_lt (herror root s hF.2.1)
  exact lt_of_le_of_lt (weightedNorm_le_of_forall hcoords) (half_lt_self hε)


end WeightedTree
end DSTBL3
