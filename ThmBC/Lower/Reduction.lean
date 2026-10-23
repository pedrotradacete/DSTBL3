import ThmBC.Lower.Continuity

/-!
# The lower construction — tree reduction

This file proves the ill-founded and well-founded directions of the tree reduction,
including the branch-cone lower bound and the dead-subtree argument.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree
namespace LowerComplete

open DSTBL3.WeightedTree

universe u

/-- In Proposition `lower-IF`, the branch-cone indicator `y^a` belongs to
`Z_E`: it is bounded and eventually constant along children by the fattening
lemma. -/
theorem branchConeIndicator_mem_Z {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] (e : E)
    {T : Tree} {b : ℕ → ℕ} (hb : IsBranch (T : Set Node) b) :
    branchConeIndicator e b ∈ Z E := by
  apply eventually_constant_template
  · refine ⟨‖e‖, ?_⟩
    intro s
    change ‖branchConeIndicatorRaw e b s‖ ≤ ‖e‖
    by_cases hs : s ∈ BranchCone b
    · have hdec : Classical.dec (s ∈ BranchCone b) = isTrue hs := Subsingleton.elim _ _
      simp [branchConeIndicatorRaw, hdec]
    · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse hs := Subsingleton.elim _ _
      simp [branchConeIndicatorRaw, hdec]
  · intro s
    by_cases hs : s ∈ BranchCone b
    · have hevent := (fattening_template.2.2 T b hb).2 s hs
      rcases eventually_atTop.1 hevent with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      change branchConeIndicatorRaw e b (child s n) = branchConeIndicatorRaw e b s
      have hchild : child s n ∈ BranchCone b := hN n hn
      have hdec_child : Classical.dec (child s n ∈ BranchCone b) = isTrue hchild :=
        Subsingleton.elim _ _
      have hdec_s : Classical.dec (s ∈ BranchCone b) = isTrue hs := Subsingleton.elim _ _
      simp [branchConeIndicatorRaw, hdec_child, hdec_s]
    · refine ⟨0, ?_⟩
      intro n _hn
      change branchConeIndicatorRaw e b (child s n) = branchConeIndicatorRaw e b s
      have hchild : child s n ∉ BranchCone b := by
        intro hchild
        exact hs ((branchCone_isTree b).2 ⟨[n], by simp [child]⟩ hchild)
      have hdec_child : Classical.dec (child s n ∈ BranchCone b) = isFalse hchild :=
        Subsingleton.elim _ _
      have hdec_s : Classical.dec (s ∈ BranchCone b) = isFalse hs := Subsingleton.elim _ _
      simp [branchConeIndicatorRaw, hdec_child, hdec_s]

/-- Positivity of the branch-cone indicator `y^a` used as a nonzero lower
bound in Proposition `lower-IF`. -/
theorem branchConeIndicator_coordinate_nonnegative {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) (b : ℕ → ℕ) :
    CoordinatewiseNonnegative (branchConeIndicator e b) := by
  intro s
  change 0 ≤ branchConeIndicatorRaw e b s
  by_cases hs : s ∈ BranchCone b
  · have hdec : Classical.dec (s ∈ BranchCone b) = isTrue hs := Subsingleton.elim _ _
    simpa [branchConeIndicatorRaw, hdec] using he.1
  · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse hs := Subsingleton.elim _ _
    simp [branchConeIndicatorRaw, hdec]

/-- The branch-cone indicator is nonzero because its root coordinate is `e`
and `‖e‖ = 1`. -/
theorem branchConeIndicator_ne_zero {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) (b : ℕ → ℕ) :
    branchConeIndicator e b ≠ 0 := by
  intro hzero
  have hroot_mem : root ∈ BranchCone b := by
    simp [BranchCone, root, initialSegment, PointwiseLE]
  have hdec : Classical.dec (root ∈ BranchCone b) = isTrue hroot_mem := Subsingleton.elim _ _
  have hroot : e = 0 := by
    have h := congrArg (fun x : V E => x root) hzero
    change branchConeIndicatorRaw e b root = (0 : E) at h
    simpa [branchConeIndicator, branchConeIndicatorRaw, hdec] using h
  have hnorm : ‖e‖ = 0 := by rw [hroot, norm_zero]
  rw [he.2] at hnorm
  norm_num at hnorm

/-- If a subtree `A` is contained in `R`, then first-exit pasting remains at
the base value `e` throughout `A`. This is used for branch cones inside the
fattened tree. -/
theorem pasteAtFirstExitAux_eq_base_of_subtree {E : Type u} [Zero E]
    {A R : Set Node} (hA : IsTree A) (hsub : A ⊆ R)
    (e : E) (d : TreeSeq E) :
    ∀ q r : Node, q ++ r ∈ A → pasteAtFirstExitAux R e d q r = e := by
  intro q r hqr
  induction r generalizing q with
  | nil =>
      simp [pasteAtFirstExitAux]
  | cons n rest ih =>
      have hprefix : Prefix (child q n) (q ++ (n :: rest)) := by
        refine ⟨rest, ?_⟩
        simp [child, List.append_assoc]
      have hchildA : child q n ∈ A := by
        exact hA.2 hprefix (by simpa [List.append_assoc] using hqr)
      have hchildR : q ++ [n] ∈ R := by
        simpa [child] using hsub hchildA
      have hdec : Classical.dec (q ++ [n] ∈ R) = isTrue hchildR := Subsingleton.elim _ _
      simpa [pasteAtFirstExitAux, hdec, child, List.append_assoc] using
        ih (child q n) (by simpa [child, List.append_assoc] using hqr)

/-- Along the branch cone of an infinite branch through `T`, the pasted
sequence `z_m^{\widehat T}` stays at the base value `e`. -/
theorem zLowerRaw_eq_base_of_branchCone {E : Type u} [Zero E]
    (e : E) (m : ℕ) {T : Tree} {b : ℕ → ℕ}
    (hb : IsBranch (T : Set Node) b) {s : Node} (hs : s ∈ BranchCone b) :
    zLowerRaw (fatten T) e m s = e := by
  have hbranch := (fattening_template.2.2 T b hb).1
  exact pasteAtFirstExitAux_eq_base_of_subtree hbranch.1 hbranch.2 e
    (deadSequenceRaw e m) root s (by simp [root, hs])

/-- The branch-cone indicator `y^a` lies below every coordinate of
`Theta(T)` when `a` is an infinite branch through `T`. -/
theorem branchConeIndicator_le_theta {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e)
    {T : Tree} {b : ℕ → ℕ} (hb : IsBranch (T : Set Node) b) :
    ∀ m : ℕ, CoordinatewiseLE (branchConeIndicator e b) (thetaLower e T m) := by
  intro m s
  change branchConeIndicatorRaw e b s ≤ zLowerRaw (fatten T) e (m + 1) s
  by_cases hs : s ∈ BranchCone b
  · have hdec : Classical.dec (s ∈ BranchCone b) = isTrue hs := Subsingleton.elim _ _
    have hz : zLowerRaw (fatten T) e (m + 1) s = e :=
      zLowerRaw_eq_base_of_branchCone e (m + 1) hb hs
    simp [branchConeIndicatorRaw, hdec, hz]
  · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse hs := Subsingleton.elim _ _
    have hnonneg := zLowerSeq_coordinate_nonnegative he (fatten T) m s
    change 0 ≤ zLowerRaw (fatten T) e (m + 1) s at hnonneg
    simpa [branchConeIndicatorRaw, hdec] using hnonneg

/-- The lower-bound element `y^a` constructed from an infinite branch. -/
theorem branchConeIndicator_lower_bound_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    {T : Tree} {b : ℕ → ℕ} (hb : IsBranch (T : Set Node) b) :
    IsNonzeroPositiveLowerBoundInZ (branchConeIndicator e b) (thetaLower e T) := by
  exact ⟨branchConeIndicator_mem_Z e hb,
    branchConeIndicator_coordinate_nonnegative he b,
    branchConeIndicator_ne_zero he b,
    branchConeIndicator_le_theta he hb⟩

/-- Lemma `lower-IF`: ill-founded trees are sent outside `X_{\downarrow 0}`. -/
theorem lower_IF_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    {T : Tree} :
    ¬ WellFoundedTree (T : Set Node) → ¬ XDownarrowZero (thetaLower e T) := by
  intro hIF hdown
  have hbranch : ∃ b : ℕ → ℕ, IsBranch (T : Set Node) b := by
    by_contra hbranch
    exact hIF hbranch
  rcases hbranch with ⟨b, hb⟩
  exact hdown.2.2 ⟨branchConeIndicator e b, branchConeIndicator_lower_bound_template he hb⟩

/-- First-exit calculation for the pasted sequence: once the path leaves
`R` at `q concat n`, the remaining value is exactly the pasted sequence `d`. -/
theorem pasteAtFirstExitAux_eq_of_first_exit {E : Type u} [Zero E]
    (R : Tree) (e : E) (d : TreeSeq E) :
    ∀ p q : Node, ∀ n : ℕ, ∀ r : Node,
      p ++ q ∈ (R : Set Node) → child (p ++ q) n ∉ (R : Set Node) →
        pasteAtFirstExitAux (R : Set Node) e d p (q ++ (n :: r)) = d r := by
  intro p q n r hpq hexit
  induction q generalizing p with
  | nil =>
      have hnot : child p n ∉ (R : Set Node) := by simpa using hexit
      have hdec : Classical.dec (child p n ∈ (R : Set Node)) = isFalse hnot :=
        Subsingleton.elim _ _
      simp [pasteAtFirstExitAux, hdec]
  | cons a qs ih =>
      have hprefix : Prefix (child p a) (p ++ (a :: qs)) := by
        refine ⟨qs, ?_⟩
        simp [child, List.append_assoc]
      have hchild_mem : child p a ∈ (R : Set Node) := R.2.2 hprefix hpq
      have hchild_mem' : p ++ [a] ∈ (R : Set Node) := by simpa [child] using hchild_mem
      have hdec : Classical.dec (p ++ [a] ∈ (R : Set Node)) = isTrue hchild_mem' :=
        Subsingleton.elim _ _
      have hexit' : child (child p a ++ qs) n ∉ (R : Set Node) := by
        simpa [child, List.append_assoc] using hexit
      have hpq' : child p a ++ qs ∈ (R : Set Node) := by
        simpa [child, List.append_assoc] using hpq
      simpa [pasteAtFirstExitAux, hdec, child, List.append_assoc] using ih (child p a) hpq' hexit'

/-- Specialized first-exit calculation for `z_m^R`: below the first exit it
is a copy of the raw dead sequence `d_m`. -/
theorem zLowerRaw_eq_deadSequenceRaw_of_first_exit {E : Type u} [Zero E]
    (R : Tree) (e : E) (m : ℕ) {q : Node} {n : ℕ}
    (hq : q ∈ (R : Set Node)) (hexit : child q n ∉ (R : Set Node)) (r : Node) :
    zLowerRaw R e m (child q n ++ r) = deadSequenceRaw e m r := by
  simpa [zLowerRaw, root, child, List.append_assoc] using
    pasteAtFirstExitAux_eq_of_first_exit R e (deadSequenceRaw e m) root q n r
      (by simpa [root] using hq) (by simpa [root] using hexit)

/-- Lemma `dead-subtree`: below a first exit from `R`, every positive lower
bound of all `z_m^R` vanishes. -/
theorem dead_subtree_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (_he : UnitPositiveElement e)
    {R : Tree} {q : Node} {n : ℕ} {x : V E} :
    q ∈ (R : Set Node) →
      child q n ∉ (R : Set Node) →
        x ∈ Z E →
          CoordinatewiseNonnegative x →
            (∀ m : ℕ, CoordinatewiseLE x (zLower R e (m + 1))) →
              ∀ r : Node, x (child q n ++ r) = 0 := by
  intro hq hexit hxZ hxNonneg hxle r
  have hdead : ∀ m : ℕ, ∀ r : Node,
      zLowerRaw R e m (child q n ++ r) = deadSequenceRaw e m r := by
    intro m r
    exact zLowerRaw_eq_deadSequenceRaw_of_first_exit R e m hq hexit r
  have hchild_zero : ∀ k : ℕ, x (child (child q n) k) = 0 := by
    intro k
    have hx_le : x (child (child q n) k) ≤
        zLower R e ((k + 1) + 1) (child (child q n) k) :=
      hxle (k + 1) (child (child q n) k)
    have htarget : zLower R e ((k + 1) + 1) (child (child q n) k) = 0 := by
      change zLowerRaw R e ((k + 1) + 1) (child (child q n) k) = 0
      have hz := hdead ((k + 1) + 1) [k]
      simpa [child, deadSequenceRaw] using hz
    have hx_le_zero : x (child (child q n) k) ≤ 0 := by
      simpa [htarget] using hx_le
    exact le_antisymm hx_le_zero (hxNonneg (child (child q n) k))
  have htend := child_convergence_template hxZ (child q n)
  have hevent : (fun k : ℕ => x (child (child q n) k)) =ᶠ[atTop]
      (fun _ : ℕ => (0 : E)) :=
    Filter.Eventually.of_forall hchild_zero
  have hexit_zero : x (child q n) = 0 :=
    tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hevent
  cases r with
  | nil =>
      simpa using hexit_zero
  | cons a rest =>
      have hx_le : x (child q n ++ (a :: rest)) ≤
          zLower R e ((a + 1) + 1) (child q n ++ (a :: rest)) :=
        hxle (a + 1) (child q n ++ (a :: rest))
      have htarget : zLower R e ((a + 1) + 1) (child q n ++ (a :: rest)) = 0 := by
        change zLowerRaw R e ((a + 1) + 1) (child q n ++ (a :: rest)) = 0
        have hz := hdead ((a + 1) + 1) (a :: rest)
        simpa [deadSequenceRaw] using hz
      have hx_le_zero : x (child q n ++ (a :: rest)) ≤ 0 := by
        simpa [htarget] using hx_le
      exact le_antisymm hx_le_zero (hxNonneg (child q n ++ (a :: rest)))

/-- Extend an infinite sequence by prefixing a finite node. This packages the
branch built inside the proof of Proposition `lower-WF`. -/
def extendBranch (s : Node) (a : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if h : i < s.length then s.get ⟨i, h⟩ else a (i - s.length)

/-- Initial segments of an extended branch split as the finite prefix followed
by an initial segment of the tail. -/
theorem initialSegment_extendBranch_add (s : Node) (a : ℕ → ℕ) (k : ℕ) :
    initialSegment (extendBranch s a) (s.length + k) = s ++ initialSegment a k := by
  induction k with
  | zero =>
      unfold initialSegment extendBranch
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp
  | succ k ih =>
      rw [show s.length + (k + 1) = (s.length + k) + 1 by omega]
      rw [initialSegment_succ, ih, initialSegment_succ]
      have hnot : ¬ s.length + k < s.length := by omega
      have hsub : s.length + k - s.length = k := by omega
      simp [extendBranch, hnot, hsub, child, List.append_assoc]

/-- Short initial segments of an extended branch recover the corresponding
prefix of the finite node. -/
theorem initialSegment_extendBranch_le (s : Node) (a : ℕ → ℕ) {k : ℕ}
    (hk : k ≤ s.length) :
    initialSegment (extendBranch s a) k = s.take k := by
  unfold initialSegment extendBranch
  apply List.ext_getElem
  · simp [hk]
  · intro i hi1 hi2
    have hi_k : i < k := by simpa using hi1
    have hi_s : i < s.length := lt_of_lt_of_le hi_k hk
    simp [hi_s]

/-- If all finite extensions `s ++ a|k` stay in a tree, then the prefixed
infinite sequence is a branch through that tree. -/
theorem extendBranch_isBranch {R : Tree} {s : Node} {a : ℕ → ℕ}
    (hsR : s ∈ (R : Set Node))
    (hpath : ∀ k : ℕ, s ++ initialSegment a k ∈ (R : Set Node)) :
    IsBranch (R : Set Node) (extendBranch s a) := by
  intro k
  by_cases hk : k ≤ s.length
  · have hEq := initialSegment_extendBranch_le s a hk
    have hprefix : Prefix (s.take k) s := by
      refine ⟨s.drop k, ?_⟩
      exact (List.take_append_drop k s).symm
    have hmem : s.take k ∈ (R : Set Node) := R.2.2 hprefix hsR
    simpa [hEq] using hmem
  · have hle : s.length ≤ k := le_of_not_ge hk
    have hks : s.length + (k - s.length) = k := Nat.add_sub_of_le hle
    have hEq : initialSegment (extendBranch s a) k =
        s ++ initialSegment a (k - s.length) := by
      calc
        initialSegment (extendBranch s a) k =
            initialSegment (extendBranch s a) (s.length + (k - s.length)) := by
              rw [hks]
        _ = s ++ initialSegment a (k - s.length) :=
            initialSegment_extendBranch_add s a (k - s.length)
    simpa [hEq] using hpath (k - s.length)

/-- A nonzero coordinate of an element of `Z_E` has a nonzero child; otherwise
child convergence would force the coordinate to vanish. -/
theorem exists_nonzero_child {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {x : V E} (hxZ : x ∈ Z E)
    {s : Node} (hs : x s ≠ 0) :
    ∃ n : ℕ, x (child s n) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have htend := child_convergence_template hxZ s
  have hevent : (fun n : ℕ => x (child s n)) =ᶠ[atTop] (fun _ : ℕ => (0 : E)) :=
    Filter.Eventually.of_forall hnone
  have hs0 : x s = 0 :=
    tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hevent
  exact hs hs0

/-- Any path from a node in `R` to a node outside `R` has a first exit. This
is the tree-combinatorial input for Lemma `dead-subtree`. -/
theorem exists_first_exit {R : Tree} :
    ∀ p r : Node, p ∈ (R : Set Node) → p ++ r ∉ (R : Set Node) →
      ∃ q : Node, ∃ n : ℕ, ∃ t : Node,
        q ∈ (R : Set Node) ∧ child q n ∉ (R : Set Node) ∧
          p ++ r = child q n ++ t := by
  intro p r hp hpr
  induction r generalizing p with
  | nil =>
      exfalso
      exact hpr (by simpa using hp)
  | cons n rest ih =>
      by_cases hchild : child p n ∈ (R : Set Node)
      · have hnot : child p n ++ rest ∉ (R : Set Node) := by
          simpa [child, List.append_assoc] using hpr
        rcases ih (child p n) hchild hnot with ⟨q, k, t, hq, hexit, hEq⟩
        refine ⟨q, k, t, hq, hexit, ?_⟩
        simpa [child, List.append_assoc] using hEq
      · refine ⟨p, n, rest, hp, hchild, ?_⟩
        simp [child, List.append_assoc]

/-- In the well-founded direction, any positive lower bound of all
`Theta(T)` coordinates must vanish outside the fattened tree. -/
theorem eq_zero_of_not_mem_fatten {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    {T : Tree} {x : V E}
    (hxZ : x ∈ Z E) (hxNonneg : CoordinatewiseNonnegative x)
    (hxle : ∀ m : ℕ, CoordinatewiseLE x (thetaLower e T m)) :
    ∀ s : Node, s ∉ (fatten T : Set Node) → x s = 0 := by
  intro s hs
  rcases exists_first_exit (R := fatten T) root s (fatten T).2.1
      (by simpa [root] using hs) with
    ⟨q, n, t, hq, hexit, hEq⟩
  have hEq' : s = child q n ++ t := by simpa [root] using hEq
  have hzero := dead_subtree_template he hq hexit hxZ hxNonneg (by
    intro m r
    simpa [thetaLower, zLowerSeq] using hxle m r) t
  simpa [hEq'] using hzero

/-- Core contradiction for Proposition `lower-WF`: a nonzero positive lower
bound would generate an infinite branch through the well-founded fattening. -/
theorem no_nonzero_lower_bound_of_wellFounded {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    {T : Tree} (hWF : WellFoundedTree (T : Set Node))
    {x : V E} (hxZ : x ∈ Z E) (hxNonneg : CoordinatewiseNonnegative x)
    (hxne : x ≠ 0) (hxle : ∀ m : ℕ, CoordinatewiseLE x (thetaLower e T m)) :
    False := by
  have hRWF : WellFoundedTree (fatten T : Set Node) := (fattening_template.2.1 T).1 hWF
  have hzero_not_mem := eq_zero_of_not_mem_fatten he hxZ hxNonneg hxle
  have hxcoord : ∃ s : Node, x s ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hxzero : x = 0 := by
      apply Subtype.ext
      funext s
      exact hnone s
    exact hxne hxzero
  rcases hxcoord with ⟨s0, hs0nz⟩
  have hs0R : s0 ∈ (fatten T : Set Node) := by
    by_contra hsnot
    exact hs0nz (hzero_not_mem s0 hsnot)
  let childIndex : {s : Node // x s ≠ 0} → ℕ := fun s =>
    Classical.choose (exists_nonzero_child hxZ s.2)
  let nextNode : {s : Node // x s ≠ 0} → {s : Node // x s ≠ 0} := fun s =>
    ⟨child s.1 (childIndex s), Classical.choose_spec (exists_nonzero_child hxZ s.2)⟩
  let zseq : ℕ → {s : Node // x s ≠ 0} := fun k =>
    Nat.rec ⟨s0, hs0nz⟩ (fun _ s => nextNode s) k
  let a : ℕ → ℕ := fun k => childIndex (zseq k)
  have hzseq_succ : ∀ k : ℕ, (zseq (k + 1)).1 = child (zseq k).1 (a k) := by
    intro k
    rfl
  have hzseq_path : ∀ k : ℕ, (zseq k).1 = s0 ++ initialSegment a k := by
    intro k
    induction k with
    | zero =>
        simp [zseq, initialSegment]
    | succ k ih =>
        rw [hzseq_succ k, ih, initialSegment_succ]
        simp [child, List.append_assoc]
  have hzseq_R : ∀ k : ℕ, (zseq k).1 ∈ (fatten T : Set Node) := by
    intro k
    by_contra hnot
    exact (zseq k).2 (hzero_not_mem (zseq k).1 hnot)
  have hpath : ∀ k : ℕ, s0 ++ initialSegment a k ∈ (fatten T : Set Node) := by
    intro k
    simpa [hzseq_path k] using hzseq_R k
  exact hRWF ⟨extendBranch s0 a, extendBranch_isBranch hs0R hpath⟩

/-- Lemma `lower-WF`: well-founded trees are sent into `X_{\downarrow 0}`. -/
theorem lower_WF_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    {T : Tree} :
    WellFoundedTree (T : Set Node) → XDownarrowZero (thetaLower e T) := by
  intro hWF
  have htheta := theta_lower_template he
  refine ⟨(htheta.2 T).1, (htheta.2 T).2, ?_⟩
  rintro ⟨x, hxZ, hxNonneg, hxne, hxle⟩
  exact no_nonzero_lower_bound_of_wellFounded he hWF hxZ hxNonneg hxne hxle

/-- The reduction property proved from `lower-IF` and `lower-WF`. -/
theorem lower_reduction_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    (T : Tree) :
    WellFoundedTree (T : Set Node) ↔ XDownarrowZero (thetaLower e T) := by
  constructor
  · exact lower_WF_template he
  · intro hdown
    by_contra hWF
    exact lower_IF_template he hWF hdown

end LowerComplete
end WeightedTree
end DSTBL3
