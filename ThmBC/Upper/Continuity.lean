import ThmBC.Upper.Basic

/-!
# The upper construction — continuity and branch bounds

This file proves continuity of the pasted upper sequences and constructs the explicit
upper bound associated with an infinite branch.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

open DSTBL3.WeightedTree
open LowerComplete

namespace UpperComplete

/-- A first-exit paste with zero base and a raw sequence bounded by `1`
is still bounded by `1` in every coordinate. -/
theorem pasteAtFirstExitAux_zero_norm_le_one {d : TreeSeq ℝ}
    (hd : ∀ s : Node, ‖d s‖ ≤ (1 : ℝ)) (R : Set Node) :
    ∀ q r : Node, ‖pasteAtFirstExitAux R (0 : ℝ) d q r‖ ≤ (1 : ℝ) := by
  intro q r
  induction r generalizing q with
  | nil =>
      simp [pasteAtFirstExitAux]
  | cons n rest ih =>
      by_cases h : child q n ∈ R
      · have hdec : Classical.dec (child q n ∈ R) = isTrue h := Subsingleton.elim _ _
        simpa [pasteAtFirstExitAux, hdec] using ih (child q n)
      · have hdec : Classical.dec (child q n ∈ R) = isFalse h := Subsingleton.elim _ _
        simpa [pasteAtFirstExitAux, hdec] using hd rest

/-- Two zero-base first-exit pastes of a raw sequence bounded by `1` differ
by at most `2` in every coordinate. -/
theorem pasteAtFirstExitAux_zero_sub_norm_le_two {d : TreeSeq ℝ}
    (hd : ∀ s : Node, ‖d s‖ ≤ (1 : ℝ)) (R U : Set Node) (q r : Node) :
    ‖pasteAtFirstExitAux R (0 : ℝ) d q r -
        pasteAtFirstExitAux U (0 : ℝ) d q r‖ ≤ (2 : ℝ) := by
  calc
    ‖pasteAtFirstExitAux R (0 : ℝ) d q r -
        pasteAtFirstExitAux U (0 : ℝ) d q r‖ ≤
        ‖pasteAtFirstExitAux R (0 : ℝ) d q r‖ +
          ‖pasteAtFirstExitAux U (0 : ℝ) d q r‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      exact add_le_add (pasteAtFirstExitAux_zero_norm_le_one hd R q r)
        (pasteAtFirstExitAux_zero_norm_le_one hd U q r)
    _ = 2 := by norm_num

/-- Main weighted estimate for Lemma `u-upper-continuous`: if two trees agree
on the finite lower-continuity control set, their upper first-exit pastes are
weighted-close. -/
theorem pasteAtFirstExitAux_zero_controlled_weighted_sub_le {d : TreeSeq ℝ}
    (hd_root : d root = 0) (hd : ∀ s : Node, ‖d s‖ ≤ (1 : ℝ))
    {ε : ℝ} (hε : 0 < ε) {T U : Tree}
    (hTU : ∀ s : Node, s ∈ lowerContinuityControlSet (ε / 4) →
      (s ∈ (T : Set Node) ↔ s ∈ (U : Set Node))) :
    ∀ q r : Node,
      weight (q ++ r) *
        ‖pasteAtFirstExitAux (T : Set Node) (0 : ℝ) d q r -
          pasteAtFirstExitAux (U : Set Node) (0 : ℝ) d q r‖ ≤ ε / 2 := by
  intro q r
  induction r generalizing q with
  | nil =>
      have hhalf : 0 ≤ ε / 2 := by linarith
      simpa [pasteAtFirstExitAux] using hhalf
  | cons n rest ih =>
      by_cases hT : child q n ∈ (T : Set Node)
      · by_cases hU : child q n ∈ (U : Set Node)
        · have hT' : q ++ [n] ∈ (T : Set Node) := by simpa [child] using hT
          have hU' : q ++ [n] ∈ (U : Set Node) := by simpa [child] using hU
          have hdecT : Classical.dec (q ++ [n] ∈ (T : Set Node)) = isTrue hT' :=
            Subsingleton.elim _ _
          have hdecU : Classical.dec (q ++ [n] ∈ (U : Set Node)) = isTrue hU' :=
            Subsingleton.elim _ _
          simpa [pasteAtFirstExitAux, hdecT, hdecU, child, List.append_assoc] using
            ih (child q n)
        · cases rest with
          | nil =>
              have hdecT : Classical.dec (child q n ∈ (T : Set Node)) = isTrue hT :=
                Subsingleton.elim _ _
              have hdecU : Classical.dec (child q n ∈ (U : Set Node)) = isFalse hU :=
                Subsingleton.elim _ _
              have hroot : d [] = 0 := by simpa [root] using hd_root
              have hhalf : 0 ≤ ε / 2 := by linarith
              simpa [pasteAtFirstExitAux, hdecT, hdecU, hroot] using hhalf
          | cons a tail =>
              have hp_ne : child q n ≠ root := child_ne_root q n
              have hp_not_control : child q n ∉ lowerContinuityControlSet (ε / 4) := by
                intro hp
                exact hU ((hTU (child q n) hp).mp hT)
              have hBlt : properExtensionWeightBound (child q n) < ε / 4 := by
                have hnot_le : ¬ ε / 4 ≤ properExtensionWeightBound (child q n) := by
                  intro hle
                  exact hp_not_control ⟨hp_ne, hle⟩
                exact lt_of_not_ge hnot_le
              have hweight : weight (q ++ (n :: a :: tail)) ≤ ε / 4 := by
                calc
                  weight (q ++ (n :: a :: tail)) =
                      weight (child q n ++ (a :: tail)) := by
                    simp [child, List.append_assoc]
                  _ ≤ properExtensionWeightBound (child q n) :=
                    weight_proper_extension_le_bound hp_ne a tail
                  _ ≤ ε / 4 := le_of_lt hBlt
              have hnorm :=
                pasteAtFirstExitAux_zero_sub_norm_le_two hd (T : Set Node) (U : Set Node)
                  q (n :: a :: tail)
              have hquarter_nonneg : 0 ≤ ε / 4 := by linarith
              calc
                weight (q ++ (n :: a :: tail)) *
                    ‖pasteAtFirstExitAux (T : Set Node) (0 : ℝ) d q (n :: a :: tail) -
                      pasteAtFirstExitAux (U : Set Node) (0 : ℝ) d q (n :: a :: tail)‖
                    ≤ (ε / 4) * 2 := by
                  exact mul_le_mul hweight hnorm (norm_nonneg _) hquarter_nonneg
                _ = ε / 2 := by ring
      · by_cases hU : child q n ∈ (U : Set Node)
        · cases rest with
          | nil =>
              have hdecT : Classical.dec (child q n ∈ (T : Set Node)) = isFalse hT :=
                Subsingleton.elim _ _
              have hdecU : Classical.dec (child q n ∈ (U : Set Node)) = isTrue hU :=
                Subsingleton.elim _ _
              have hroot : d [] = 0 := by simpa [root] using hd_root
              have hhalf : 0 ≤ ε / 2 := by linarith
              simpa [pasteAtFirstExitAux, hdecT, hdecU, hroot] using hhalf
          | cons a tail =>
              have hp_ne : child q n ≠ root := child_ne_root q n
              have hp_not_control : child q n ∉ lowerContinuityControlSet (ε / 4) := by
                intro hp
                exact hT ((hTU (child q n) hp).mpr hU)
              have hBlt : properExtensionWeightBound (child q n) < ε / 4 := by
                have hnot_le : ¬ ε / 4 ≤ properExtensionWeightBound (child q n) := by
                  intro hle
                  exact hp_not_control ⟨hp_ne, hle⟩
                exact lt_of_not_ge hnot_le
              have hweight : weight (q ++ (n :: a :: tail)) ≤ ε / 4 := by
                calc
                  weight (q ++ (n :: a :: tail)) =
                      weight (child q n ++ (a :: tail)) := by
                    simp [child, List.append_assoc]
                  _ ≤ properExtensionWeightBound (child q n) :=
                    weight_proper_extension_le_bound hp_ne a tail
                  _ ≤ ε / 4 := le_of_lt hBlt
              have hnorm :=
                pasteAtFirstExitAux_zero_sub_norm_le_two hd (T : Set Node) (U : Set Node)
                  q (n :: a :: tail)
              have hquarter_nonneg : 0 ≤ ε / 4 := by linarith
              calc
                weight (q ++ (n :: a :: tail)) *
                    ‖pasteAtFirstExitAux (T : Set Node) (0 : ℝ) d q (n :: a :: tail) -
                      pasteAtFirstExitAux (U : Set Node) (0 : ℝ) d q (n :: a :: tail)‖
                    ≤ (ε / 4) * 2 := by
                  exact mul_le_mul hweight hnorm (norm_nonneg _) hquarter_nonneg
                _ = ε / 2 := by ring
        · have hdecT : Classical.dec (child q n ∈ (T : Set Node)) = isFalse hT :=
            Subsingleton.elim _ _
          have hdecU : Classical.dec (child q n ∈ (U : Set Node)) = isFalse hU :=
            Subsingleton.elim _ _
          have hhalf : 0 ≤ ε / 2 := by linarith
          simpa [pasteAtFirstExitAux, hdecT, hdecU] using hhalf

/-- Paper Lemma `u-upper-in-Y`: for every tree `R`, each pasted element
`u_m^R` lies in `Y_+`, and the sequence
`0 ≤ u_1^R ≤ u_2^R ≤ ...` is increasing. -/
theorem u_upper_in_Y_template (R : Tree) :
    (∀ m : ℕ, uUpper R m ∈ Y) ∧ IsPositiveIncreasing (uUpperSeq R) := by
  exact ⟨uUpper_mem_Y R,
    ⟨uUpper_coordinate_nonnegative R, uUpper_increasing R⟩⟩

/-- Paper Lemma `u-upper-continuous`: for fixed `m`, the map
`R ↦ u_m^R` is continuous.  The paper proves this by the same finite-control
argument as the lower construction: if two trees first differ at `r`, any
difference lies strictly below `r`, where the weights are controlled by
`B(r)`. -/
theorem u_upper_continuous_template :
    (∀ m : ℕ, TreeToWeightedContinuous (fun R : Tree => uUpper R m)) ∧
      TreeToSequenceContinuous (fun R : Tree => uUpperSeq R) := by
  have hweighted : ∀ m : ℕ, TreeToWeightedContinuous (fun R : Tree => uUpper R m) := by
    intro m T ε hε
    have hd_norm : ∀ s : Node, ‖upperSequenceRaw m s‖ ≤ (1 : ℝ) := by
      intro s
      cases s with
      | nil =>
          simp [upperSequenceRaw]
      | cons j rest =>
          by_cases h : j ≤ m
          · simp [upperSequenceRaw, h]
          · simp [upperSequenceRaw, h]
    let δ : ℝ := ε / 4
    have hδpos : 0 < δ := by
      dsimp [δ]
      linarith
    let A : Finset Node := (lowerContinuityControlSet_finite hδpos).toFinset
    have hAcoe : (A : Set Node) = lowerContinuityControlSet δ := by
      dsimp [A]
      exact (lowerContinuityControlSet_finite hδpos).coe_toFinset
    refine ⟨A, ?_⟩
    intro U hU
    have hTU : ∀ s : Node, s ∈ lowerContinuityControlSet (ε / 4) →
        (s ∈ (T : Set Node) ↔ s ∈ (U : Set Node)) := by
      intro s hs
      apply hU s
      have hsAset : s ∈ (A : Set Node) := by
        simpa [hAcoe, δ] using hs
      simpa using hsAset
    have hcoords : ∀ s : Node,
        weight s * ‖((uUpper T m - uUpper U m : V ℝ) s)‖ ≤ ε / 2 := by
      intro s
      change weight s * ‖uUpperRaw T m s - uUpperRaw U m s‖ ≤ ε / 2
      simpa [uUpperRaw, root] using
        pasteAtFirstExitAux_zero_controlled_weighted_sub_le
          (by simp [upperSequenceRaw, root]) hd_norm hε hTU root s
    exact lt_of_le_of_lt (weightedNorm_le_of_forall hcoords) (half_lt_self hε)
  exact ⟨hweighted, by
    intro m
    simpa [uUpperSeq] using hweighted m⟩

/-- The reduction map `Phi(T) = (u_m^{\widehat T})_m`. -/
noncomputable def phiUpper (T : Tree) : ℕ → V ℝ :=
  uUpperSeq (fatten T)

/-- Formalizes the continuity assertion immediately after the definition of
`Φ`: combine continuity of fattening with Lemma `u-upper-continuous`. -/
theorem phi_upper_continuous_template :
    TreeToSequenceContinuous phiUpper := by
  intro m T ε hε
  rcases (u_upper_continuous_template.1 m) (fatten T) ε hε with ⟨B, hB⟩
  choose C hC using fattening_template.1
  let A : Finset Node := B.biUnion C
  refine ⟨A, ?_⟩
  intro U hU
  have hfat_agree : ∀ s : Node, s ∈ B →
      (s ∈ (fatten T : Set Node) ↔ s ∈ (fatten U : Set Node)) := by
    intro s hs
    exact hC s T U (by
      intro a ha
      apply hU a
      exact Finset.mem_biUnion.mpr ⟨s, hs, ha⟩)
  simpa [phiUpper, uUpperSeq] using hB (fatten U) hfat_agree

/-- Formalizes the same paragraph after the definition of `Φ`: for every
tree `T`, the sequence `Φ(T)` lies in `Y^↑`, i.e. it is positive, increasing,
and all its terms are in `Y`. -/
theorem phi_upper_increasing_template (T : Tree) :
    (∀ m : ℕ, phiUpper T m ∈ Y) ∧ IsPositiveIncreasing (phiUpper T) := by
  simpa [phiUpper, uUpperSeq] using u_upper_in_Y_template (fatten T)

/-- The branch upper-bound witness `y^b`: it is `0` on the branch cone `L_b`
and `1` outside it. -/
noncomputable def branchConeComplementIndicatorRaw (b : ℕ → ℕ) : TreeSeq ℝ :=
  fun s =>
    match Classical.dec (s ∈ BranchCone b) with
    | isTrue _ => 0
    | isFalse _ => 1

/-- Boundedness of the branch-cone complement `y^b` from Proposition
`upper-IF`: its coordinates are exactly `0` on `L_b` and `1` off `L_b`, so it
is weighted bounded before being bundled as an element of `V_ℝ`. -/
theorem branchConeComplementIndicatorRaw_weightedBounded (b : ℕ → ℕ) :
    WeightedBounded (branchConeComplementIndicatorRaw b) := by
  refine ⟨1, ?_⟩
  intro s
  have hnorm : ‖branchConeComplementIndicatorRaw b s‖ ≤ (1 : ℝ) := by
    by_cases h : s ∈ BranchCone b
    · have hdec : Classical.dec (s ∈ BranchCone b) = isTrue h := Subsingleton.elim _ _
      simp [branchConeComplementIndicatorRaw, hdec]
    · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse h := Subsingleton.elim _ _
      simp [branchConeComplementIndicatorRaw, hdec]
  calc
    weight s * ‖branchConeComplementIndicatorRaw b s‖ ≤ 1 * (1 : ℝ) := by
      exact mul_le_mul (weight_le_one s) hnorm (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The element `y^b ∈ V_ℝ`. -/
noncomputable def branchConeComplementIndicator (b : ℕ → ℕ) : V ℝ :=
  ⟨branchConeComplementIndicatorRaw b,
    branchConeComplementIndicatorRaw_weightedBounded b⟩

/-- Formalizes the claim in Proposition `upper-IF` that `y^b ∈ Y`: the
branch cone contains the root, so the root value is `0`, and the eventual
constancy template gives membership in `Z_ℝ`. -/
theorem branchConeComplementIndicator_mem_Y (b : ℕ → ℕ) :
    branchConeComplementIndicator b ∈ Y := by
  refine ⟨?_, ?_⟩
  · apply eventually_constant_template (branchConeComplementIndicator b)
    · refine ⟨1, ?_⟩
      intro s
      change ‖branchConeComplementIndicatorRaw b s‖ ≤ (1 : ℝ)
      by_cases hs : s ∈ BranchCone b
      · have hdec : Classical.dec (s ∈ BranchCone b) = isTrue hs :=
          Subsingleton.elim _ _
        simp [branchConeComplementIndicatorRaw, hdec]
      · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse hs :=
          Subsingleton.elim _ _
        simp [branchConeComplementIndicatorRaw, hdec]
    · intro s
      change ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        branchConeComplementIndicatorRaw b (child s n) =
          branchConeComplementIndicatorRaw b s
      by_cases hs : s ∈ BranchCone b
      · refine ⟨b s.length, ?_⟩
        intro n hn
        have hchild : child s n ∈ BranchCone b := by
          have hle :
              PointwiseLE (child (initialSegment b s.length) (b s.length))
                (child s n) :=
            pointwiseLE_child hs hn
          simpa [BranchCone, child, initialSegment_succ] using hle
        have hdec_child : Classical.dec (child s n ∈ BranchCone b) = isTrue hchild :=
          Subsingleton.elim _ _
        have hdec_s : Classical.dec (s ∈ BranchCone b) = isTrue hs :=
          Subsingleton.elim _ _
        simp [branchConeComplementIndicatorRaw, hdec_child, hdec_s]
      · refine ⟨0, ?_⟩
        intro n _hn
        have hchild : child s n ∉ BranchCone b := by
          intro hchild
          exact hs ((branchCone_isTree b).2 ⟨[n], by simp [child]⟩ hchild)
        have hdec_child : Classical.dec (child s n ∈ BranchCone b) = isFalse hchild :=
          Subsingleton.elim _ _
        have hdec_s : Classical.dec (s ∈ BranchCone b) = isFalse hs :=
          Subsingleton.elim _ _
        simp [branchConeComplementIndicatorRaw, hdec_child, hdec_s]
  · have hroot_mem : root ∈ BranchCone b := by
      simp [BranchCone, root, initialSegment, PointwiseLE]
    have hdec : Classical.dec (root ∈ BranchCone b) = isTrue hroot_mem :=
      Subsingleton.elim _ _
    simp [branchConeComplementIndicator, branchConeComplementIndicatorRaw, hdec]

/-- Positivity of the upper-bound witness `y^b` in Proposition `upper-IF`:
the indicator complement only takes the values `0` and `1`. -/
theorem branchConeComplementIndicator_coordinate_nonnegative (b : ℕ → ℕ) :
    CoordinatewiseNonnegative (branchConeComplementIndicator b) := by
  intro s
  change 0 ≤ branchConeComplementIndicatorRaw b s
  by_cases hs : s ∈ BranchCone b
  · have hdec : Classical.dec (s ∈ BranchCone b) = isTrue hs := Subsingleton.elim _ _
    simp [branchConeComplementIndicatorRaw, hdec]
  · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse hs := Subsingleton.elim _ _
    simp [branchConeComplementIndicatorRaw, hdec]

/-- The upper-bound element `y^b` constructed in Proposition `upper-IF`.
If `b` is an infinite branch through `T`, then the branch cone lies inside
`\widehat T`; on the cone both sides are `0`, and off the cone `y^b = 1`
dominates every `u_m^{\widehat T}`. -/
theorem branchConeComplement_upper_bound_template
    {T : Tree} {b : ℕ → ℕ} (hb : IsBranch (T : Set Node) b) :
    IsOrderUpperBoundInY (branchConeComplementIndicator b) (phiUpper T) := by
  refine ⟨branchConeComplementIndicator_mem_Y b, ?_⟩
  intro m s
  change uUpperRaw (fatten T) m s ≤ branchConeComplementIndicatorRaw b s
  by_cases hs : s ∈ BranchCone b
  · have hbranch := (fattening_template.2.2 T b hb).1
    have hu : uUpperRaw (fatten T) m s = 0 := by
      simpa [uUpperRaw, root] using
        pasteAtFirstExitAux_eq_base_of_subtree hbranch.1 hbranch.2 (0 : ℝ)
          (upperSequenceRaw m) root s (by simp [root, hs])
    have hdec : Classical.dec (s ∈ BranchCone b) = isTrue hs := Subsingleton.elim _ _
    simp [branchConeComplementIndicatorRaw, hdec, hu]
  · have hdec : Classical.dec (s ∈ BranchCone b) = isFalse hs := Subsingleton.elim _ _
    have hd_norm : ∀ r : Node, ‖upperSequenceRaw m r‖ ≤ (1 : ℝ) := by
      intro r
      cases r with
      | nil =>
          simp [upperSequenceRaw]
      | cons j rest =>
          by_cases h : j ≤ m
          · simp [upperSequenceRaw, h]
          · simp [upperSequenceRaw, h]
    have hnorm : ‖uUpperRaw (fatten T) m s‖ ≤ (1 : ℝ) := by
      simpa [uUpperRaw] using
        pasteAtFirstExitAux_zero_norm_le_one hd_norm (fatten T : Set Node) root s
    have hle : uUpperRaw (fatten T) m s ≤ (1 : ℝ) :=
      (le_abs_self (uUpperRaw (fatten T) m s)).trans
        (by simpa [Real.norm_eq_abs] using hnorm)
    simpa [branchConeComplementIndicatorRaw, hdec] using hle

end UpperComplete
end WeightedTree
end DSTBL3
