import ThmBC.Lower.Basic

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree
namespace LowerComplete

universe u

/-- Infimum-zero part of Lemma `dead-sequence`: a positive lower bound below
all `d_m` must vanish, using child convergence at the root. -/
theorem deadSequenceSeq_infimum_zero {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} :
    HasInfimumZeroInZ (deadSequenceSeq e) := by
  rintro ⟨y, hyZ, hyNonneg, hyne, hyle⟩
  have hchild_zero : ∀ n : ℕ, y (child root n) = 0 := by
    intro n
    have hy_le : y (child root n) ≤ deadSequenceSeq e (n + 1) (child root n) :=
      hyle (n + 1) (child root n)
    have htarget : deadSequenceSeq e (n + 1) (child root n) = 0 := by
      change deadSequenceRaw e ((n + 1) + 1) (child root n) = 0
      simp [deadSequenceRaw, child, root]
    have hy_le_zero : y (child root n) ≤ 0 := by
      simpa [htarget] using hy_le
    exact le_antisymm hy_le_zero (hyNonneg (child root n))
  have htend := child_convergence_template hyZ root
  have hevent : (fun n : ℕ => y (child root n)) =ᶠ[atTop] (fun _ : ℕ => (0 : E)) :=
    Filter.Eventually.of_forall hchild_zero
  have hroot0 : y root = 0 :=
    tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hevent
  have hcoord_zero : ∀ s : Node, y s = 0 := by
    intro s
    cases s with
    | nil =>
        exact hroot0
    | cons n rest =>
        have hy_le : y (n :: rest) ≤ deadSequenceSeq e (n + 1) (n :: rest) :=
          hyle (n + 1) (n :: rest)
        have htarget : deadSequenceSeq e (n + 1) (n :: rest) = 0 := by
          change deadSequenceRaw e ((n + 1) + 1) (n :: rest) = 0
          simp [deadSequenceRaw]
        have hy_le_zero : y (n :: rest) ≤ 0 := by
          simpa [htarget] using hy_le
        exact le_antisymm hy_le_zero (hyNonneg (n :: rest))
  have hy_eq_zero : y = 0 := by
    apply Subtype.ext
    funext s
    exact hcoord_zero s
  exact hyne hy_eq_zero

/-- Lemma `dead-sequence`: the elements `d_m` lie in `X_+`, form a decreasing
sequence, and have infimum zero. -/
theorem dead_sequence_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e) :
    (∀ m : ℕ, deadSequenceSeq e m ∈ Z E ∧
      CoordinatewiseNonnegative (deadSequenceSeq e m)) ∧
      IsPositiveDecreasing (deadSequenceSeq e) ∧
        HasInfimumZeroInZ (deadSequenceSeq e) := by
  refine ⟨?_, ?_, deadSequenceSeq_infimum_zero⟩
  · intro m
    exact ⟨deadSequence_mem_Z e (m + 1), deadSequenceSeq_coordinate_nonnegative he m⟩
  · exact ⟨deadSequenceSeq_coordinate_nonnegative he, deadSequenceSeq_decreasing he⟩

/-- Lemma `z-lower-in-X`: for every tree `R`, the elements `z_m^R` lie in
`X_+` and form a decreasing sequence. -/
theorem z_lower_in_X_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e)
    (R : Tree) :
    (∀ m : ℕ, zLowerSeq R e m ∈ Z E ∧ CoordinatewiseNonnegative (zLowerSeq R e m)) ∧
      IsPositiveDecreasing (zLowerSeq R e) := by
  refine ⟨?_, ?_⟩
  · intro m
    exact ⟨zLower_mem_Z R e (m + 1), zLowerSeq_coordinate_nonnegative he R m⟩
  · exact ⟨zLowerSeq_coordinate_nonnegative he R, zLowerSeq_decreasing he R⟩

/-- Nonnegativity of the proper-extension bound `B(r)` used in the proof of
Lemma `z-lower-continuous`. -/
theorem properExtensionWeightBound_nonneg (r : Node) :
    0 ≤ properExtensionWeightBound r := by
  unfold properExtensionWeightBound
  exact mul_nonneg (mul_nonneg gamma_nonneg (lambda_nonneg (lastD r))) (weight_nonneg r)

/-- The proper-extension bound below `r` is no larger than the weight of `r`. -/
theorem properExtensionWeightBound_le_weight (r : Node) :
    properExtensionWeightBound r ≤ weight r := by
  unfold properExtensionWeightBound
  calc
    gamma * lambda (lastD r) * weight r ≤ 1 * weight r := by
      refine mul_le_mul_of_nonneg_right ?_ (weight_nonneg r)
      calc
        gamma * lambda (lastD r) ≤ 1 * lambda (lastD r) :=
          mul_le_mul_of_nonneg_right gamma_le_one (lambda_nonneg (lastD r))
        _ ≤ 1 := by simpa using lambda_le_one (lastD r)
    _ = weight r := by ring

/-- Recursive formula for `B(r)` on nodes with at least two coordinates. -/
theorem properExtensionWeightBound_cons_cons_eq (b c : ℕ) (rest : Node) :
    properExtensionWeightBound (b :: c :: rest) =
      gamma * lambda b * properExtensionWeightBound (c :: rest) := by
  simp [properExtensionWeightBound, weight, lambdaPrefixProduct, lastD, pow_succ]
  ring

/-- Dropping the first coordinate can only increase the proper-extension
bound. -/
theorem properExtensionWeightBound_cons_le_tail (b c : ℕ) (rest : Node) :
    properExtensionWeightBound (b :: c :: rest) ≤
      properExtensionWeightBound (c :: rest) := by
  rw [properExtensionWeightBound_cons_cons_eq]
  calc
    gamma * lambda b * properExtensionWeightBound (c :: rest) ≤
        1 * properExtensionWeightBound (c :: rest) := by
      refine mul_le_mul_of_nonneg_right ?_ (properExtensionWeightBound_nonneg (c :: rest))
      calc
        gamma * lambda b ≤ 1 * lambda b :=
          mul_le_mul_of_nonneg_right gamma_le_one (lambda_nonneg b)
        _ ≤ 1 := by simpa using lambda_le_one b
    _ = properExtensionWeightBound (c :: rest) := by ring

/-- Any node beginning with `a` has proper-extension bound controlled by
`lambda a`. -/
theorem properExtensionWeightBound_cons_le_lambda (a : ℕ) (rest : Node) :
    properExtensionWeightBound (a :: rest) ≤ lambda a := by
  cases rest with
  | nil =>
      dsimp [properExtensionWeightBound]
      calc
        gamma * lambda a * weight [a] ≤ 1 * lambda a * 1 := by
          refine mul_le_mul ?_ (weight_le_one [a]) (weight_nonneg [a]) ?_
          · exact mul_le_mul gamma_le_one (le_refl _) (lambda_nonneg a) zero_le_one
          · exact mul_nonneg zero_le_one (lambda_nonneg a)
        _ = lambda a := by ring
  | cons b bs =>
      exact (properExtensionWeightBound_le_weight (a :: b :: bs)).trans
        (by simpa [root, child] using weight_child_cons_append_le_lambda root a b bs)

/-- If a coordinate `a` occurs in a node, then `B(r) ≤ lambda a`. This is the
coordinate cutoff used to prove finiteness of continuity control sets. -/
theorem properExtensionWeightBound_le_lambda_of_mem {a : ℕ} :
    ∀ {r : Node}, a ∈ r → properExtensionWeightBound r ≤ lambda a := by
  intro r ha
  induction r with
  | nil =>
      simp at ha
  | cons b rest ih =>
      rcases List.mem_cons.mp ha with h | h
      · subst h
        exact properExtensionWeightBound_cons_le_lambda a rest
      · cases rest with
        | nil => simp at h
        | cons c cs =>
            exact (properExtensionWeightBound_cons_le_tail b c cs).trans (ih h)

/-- Constant-cutoff controlled trees contain every node of bounded length
whose coordinates are all below the cutoff. -/
theorem controlledTree_const_mem_of_length_lt_of_forall_mem_lt {N : ℕ} :
    ∀ r : Node, r.length < N → (∀ a : ℕ, a ∈ r → a < N) →
      r ∈ controlledTree (fun _ : Node => N) N := by
  intro r hlen hcoord
  induction r using List.reverseRecOn with
  | nil =>
      exact controlledTree_root_mem (fun _ : Node => N) N
  | append_singleton p n ih =>
      have hp_len : p.length < N := by
        simp at hlen
        omega
      have hp_coord : ∀ a : ℕ, a ∈ p → a < N := by
        intro a ha
        exact hcoord a (by simp [ha])
      have hp_mem : p ∈ controlledTree (fun _ : Node => N) N := ih hp_len hp_coord
      have hn_lt : n < N := hcoord n (by simp)
      simpa [child] using controlledTree_child_mem_of_length_lt (N := fun _ : Node => N)
        (L := N) hp_mem hp_len hn_lt

/-- The continuity control set from the proof of `z-lower-continuous` is
finite for every positive `ε`. -/
theorem lowerContinuityControlSet_finite {ε : ℝ} (hε : 0 < ε) :
    (lowerContinuityControlSet ε).Finite := by
  rcases lambda_eventually_lt hε with ⟨N, hN⟩
  refine ((controlledTree (fun _ : Node => N) N).finite_toSet).subset ?_
  intro r hr
  have hεB : ε ≤ properExtensionWeightBound r := hr.2
  have hlen_lt : r.length < N := by
    by_contra hnot
    have hNlen : N ≤ r.length := le_of_not_gt hnot
    have hlt : lambda r.length < ε := hN r.length hNlen
    have hle : properExtensionWeightBound r ≤ lambda r.length :=
      (properExtensionWeightBound_le_weight r).trans (weight_le_lambda_length r)
    exact (not_lt_of_ge (hεB.trans hle)) hlt
  have hcoord_lt : ∀ a : ℕ, a ∈ r → a < N := by
    intro a ha
    by_contra hnot
    have hNa : N ≤ a := le_of_not_gt hnot
    have hlt : lambda a < ε := hN a hNa
    have hle : properExtensionWeightBound r ≤ lambda a :=
      properExtensionWeightBound_le_lambda_of_mem ha
    exact (not_lt_of_ge (hεB.trans hle)) hlt
  exact controlledTree_const_mem_of_length_lt_of_forall_mem_lt r hlen_lt hcoord_lt

/-- No child node is the root. This small tree fact is used when applying the
proper-extension bound after a first exit. -/
theorem child_ne_root (s : Node) (n : ℕ) :
    child s n ≠ root := by
  intro h
  have hlen := congrArg List.length h
  simp [child, root] at hlen

/-- Every strict descendant below a non-root node has weight bounded by the
proper-extension bound of that node. -/
theorem weight_proper_extension_le_bound {p : Node} (hp : p ≠ root)
    (n : ℕ) (t : Node) :
    weight (p ++ (n :: t)) ≤ properExtensionWeightBound p := by
  calc
    weight (p ++ (n :: t)) = weight (child p n ++ t) := by
      simp [child, List.append_assoc]
    _ ≤ weight (child p n) := weight_append_le_left (child p n) t
    _ = properExtensionWeightBound p := by
      rw [weight_child_nonroot hp n]
      rfl

/-- Two first-exit pasted `d_m` sequences differ by at most `2` in any
coordinate, since all values have norm at most `‖e‖ = 1`. -/
theorem pasteAtFirstExitAux_deadSequence_sub_norm_le_two {E : Type u}
    [NormedAddCommGroup E] [LE E] {e : E} (he : UnitPositiveElement e)
    (R U : Set Node) (m : ℕ) (q r : Node) :
    ‖pasteAtFirstExitAux R e (deadSequenceRaw e m) q r -
        pasteAtFirstExitAux U e (deadSequenceRaw e m) q r‖ ≤ 2 := by
  calc
    ‖pasteAtFirstExitAux R e (deadSequenceRaw e m) q r -
        pasteAtFirstExitAux U e (deadSequenceRaw e m) q r‖ ≤
        ‖pasteAtFirstExitAux R e (deadSequenceRaw e m) q r‖ +
          ‖pasteAtFirstExitAux U e (deadSequenceRaw e m) q r‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      refine add_le_add ?_ ?_
      · simpa [he.2] using
          pasteAtFirstExitAux_norm_le (R := R) (d := deadSequenceRaw e m)
            (deadSequenceRaw_norm_le e m) q r
      · simpa [he.2] using
          pasteAtFirstExitAux_norm_le (R := U) (d := deadSequenceRaw e m)
            (deadSequenceRaw_norm_le e m) q r
    _ = 2 := by norm_num

/-- Main weighted estimate for Lemma `z-lower-continuous`: if two trees agree
on the finite control set, the coordinatewise weighted difference of their
first-exit pastes is at most `ε / 2`. -/
theorem pasteAtFirstExitAux_controlled_weighted_sub_le {E : Type u}
    [NormedAddCommGroup E] [LE E] {e : E} (he : UnitPositiveElement e)
    {ε : ℝ} (hε : 0 < ε) {T U : Tree}
    (hTU : ∀ s : Node, s ∈ lowerContinuityControlSet (ε / 4) →
      (s ∈ (T : Set Node) ↔ s ∈ (U : Set Node)))
    (m : ℕ) : ∀ q r : Node,
      weight (q ++ r) *
        ‖pasteAtFirstExitAux (T : Set Node) e (deadSequenceRaw e m) q r -
          pasteAtFirstExitAux (U : Set Node) e (deadSequenceRaw e m) q r‖ ≤ ε / 2 := by
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
              have hhalf : 0 ≤ ε / 2 := by linarith
              simpa [pasteAtFirstExitAux, hdecT, hdecU, deadSequenceRaw] using hhalf
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
                pasteAtFirstExitAux_deadSequence_sub_norm_le_two he (T : Set Node)
                  (U : Set Node) m q (n :: a :: tail)
              have hquarter_nonneg : 0 ≤ ε / 4 := by linarith
              calc
                weight (q ++ (n :: a :: tail)) *
                    ‖pasteAtFirstExitAux (T : Set Node) e (deadSequenceRaw e m) q
                        (n :: a :: tail) -
                      pasteAtFirstExitAux (U : Set Node) e (deadSequenceRaw e m) q
                        (n :: a :: tail)‖
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
              have hhalf : 0 ≤ ε / 2 := by linarith
              simpa [pasteAtFirstExitAux, hdecT, hdecU, deadSequenceRaw] using hhalf
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
                pasteAtFirstExitAux_deadSequence_sub_norm_le_two he (T : Set Node)
                  (U : Set Node) m q (n :: a :: tail)
              have hquarter_nonneg : 0 ≤ ε / 4 := by linarith
              calc
                weight (q ++ (n :: a :: tail)) *
                    ‖pasteAtFirstExitAux (T : Set Node) e (deadSequenceRaw e m) q
                        (n :: a :: tail) -
                      pasteAtFirstExitAux (U : Set Node) e (deadSequenceRaw e m) q
                        (n :: a :: tail)‖
                    ≤ (ε / 4) * 2 := by
                  exact mul_le_mul hweight hnorm (norm_nonneg _) hquarter_nonneg
                _ = ε / 2 := by ring
        · have hdecT : Classical.dec (child q n ∈ (T : Set Node)) = isFalse hT :=
            Subsingleton.elim _ _
          have hdecU : Classical.dec (child q n ∈ (U : Set Node)) = isFalse hU :=
            Subsingleton.elim _ _
          have hhalf : 0 ≤ ε / 2 := by linarith
          simpa [pasteAtFirstExitAux, hdecT, hdecU] using hhalf

/-- Lemma `z-lower-continuous`: for fixed `m`, the map `R ↦ z_m^R` is
continuous. -/
theorem z_lower_continuous_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) (m : ℕ) :
    TreeToWeightedContinuous fun R : Tree => zLower R e (m + 1) := by
  intro T ε hε
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
      weight s * ‖((zLower T e (m + 1) - zLower U e (m + 1) : V E) s)‖ ≤
        ε / 2 := by
    intro s
    change weight s * ‖zLowerRaw T e (m + 1) s - zLowerRaw U e (m + 1) s‖ ≤
      ε / 2
    simpa [zLowerRaw, root] using
      pasteAtFirstExitAux_controlled_weighted_sub_le he hε hTU (m + 1) root s
  exact lt_of_le_of_lt (weightedNorm_le_of_forall hcoords) (half_lt_self hε)

/-- The sequence-valued map `R ↦ (z_m^R)_m` is continuous. -/
theorem z_lower_sequence_continuous_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    {e : E} (he : UnitPositiveElement e) :
    TreeToSequenceContinuous fun R : Tree => zLowerSeq R e := by
  intro m
  exact z_lower_continuous_template he m

/-- The map `Theta` is continuous and takes values in positive decreasing
sequences in `X = Z_E`. -/
theorem theta_lower_template {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
    [TopologicalSpace.SeparableSpace E] {e : E} (he : UnitPositiveElement e) :
    TreeToSequenceContinuous (thetaLower e) ∧
      ∀ T : Tree,
        (∀ m : ℕ, thetaLower e T m ∈ Z E) ∧
          IsPositiveDecreasing (thetaLower e T) := by
  refine ⟨?_, ?_⟩
  · intro m T ε hε
    rcases z_lower_continuous_template he m (fatten T) ε hε with ⟨B, hB⟩
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
    simpa [thetaLower, zLowerSeq] using hB (fatten U) hfat_agree
  · intro T
    have hz := z_lower_in_X_template he (fatten T)
    refine ⟨?_, ?_⟩
    · intro m
      simpa [thetaLower] using (hz.1 m).1
    · simpa [thetaLower] using hz.2

end LowerComplete
end WeightedTree
end DSTBL3
