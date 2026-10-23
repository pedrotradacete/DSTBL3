import ThmBC.Upper.Continuity

/-!
# The upper construction — well-founded-tree reduction

This file proves the ill-founded and well-founded directions of the reduction and
establishes the closedness and separability properties of the target lattice `Y`.
-/

open Filter
open scoped BigOperators Topology

namespace DSTBL3
namespace WeightedTree

open DSTBL3.WeightedTree
open LowerComplete

namespace UpperComplete

/-- Paper Proposition `upper-IF`: if `T` is ill-founded, an infinite branch
produces the explicit upper bound `y^b`, so `Φ(T)` is order bounded and hence
does not belong to `Y^{\uparrow\infty}`. -/
theorem upper_IF_template {T : Tree} :
    ¬ WellFoundedTree (T : Set Node) → ¬ YUpwardUnbounded (phiUpper T) := by
  intro hIF hupper
  have hbranch : ∃ b : ℕ → ℕ, IsBranch (T : Set Node) b := by
    by_contra hbranch
    exact hIF hbranch
  rcases hbranch with ⟨b, hb⟩
  exact hupper.2.2 ⟨branchConeComplementIndicator b,
    branchConeComplement_upper_bound_template hb⟩

/-- If `y` is an order upper bound for all `u_m^R`, then immediately below a
first exit from `R` the coordinate of `y` is at least `1`. -/
theorem upperBound_ge_one_at_first_exit {R : Tree} {y : V ℝ}
    (hyZ : y ∈ Z ℝ) (hupper : ∀ m : ℕ, CoordinatewiseLE (uUpperSeq R m) y)
    {q : Node} {n : ℕ} (hq : q ∈ (R : Set Node))
    (hexit : child q n ∉ (R : Set Node)) :
    (1 : ℝ) ≤ y (child q n) := by
  by_contra hnot
  have hlt : y (child q n) < (1 : ℝ) := lt_of_not_ge hnot
  have hpos : 0 < ((1 : ℝ) - y (child q n)) / 2 := by linarith
  have htend := child_convergence_template hyZ (child q n)
  rw [Metric.tendsto_atTop] at htend
  rcases htend (((1 : ℝ) - y (child q n)) / 2) hpos with ⟨K, hK⟩
  have hnear : dist (y (child (child q n) K)) (y (child q n)) <
      ((1 : ℝ) - y (child q n)) / 2 := hK K (le_refl K)
  have hchild_lt : y (child (child q n) K) < (1 : ℝ) := by
    have habs : |y (child (child q n) K) - y (child q n)| <
        ((1 : ℝ) - y (child q n)) / 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using hnear
    have hdiff_lt := (abs_lt.mp habs).2
    linarith
  have hupperK : (1 : ℝ) ≤ y (child (child q n) K) := by
    have hcoord := hupper K (child (child q n) K)
    have hvalue : uUpperSeq R K (child (child q n) K) = (1 : ℝ) := by
      change uUpperRaw R K (child (child q n) K) = (1 : ℝ)
      have hfirst :=
        pasteAtFirstExitAux_eq_of_first_exit R (0 : ℝ) (upperSequenceRaw K)
          root q n [K] (by simpa [root] using hq) (by simpa [root] using hexit)
      simpa [uUpperRaw, child, root, upperSequenceRaw] using hfirst
    simpa [hvalue] using hcoord
  linarith

/-- A node of `R` where an upper bound is still below `1` has a child in `R`
with the same defect. Otherwise the first-exit estimate would contradict
child convergence. -/
theorem upperBound_exists_bad_child {R : Tree} {y : V ℝ}
    (hyZ : y ∈ Z ℝ) (hupper : ∀ m : ℕ, CoordinatewiseLE (uUpperSeq R m) y)
    {s : Node} (hsR : s ∈ (R : Set Node)) (hslt : y s < (1 : ℝ)) :
    ∃ n : ℕ, child s n ∈ (R : Set Node) ∧ y (child s n) < (1 : ℝ) := by
  have hpos : 0 < ((1 : ℝ) - y s) / 2 := by linarith
  have htend := child_convergence_template hyZ s
  rw [Metric.tendsto_atTop] at htend
  rcases htend (((1 : ℝ) - y s) / 2) hpos with ⟨N, hN⟩
  have hnear : dist (y (child s N)) (y s) < ((1 : ℝ) - y s) / 2 :=
    hN N (le_refl N)
  have hchild_lt : y (child s N) < (1 : ℝ) := by
    have habs : |y (child s N) - y s| < ((1 : ℝ) - y s) / 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using hnear
    have hdiff_lt := (abs_lt.mp habs).2
    linarith
  have hchildR : child s N ∈ (R : Set Node) := by
    by_contra hnot
    have hge := upperBound_ge_one_at_first_exit hyZ hupper hsR hnot
    linarith
  exact ⟨N, hchildR, hchild_lt⟩

/-- Paper Proposition `upper-WF`: if `T` is well-founded, then any putative
upper bound for `Φ(T)` would, by well-founded induction through
`\widehat T`, have all coordinates on the tree at least `1`, contradicting
the defining condition `y_root = 0` for elements of `Y`. -/
theorem upper_WF_template {T : Tree} :
    WellFoundedTree (T : Set Node) → YUpwardUnbounded (phiUpper T) := by
  intro hWF
  have hphi := phi_upper_increasing_template T
  refine ⟨hphi.1, hphi.2, ?_⟩
  rintro ⟨y, hyub⟩
  rcases hyub with ⟨hyY, hupperPhi⟩
  rcases hyY with ⟨hyZ, hyroot⟩
  let R : Tree := fatten T
  have hRWF : WellFoundedTree (R : Set Node) := by
    dsimp [R]
    exact (fattening_template.2.1 T).1 hWF
  have hupperR : ∀ m : ℕ, CoordinatewiseLE (uUpperSeq R m) y := by
    intro m s
    dsimp [R]
    simpa [phiUpper] using hupperPhi m s
  let Bad : Type := {s : Node // s ∈ (R : Set Node) ∧ y s < (1 : ℝ)}
  have hroot_bad : root ∈ (R : Set Node) ∧ y root < (1 : ℝ) := by
    refine ⟨R.2.1, ?_⟩
    linarith
  let childIndex : Bad → ℕ := fun s =>
    Classical.choose (upperBound_exists_bad_child hyZ hupperR s.2.1 s.2.2)
  let nextNode : Bad → Bad := fun s =>
    let hchild := Classical.choose_spec
      (upperBound_exists_bad_child hyZ hupperR s.2.1 s.2.2)
    ⟨child s.1 (childIndex s), hchild⟩
  let zseq : ℕ → Bad := fun k =>
    Nat.rec ⟨root, hroot_bad⟩ (fun _ s => nextNode s) k
  let a : ℕ → ℕ := fun k => childIndex (zseq k)
  have hzseq_succ : ∀ k : ℕ, (zseq (k + 1)).1 = child (zseq k).1 (a k) := by
    intro k
    rfl
  have hzseq_path : ∀ k : ℕ, (zseq k).1 = initialSegment a k := by
    intro k
    induction k with
    | zero =>
        simp [zseq, initialSegment, root]
    | succ k ih =>
        rw [hzseq_succ k, ih, initialSegment_succ]
  have hpath : ∀ k : ℕ, initialSegment a k ∈ (R : Set Node) := by
    intro k
    simpa [← hzseq_path k] using (zseq k).2.1
  exact hRWF ⟨a, hpath⟩

/-- The equivalence used in the proof of Theorem `upper-complete`: the
continuous reduction `Φ` sends well-founded trees exactly to
`Y^{\uparrow\infty}`. -/
theorem upper_reduction_template (T : Tree) :
    WellFoundedTree (T : Set Node) ↔ YUpwardUnbounded (phiUpper T) := by
  constructor
  · exact upper_WF_template
  · intro hupper
    by_contra hWF
    exact upper_IF_template hWF hupper

/-- The constant raw sequence, used to project elements of `Z_ℝ` onto the
root-zero slice defining `Y`. -/
noncomputable def constantRaw (a : ℝ) : TreeSeq ℝ :=
  fun _ => a

/-- Constant raw sequences are weighted bounded. -/
theorem constantRaw_weightedBounded (a : ℝ) :
    WeightedBounded (constantRaw a) := by
  refine ⟨‖a‖, ?_⟩
  intro s
  change weight s * ‖a‖ ≤ ‖a‖
  simpa using mul_le_mul_of_nonneg_right (weight_le_one s) (norm_nonneg a)

/-- The constant element of the ambient weighted space. -/
noncomputable def constantElement (a : ℝ) : V ℝ :=
  ⟨constantRaw a, constantRaw_weightedBounded a⟩

/-- Constant elements are finite-rank, witnessed by the singleton root tree. -/
theorem constantElement_finiteRank (a : ℝ) :
    FiniteRank (constantElement a) := by
  refine ⟨{root}, isFiniteDownwardClosedTree_singleton_root, ?_⟩
  intro s n hs hchild t
  rfl

/-- Constant elements belong to `Z_ℝ`. -/
theorem constantElement_mem_Z (a : ℝ) :
    constantElement a ∈ Z ℝ :=
  finiteRank_mem_Z (constantElement_finiteRank a)

/-- The weighted norm of a constant element is bounded by the absolute value
of its constant. -/
theorem constantElement_norm_le (a : ℝ) :
    ‖constantElement a‖ ≤ ‖a‖ := by
  apply weightedNorm_le_of_forall
  intro s
  change weight s * ‖a‖ ≤ ‖a‖
  simpa using mul_le_mul_of_nonneg_right (weight_le_one s) (norm_nonneg a)

/-- Projection onto the root-zero affine hyperplane by subtracting the
constant root value. -/
noncomputable def zeroRootProjection (x : V ℝ) : V ℝ :=
  x - constantElement (x root)

/-- Projecting an element of `Z_ℝ` by subtracting its constant root value
lands in `Y`. -/
theorem zeroRootProjection_mem_Y {x : V ℝ} (hxZ : x ∈ Z ℝ) :
    zeroRootProjection x ∈ Y := by
  rcases (Z_isVectorSubLattice (E := ℝ)) with ⟨_hzero, hadd, hneg, _hsmul, _hsup, _hinf⟩
  refine ⟨?_, ?_⟩
  · have hconstZ : constantElement (x root) ∈ Z ℝ := constantElement_mem_Z (x root)
    have hsubZ : x + -constantElement (x root) ∈ Z ℝ :=
      hadd x hxZ (-constantElement (x root)) (hneg (constantElement (x root)) hconstZ)
    have hsub_eq : x - constantElement (x root) = x + -constantElement (x root) := by
      apply Subtype.ext
      funext s
      rfl
    rw [zeroRootProjection, hsub_eq]
    exact hsubZ
  · change x root - constantElement (x root) root = 0
    simp [constantElement, constantRaw]

/-- The projection changes an element by at most the norm of its root value. -/
theorem weightedNorm_sub_zeroRootProjection_le (x : V ℝ) :
    ‖x - zeroRootProjection x‖ ≤ ‖x root‖ := by
  apply weightedNorm_le_of_forall
  intro s
  change weight s * ‖x s - (x s - constantElement (x root) s)‖ ≤ ‖x root‖
  have hcoord : x s - (x s - constantElement (x root) s) = x root := by
    simp [constantElement, constantRaw]
  rw [hcoord]
  simpa using mul_le_mul_of_nonneg_right (weight_le_one s) (norm_nonneg (x root))

/-- Formalizes the opening paragraph of Section 7: because root evaluation is
a continuous lattice homomorphism, `Y = {y ∈ Z_ℝ | y_root = 0}` is a closed
Banach sublattice of `Z_ℝ`, and it remains separable. -/
theorem Y_closed_separable_template :
    IsClosedBanachSubLattice Y ∧ IsSeparableForWeightedNorm Y := by
  have hZlat := Z_isVectorSubLattice (E := ℝ)
  rcases hZlat with ⟨hZzero, hZadd, hZneg, hZsmul, hZsup, hZinf⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨hZzero, ?_⟩
        change (0 : ℝ) = 0
        rfl
      · intro x hx y hy
        refine ⟨hZadd x hx.1 y hy.1, ?_⟩
        change x root + y root = 0
        rw [hx.2, hy.2]
        ring
      · intro x hx
        refine ⟨hZneg x hx.1, ?_⟩
        change -x root = 0
        rw [hx.2]
        ring
      · intro a x hx
        refine ⟨hZsmul a x hx.1, ?_⟩
        change a • x root = 0
        rw [hx.2]
        simp
      · intro x hx y hy
        refine ⟨hZsup x hx.1 y hy.1, ?_⟩
        change x root ⊔ y root = 0
        simp [hx.2, hy.2]
      · intro x hx y hy
        refine ⟨hZinf x hx.1 y hy.1, ?_⟩
        change x root ⊓ y root = 0
        simp [hx.2, hy.2]
    · intro x hx
      have hxZ : x ∈ Z ℝ := by
        apply Z_isClosedForWeightedNorm
        intro ε hε
        rcases hx ε hε with ⟨y, hyY, hxy⟩
        exact ⟨y, hyY.1, hxy⟩
      have hxroot : x root = 0 := by
        by_contra hroot
        have hnorm_pos : 0 < ‖x root‖ := norm_pos_iff.mpr hroot
        have hhalf : 0 < ‖x root‖ / 2 := half_pos hnorm_pos
        rcases hx (‖x root‖ / 2) hhalf with ⟨y, hyY, hxy⟩
        have hcoord : ‖x root‖ ≤ ‖x - y‖ := by
          have h := weighted_coordinate_le_norm (x - y) root
          change weight root * ‖x root - y root‖ ≤ ‖x - y‖ at h
          simpa [weight_root, hyY.2] using h
        linarith
      exact ⟨hxZ, hxroot⟩
    · intro u huY huC
      have huZ : ∀ n : ℕ, u n ∈ Z ℝ := fun n => (huY n).1
      rcases Z_isCompleteForWeightedNorm (E := ℝ) u huZ huC with ⟨x, hxZ, hux⟩
      refine ⟨x, ?_, hux⟩
      refine ⟨hxZ, ?_⟩
      by_contra hroot
      have hnorm_pos : 0 < ‖x root‖ := norm_pos_iff.mpr hroot
      have hhalf : 0 < ‖x root‖ / 2 := half_pos hnorm_pos
      rcases hux (‖x root‖ / 2) hhalf with ⟨N, hN⟩
      have hdist : ‖u N - x‖ < ‖x root‖ / 2 := hN N (le_refl N)
      have hcoord : ‖x root‖ ≤ ‖u N - x‖ := by
        have h := weighted_coordinate_le_norm (u N - x) root
        change weight root * ‖u N root - x root‖ ≤ ‖u N - x‖ at h
        have huNroot : u N root = 0 := (huY N).2
        simpa [weight_root, huNroot, norm_neg] using h
      linarith
  · rcases Z_isSeparableForWeightedNorm (E := ℝ) with ⟨DZ, hDZcount, hDZsub, hDZDense⟩
    let D : Set (V ℝ) := zeroRootProjection '' DZ
    refine ⟨D, ?_, ?_, ?_⟩
    · exact hDZcount.image zeroRootProjection
    · rintro z ⟨y, hyD, rfl⟩
      exact zeroRootProjection_mem_Y (hDZsub hyD)
    · intro x hxY ε hε
      have hhalf : 0 < ε / 2 := half_pos hε
      rcases hDZDense x hxY.1 (ε / 2) hhalf with ⟨y, hyD, hxy⟩
      refine ⟨zeroRootProjection y, ⟨y, hyD, rfl⟩, ?_⟩
      have hproj_root : ‖y - zeroRootProjection y‖ ≤ ‖y root‖ :=
        weightedNorm_sub_zeroRootProjection_le y
      have hyroot_le : ‖y root‖ ≤ ‖x - y‖ := by
        have h := weighted_coordinate_le_norm (x - y) root
        change weight root * ‖x root - y root‖ ≤ ‖x - y‖ at h
        simpa [weight_root, hxY.2, norm_neg] using h
      have hproj : ‖y - zeroRootProjection y‖ ≤ ‖x - y‖ :=
        hproj_root.trans hyroot_le
      have hdist := weightedNorm_sub_le x y (zeroRootProjection y)
      have hsum : ‖x - y‖ + ‖y - zeroRootProjection y‖ < ε := by
        linarith
      exact lt_of_le_of_lt hdist hsum

end UpperComplete
end WeightedTree
end DSTBL3
