import Lean_Code.ThmA.SigmaOrder

/-!
# Coordinates and projections (paper Section 4)
-/

namespace ThmA

open Finset

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- **`lem:proj_sotends`.** For every `x`, `P_m x ⟶σo x`. -/
theorem proj_sigmaOrderTendsto (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    SigmaOrderTendsto (fun m => proj e hbasis m x) x :=
  (Classical.choose_spec (hbasis x)).1

/-- **`lem:coord_unique`.** If `s_m(a) ⟶σo x` then `a = aˣ`. -/
theorem coord_unique (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) {a : ℕ → ℝ} {x : X}
    (h : SigmaOrderTendsto (fun m => ∑ k ∈ range (m + 1), a k • e k) x) :
    a = coord e hbasis x :=
  (Classical.choose_spec (hbasis x)).2 a h

/-- **`lem:coord_add`.** Coordinates are additive. -/
theorem coord_add (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x y : X) (k : ℕ) :
    coord e hbasis (x + y) k = coord e hbasis x k + coord e hbasis y k := by
  have hsum : SigmaOrderTendsto
      (fun m => ∑ k ∈ range (m + 1), (coord e hbasis x + coord e hbasis y) k • e k) (x + y) := by
    have h := (proj_sigmaOrderTendsto e hbasis x).add (proj_sigmaOrderTendsto e hbasis y)
    have heq : (fun m => ∑ k ∈ range (m + 1), (coord e hbasis x + coord e hbasis y) k • e k)
             = (fun m => proj e hbasis m x + proj e hbasis m y) := by
      funext m
      simp only [Pi.add_apply, add_smul, proj, Finset.sum_add_distrib]
    rw [heq]; exact h
  have huniq := coord_unique e hbasis hsum
  have := congrFun huniq k
  simpa [Pi.add_apply] using this.symm

/-- **`lem:coord_smul`.** Coordinates are homogeneous. -/
theorem coord_smul (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (α : ℝ) (x : X) (k : ℕ) :
    coord e hbasis (α • x) k = α * coord e hbasis x k := by
  have hsum : SigmaOrderTendsto
      (fun m => ∑ k ∈ range (m + 1), (α • coord e hbasis x) k • e k) (α • x) := by
    have h := (proj_sigmaOrderTendsto e hbasis x).smul α
    have heq : (fun m => ∑ k ∈ range (m + 1), (α • coord e hbasis x) k • e k)
             = (fun m => α • proj e hbasis m x) := by
      funext m
      simp only [Pi.smul_apply, smul_eq_mul, proj, Finset.smul_sum, mul_smul]
    rw [heq]; exact h
  have huniq := coord_unique e hbasis hsum
  have := congrFun huniq k
  simpa [Pi.smul_apply, smul_eq_mul] using this.symm

/-- **`lem:proj_linear` (additivity).** -/
theorem proj_add (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (m : ℕ) (x y : X) :
    proj e hbasis m (x + y) = proj e hbasis m x + proj e hbasis m y := by
  simp only [proj]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [coord_add, add_smul]

/-- **`lem:proj_linear` (homogeneity).** -/
theorem proj_smul (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (m : ℕ) (α : ℝ) (x : X) :
    proj e hbasis m (α • x) = α • proj e hbasis m x := by
  simp only [proj]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [coord_smul, mul_smul]

/-- `coord` of `0` is the zero sequence. -/
theorem coord_zero (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) : coord e hbasis (0 : X) = 0 := by
  have h : SigmaOrderTendsto (fun m => ∑ k ∈ range (m + 1), (0 : ℕ → ℝ) k • e k) (0 : X) :=
    sigmaOrderTendsto_of_eventuallyEq ⟨0, fun n _ => by simp⟩
  exact (coord_unique e hbasis h).symm

/-- `proj` of `0` is `0`. -/
theorem proj_zero (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (m : ℕ) :
    proj e hbasis m (0 : X) = 0 := by
  simp [proj, coord_zero]

/-- **`lem:e_indep`.** The basis vectors `(e_n)` are linearly independent. -/
theorem e_linearIndependent (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    LinearIndependent ℝ e := by
  rw [linearIndependent_iff']
  intro s g hg
  obtain ⟨N, hsN⟩ : ∃ N, ∀ j ∈ s, j < N :=
    ⟨s.sup id + 1, fun j hj => Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)⟩
  have hsub : s ⊆ range N := fun j hj => mem_range.mpr (hsN j hj)
  set ĝ : ℕ → ℝ := fun k => if k ∈ s then g k else 0 with hĝ
  have hĝs : ∀ k ∈ s, ĝ k = g k := fun k hk => by simp [hĝ, hk]
  have hĝns : ∀ k, k ∉ s → ĝ k = 0 := fun k hk => by simp [hĝ, hk]
  have hsum0 : ∑ k ∈ range N, ĝ k • e k = 0 := by
    rw [← Finset.sum_subset hsub (fun k _ hknot => by rw [hĝns k hknot, zero_smul])]
    rw [← hg]
    exact Finset.sum_congr rfl (fun k hk => by rw [hĝs k hk])
  have hĝ0 : ĝ = coord e hbasis (0 : X) := by
    apply coord_unique e hbasis
    apply sigmaOrderTendsto_of_eventuallyEq
    refine ⟨N, fun M hM => ?_⟩
    show (∑ k ∈ range (M + 1), ĝ k • e k) = 0
    rw [← hsum0]
    refine (Finset.sum_subset
      (fun k hk => mem_range.mpr (lt_of_lt_of_le (mem_range.mp hk) (by omega))) ?_).symm
    intro k _ hknot
    rw [hĝns k (fun hks => hknot (mem_range.mpr (hsN k hks))), zero_smul]
  intro i hi
  have hi0 : ĝ i = 0 := by rw [hĝ0, coord_zero]; rfl
  rw [← hĝs i hi]; exact hi0

end ThmA
