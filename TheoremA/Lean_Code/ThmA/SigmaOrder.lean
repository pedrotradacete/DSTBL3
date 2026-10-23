import Lean_Code.ThmA.Defs
import Lean_Code.ThmA.Prelim.AbsSmul
import Lean_Code.ThmA.Regulators

/-!
# σ-order convergence: basic calculus (paper Section 4)
-/

namespace ThmA

open Finset

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- Triangle inequality helper: `|a| ≤ |a - b| + |b|`. -/
private theorem abs_le_abs_add (a b : X) : |a| ≤ |a - b| + |b| := by
  calc |a| = |(a - b) + b| := by rw [show (a - b) + b = a from by abel]
    _ ≤ |a - b| + |b| := abs_add_le _ _

/-- **`lem:so_eventuallyEq`.** Eventually constant ⇒ σ-order converges. -/
theorem sigmaOrderTendsto_of_eventuallyEq {x : ℕ → X} {x0 : X}
    (h : ∃ n0, ∀ n ≥ n0, x n = x0) : SigmaOrderTendsto x x0 := by
  obtain ⟨n0, hn0⟩ := h
  refine ⟨0, downToZero_zero, fun m => ⟨n0, fun n hn => ?_⟩⟩
  rw [hn0 n hn]; simp

/-- **`lem:so_add`.** Additivity of σ-order convergence. -/
theorem SigmaOrderTendsto.add {x y : ℕ → X} {x0 y0 : X}
    (hx : SigmaOrderTendsto x x0) (hy : SigmaOrderTendsto y y0) :
    SigmaOrderTendsto (fun n => x n + y n) (x0 + y0) := by
  obtain ⟨z, hz, hzb⟩ := hx
  obtain ⟨w, hw, hwb⟩ := hy
  refine ⟨z + w, hz.add hw, fun m => ?_⟩
  obtain ⟨nz, hnz⟩ := hzb m
  obtain ⟨nw, hnw⟩ := hwb m
  refine ⟨max nz nw, fun n hn => ?_⟩
  have h1 : |x n - x0| ≤ z m := hnz n (le_trans (le_max_left _ _) hn)
  have h2 : |y n - y0| ≤ w m := hnw n (le_trans (le_max_right _ _) hn)
  calc |(x n + y n) - (x0 + y0)|
      = |(x n - x0) + (y n - y0)| := by rw [show (x n + y n) - (x0 + y0) = (x n - x0) + (y n - y0) from by abel]
    _ ≤ |x n - x0| + |y n - y0| := abs_add_le _ _
    _ ≤ z m + w m := add_le_add h1 h2

/-- **`lem:so_smul`.** Homogeneity of σ-order convergence. -/
theorem SigmaOrderTendsto.smul {x : ℕ → X} {x0 : X}
    (h : SigmaOrderTendsto x x0) (α : ℝ) :
    SigmaOrderTendsto (fun n => α • x n) (α • x0) := by
  obtain ⟨z, hz, hzb⟩ := h
  refine ⟨fun m => |α| • z m, hz.smul α, fun m => ?_⟩
  obtain ⟨n0, hn0⟩ := hzb m
  refine ⟨n0, fun n hn => ?_⟩
  have hb := hn0 n hn
  calc |α • x n - α • x0| = |α • (x n - x0)| := by rw [smul_sub]
    _ = |α| • |x n - x0| := abs_smul_vectorLattice α _
    _ ≤ |α| • z m := smul_le_smul_of_nonneg_left hb (abs_nonneg α)

/-- **`lem:so_bounded`.** σ-order limits are order bounded. -/
theorem SigmaOrderTendsto.orderBounded {x : ℕ → X} {x0 : X}
    (h : SigmaOrderTendsto x x0) : ∃ u : X, 0 ≤ u ∧ ∀ n, |x n| ≤ u := by
  obtain ⟨z, hz, hzb⟩ := h
  obtain ⟨n0, hn0⟩ := hzb 0
  set B : X := |x0| + z 0 with hB
  have hBnn : 0 ≤ B := add_nonneg (abs_nonneg _) (hz.1 0)
  have hxB : ∀ n, n0 ≤ n → |x n| ≤ B := by
    intro n hge
    calc |x n| ≤ |x n - x0| + |x0| := abs_le_abs_add (x n) x0
      _ ≤ z 0 + |x0| := add_le_add (hn0 n hge) (le_refl _)
      _ = B := by rw [hB, add_comm]
  rcases Nat.eq_zero_or_pos n0 with hn0z | hn0p
  · exact ⟨B, hBnn, fun n => hxB n (by omega)⟩
  · have hne : (range n0).Nonempty := nonempty_range_iff.mpr (by omega)
    refine ⟨(range n0).sup' hne (fun k => |x k|) ⊔ B, le_sup_of_le_right hBnn, fun n => ?_⟩
    rcases lt_or_ge n n0 with hlt | hge
    · exact le_sup_of_le_left (Finset.le_sup' (fun k => |x k|) (mem_range.mpr hlt))
    · exact le_sup_of_le_right (hxB n hge)

/-- **`lem:so_abs_le`.** Order bounds pass to σ-order limits. -/
theorem SigmaOrderTendsto.abs_le {x : ℕ → X} {x0 u : X}
    (h : SigmaOrderTendsto x x0) (_hu : 0 ≤ u) (hb : ∀ n, |x n| ≤ u) : |x0| ≤ u := by
  obtain ⟨z, hz, hzb⟩ := h
  have key : ∀ m, (|x0| - u)⁺ ≤ z m := by
    intro m
    obtain ⟨n0, hn0⟩ := hzb m
    have h1 : |x0| ≤ u + z m := by
      have hle := abs_le_abs_add x0 (x n0)
      rw [abs_sub_comm] at hle
      calc |x0| ≤ |x n0 - x0| + |x n0| := hle
        _ ≤ z m + u := add_le_add (hn0 n0 (le_refl n0)) (hb n0)
        _ = u + z m := by rw [add_comm]
    rw [posPart_def]
    exact sup_le (sub_le_iff_le_add.mpr (by rw [add_comm]; exact h1)) (hz.1 m)
  exact sub_nonpos.mp (posPart_eq_zero.mp (hz.2.2 _ (posPart_nonneg _) key))

/-- **`lem:norm_limit_abs_le`.** Order bounds pass to norm limits. -/
theorem abs_le_of_tendsto {x : ℕ → X} {x0 u : X}
    (h : Filter.Tendsto x Filter.atTop (nhds x0)) (hb : ∀ i, |x i| ≤ u) : |x0| ≤ u := by
  rw [abs_le']
  refine ⟨le_of_tendsto' h (fun i => (abs_le'.mp (hb i)).1),
          le_of_tendsto' h.neg (fun i => (abs_le'.mp (hb i)).2)⟩

/-- **`lem:reg_tail`.** Tails of a positive norm-summable series form a regulator:
`U_R = ∑_{r≥R} u_r ↓ 0`. -/
theorem downToZero_tsum_tail {u : ℕ → X} (hpos : ∀ r, 0 ≤ u r)
    (hsum : Summable (fun r => ‖u r‖)) : DownToZero (fun R => ∑' r, u (r + R)) := by
  have hsummable : Summable u := hsum.of_norm
  refine ⟨fun R => tsum_nonneg (fun r => hpos (r + R)), fun R => ?_, fun h hh0 hh => ?_⟩
  · -- U (R+1) ≤ U R
    have hf : Summable (fun r => u (r + R)) := (summable_nat_add_iff R).mpr hsummable
    have hrec : (∑' r, u (r + R)) = u R + ∑' r, u (r + (R + 1)) := by
      rw [hf.tsum_eq_zero_add]
      congr 1
      · rw [Nat.zero_add]
      · exact tsum_congr (fun b => by congr 1; omega)
    show (∑' r, u (r + (R + 1))) ≤ ∑' r, u (r + R)
    rw [hrec]
    exact le_add_of_nonneg_left (hpos R)
  · -- h = 0
    have hUtendsto : Filter.Tendsto (fun R => ‖∑' r, u (r + R)‖) Filter.atTop (nhds 0) := by
      simpa using (tendsto_sum_nat_add u).norm
    have hnorm_le : ∀ R, ‖h‖ ≤ ‖∑' r, u (r + R)‖ := by
      intro R
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg hh0, abs_of_nonneg (tsum_nonneg (fun r => hpos (r + R)))]
      exact hh R
    have hle0 : ‖h‖ ≤ 0 := ge_of_tendsto' hUtendsto hnorm_le
    exact norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg h))

end ThmA
