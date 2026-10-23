import Lean_Code.ThmA.Defs

/-!
# The calculus of regulators `z ↓ 0` (paper Section 4)
-/

namespace ThmA

open Finset

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- **`lem:reg_zero`.** The constant sequence `0` satisfies `0 ↓ 0`. -/
theorem downToZero_zero : DownToZero (0 : ℕ → X) := by
  refine ⟨fun m => ?_, fun m => ?_, fun h hh0 hh => ?_⟩
  · simp
  · simp
  · exact le_antisymm (hh 0) hh0

/-- **`lem:reg_add`.** Regulators are closed under addition. -/
theorem DownToZero.add {z w : ℕ → X} (hz : DownToZero z) (hw : DownToZero w) :
    DownToZero (z + w) := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hw0, hw1, hw2⟩ := hw
  have hz_anti : Antitone z := antitone_nat_of_succ_le hz1
  have hw_anti : Antitone w := antitone_nat_of_succ_le hw1
  refine ⟨fun m => add_nonneg (hz0 m) (hw0 m), fun m => add_le_add (hz1 m) (hw1 m),
    fun h hh0 hh => ?_⟩
  -- (iii): conclude h = 0 by showing h ≤ z M for every M.
  apply hz2 h hh0
  intro M
  have hposbound : ∀ m, M ≤ m → (h - z M)⁺ ≤ w m := by
    intro m hMm
    have hhm : h ≤ z m + w m := hh m
    have hmono : z m + w m ≤ z M + w m := by gcongr; exact hz_anti hMm
    have hsub : h - z M ≤ w m :=
      sub_le_iff_le_add.mpr (by rw [add_comm]; exact le_trans hhm hmono)
    rw [posPart_def]; exact sup_le hsub (hw0 m)
  have key : ∀ m, (h - z M)⁺ ≤ w m := by
    intro m
    rcases le_or_gt M m with hMm | hmM
    · exact hposbound m hMm
    · exact le_trans (hposbound M (le_refl M)) (hw_anti (le_of_lt hmM))
  exact sub_nonpos.mp (posPart_eq_zero.mp (hw2 _ (posPart_nonneg _) key))

/-- **`lem:reg_smul`.** Regulators are closed under scaling: `(|α| • z_m)_m ↓ 0`. -/
theorem DownToZero.smul {z : ℕ → X} (hz : DownToZero z) (α : ℝ) :
    DownToZero (fun m => |α| • z m) := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  have habs : 0 ≤ |α| := abs_nonneg α
  refine ⟨fun m => smul_nonneg habs (hz0 m),
    fun m => smul_le_smul_of_nonneg_left (hz1 m) habs, fun h hh0 hh => ?_⟩
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    refine le_antisymm ?_ hh0
    have := hh 0; simpa using this
  · have hpos : 0 < |α| := abs_pos.mpr hα
    have hne : |α| ≠ 0 := ne_of_gt hpos
    have hinv : 0 ≤ |α|⁻¹ := le_of_lt (inv_pos.mpr hpos)
    have key : ∀ m, |α|⁻¹ • h ≤ z m := by
      intro m
      have := smul_le_smul_of_nonneg_left (hh m) hinv
      rwa [inv_smul_smul₀ hne] at this
    have hzero : |α|⁻¹ • h = 0 := hz2 _ (smul_nonneg hinv hh0) key
    have h2 : |α| • (|α|⁻¹ • h) = |α| • (0 : X) := by rw [hzero]
    rwa [smul_smul, mul_inv_cancel₀ hne, one_smul, smul_zero] at h2

/-- **`lem:diagonal`.** Diagonal regulator: if `c ↓ 0`, each `w^R ↓ 0`, and for all `R, j`
eventually `|y_m - x| ≤ c_R + w^R_j`, then `y_m ⟶σo x`. -/
theorem sigmaOrderTendsto_of_diagonal {y : ℕ → X} {x : X} {c : ℕ → X} {w : ℕ → ℕ → X}
    (hc : DownToZero c) (hw : ∀ R, DownToZero (w R))
    (hbound : ∀ R j, ∃ m0, ∀ m ≥ m0, |y m - x| ≤ c R + w R j) :
    SigmaOrderTendsto y x := by
  refine ⟨fun j => (range (j + 1)).inf' (nonempty_range_iff.mpr (Nat.succ_ne_zero j))
      (fun R => c R + w R j), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- 0 ≤ b j
    intro j
    apply Finset.le_inf'
    intro R _
    exact add_nonneg (hc.1 R) ((hw R).1 j)
  · -- b (j+1) ≤ b j
    intro j
    apply Finset.le_inf'
    intro R hR
    have hR2 : R ∈ range (j + 2) := mem_range.mpr (by have := mem_range.mp hR; omega)
    calc (range (j + 2)).inf' _ (fun R => c R + w R (j + 1))
          ≤ c R + w R (j + 1) := Finset.inf'_le _ hR2
        _ ≤ c R + w R j := by gcongr; exact (hw R).2.1 j
  · -- b ↓ 0
    intro h hh0 hh
    apply hc.2.2 h hh0
    intro R
    have hwR := hw R
    have hwR_anti : Antitone (w R) := antitone_nat_of_succ_le hwR.2.1
    have hposbound : ∀ j, R ≤ j → (h - c R)⁺ ≤ w R j := by
      intro j hRj
      have hbj : h ≤ c R + w R j :=
        le_trans (hh j) (Finset.inf'_le _ (mem_range.mpr (by omega)))
      have hsub : h - c R ≤ w R j := sub_le_iff_le_add.mpr (by rw [add_comm]; exact hbj)
      rw [posPart_def]; exact sup_le hsub (hwR.1 j)
    have key : ∀ j, (h - c R)⁺ ≤ w R j := by
      intro j
      rcases le_or_gt R j with hRj | hjR
      · exact hposbound j hRj
      · exact le_trans (hposbound R (le_refl R)) (hwR_anti (le_of_lt hjR))
    exact sub_nonpos.mp (posPart_eq_zero.mp (hwR.2.2 _ (posPart_nonneg _) key))
  · -- the eventual bound |y n - x| ≤ b j
    intro j
    refine ⟨(range (j + 1)).sup (fun R => (hbound R j).choose), fun n hn => ?_⟩
    apply Finset.le_inf'
    intro R hR
    have hm0 : (hbound R j).choose ≤ n :=
      le_trans (Finset.le_sup (f := fun R => (hbound R j).choose) hR) hn
    exact (hbound R j).choose_spec n hm0

end ThmA
