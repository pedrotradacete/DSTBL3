import Mathlib

/-!
# Scalars versus the lattice

The only genuinely new theory (Remark `rem:gap`): on a **non-linearly-ordered** vector
lattice, `|α • x| = |α| • |x|`.  Mathlib's `abs_smul` / `smul_max_of_nonneg` require a
`LinearOrder` on the module, which a Banach lattice does not have; for general lattices
Mathlib only supplies the one-sided `smul_inf_le`.  We derive the equality here.
-/

namespace ThmA

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- **Lemma `lem:smul_sup_nonneg`.** Positive scalars distribute over joins:
`α • (a ⊔ b) = (α • a) ⊔ (α • b)` for `0 ≤ α`. -/
theorem smul_sup_of_nonneg {α : ℝ} (hα : 0 ≤ α) (a b : X) :
    α • (a ⊔ b) = (α • a) ⊔ (α • b) := by
  -- one-sided inequality `(d • p) ⊔ (d • q) ≤ d • (p ⊔ q)`, valid for any `0 ≤ d`
  have onesided : ∀ (d : ℝ), 0 ≤ d → ∀ p q : X, (d • p) ⊔ (d • q) ≤ d • (p ⊔ q) := by
    intro d hd p q
    exact sup_le (smul_le_smul_of_nonneg_left le_sup_left hd)
                 (smul_le_smul_of_nonneg_left le_sup_right hd)
  refine le_antisymm ?_ (onesided α hα a b)
  rcases eq_or_lt_of_le hα with h0 | hpos
  · -- α = 0 : both sides collapse to 0
    rw [← h0]; simp
  · -- α > 0 : apply the one-sided inequality to α⁻¹ at p = α•a, q = α•b, then rescale
    have hne : α ≠ 0 := ne_of_gt hpos
    have hinv : (0 : ℝ) ≤ α⁻¹ := le_of_lt (inv_pos.mpr hpos)
    have h1 := onesided α⁻¹ hinv (α • a) (α • b)
    rw [inv_smul_smul₀ hne a, inv_smul_smul₀ hne b] at h1
    -- h1 : a ⊔ b ≤ α⁻¹ • (α • a ⊔ α • b)
    have h2 := smul_le_smul_of_nonneg_left h1 hα
    rwa [smul_inv_smul₀ hne] at h2

/-- **Lemma `lem:abs_smul`.** The absolute value is scalar-homogeneous on a vector
lattice: `|α • x| = |α| • |x|`. -/
theorem abs_smul_vectorLattice (α : ℝ) (x : X) : |α • x| = |α| • |x| := by
  -- `|a| = a ⊔ -a` holds definitionally on a lattice-ordered group
  have hsupneg : ∀ a : X, |a| = a ⊔ -a := fun _ => rfl
  -- key case: nonnegative scalars
  have key : ∀ c : ℝ, 0 ≤ c → |c • x| = c • |x| := by
    intro c hc
    rw [hsupneg (c • x), ← smul_neg, ← smul_sup_of_nonneg hc, ← hsupneg]
  rcases le_total 0 α with hα | hα
  · rw [key α hα, abs_of_nonneg hα]
  · -- α ≤ 0 : reduce to the nonnegative scalar `-α`
    have hd : 0 ≤ -α := neg_nonneg.mpr hα
    have hrw : α • x = -((-α) • x) := by rw [neg_smul, neg_neg]
    rw [hrw, abs_neg, key (-α) hd, abs_of_nonpos hα]

end ThmA
