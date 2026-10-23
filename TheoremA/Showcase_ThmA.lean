import Mathlib
open Finset

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- A sequence `(z m)` in the positive cone of `X` satisfies `z_m ↓ 0` if
1. `z (m + 1) ≤ z m` for every `m`, and
2. whenever `h ≥ 0` satisfies `h ≤ z m` for every `m`, then `h = 0`. -/

def DownToZero (z : ℕ → X) : Prop :=
  (∀ m, 0 ≤ z m) ∧ (∀ m, z (m + 1) ≤ z m) ∧
    ∀ h : X, 0 ≤ h → (∀ m, h ≤ z m) → h = 0

/-- A sequence `(x n)` in `X` *σ-order converges* to `x0 : X` if there is a
sequence `z_m ↓ 0` in the positive cone such that, for every `m`,
`|x n - x0| ≤ z m` holds for all sufficiently large `n`. -/

def SigmaOrderTendsto (x : ℕ → X) (x0 : X) : Prop :=
  ∃ z : ℕ → X, DownToZero z ∧ ∀ m : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, |x n - x0| ≤ z m

/-- A sequence `(e n)` in `X` is a *σ-order basis* for `X` if for every
`x ∈ X` there is a unique scalar sequence `(a n)` such that the partial sums
`∑ k ∈ range (m + 1), a k • e k` σ-order converge to `x`. -/

def IsSigmaOrderBasis (e : ℕ → X) : Prop :=
  ∀ x : X, ∃! a : ℕ → ℝ,
    SigmaOrderTendsto (fun m => ∑ k ∈ range (m + 1), a k • e k) x

/-- **Theorem A (σ-order form).** -/

theorem theoremA_sigma_order_form (e : ℕ → X)
    (hbasis : IsSigmaOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    ∃ C : ℝ, ∀ (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℝ),
      ‖(range N).sup' (nonempty_range_iff.mpr (by omega))
          (fun m => |∑ k ∈ range (m + 1), a k • e k|)‖
        ≤ C * ‖∑ k ∈ range N, a k • e k‖ := by
  sorry
