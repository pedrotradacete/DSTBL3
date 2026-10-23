import Mathlib

/-!
# Core definitions for Theorem A

This file formalizes the convergence and basis notions used in Sections 3 and 4
of the paper. `coord` and `proj` are supporting definitions for the proof.
-/

namespace ThmA

open Finset

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- **`def:downto`.** A sequence `(z m)` in the positive cone of `X` satisfies `z_m ↓ 0` if
1. `z (m + 1) ≤ z m` for every `m`, and
2. whenever `h ≥ 0` satisfies `h ≤ z m` for every `m`, then `h = 0`. -/
def DownToZero (z : ℕ → X) : Prop :=
  (∀ m, 0 ≤ z m) ∧ (∀ m, z (m + 1) ≤ z m) ∧
    ∀ h : X, 0 ≤ h → (∀ m, h ≤ z m) → h = 0

/-- **`def:sigo`.** A sequence `(x n)` in `X` *σ-order converges* to `x0 : X` if there is a
sequence `z_m ↓ 0` in the positive cone such that, for every `m`,
`|x n - x0| ≤ z m` holds for all sufficiently large `n`. -/
def SigmaOrderTendsto (x : ℕ → X) (x0 : X) : Prop :=
  ∃ z : ℕ → X, DownToZero z ∧ ∀ m : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, |x n - x0| ≤ z m

/-- **`def:basis`.** A sequence `(e n)` in `X` is a *σ-order basis* for `X` if for every
`x ∈ X` there is a unique scalar sequence `(a n)` such that the partial sums
`∑ k ∈ range (m + 1), a k • e k` σ-order converge to `x`. -/
def IsSigmaOrderBasis (e : ℕ → X) : Prop :=
  ∀ x : X, ∃! a : ℕ → ℝ,
    SigmaOrderTendsto (fun m => ∑ k ∈ range (m + 1), a k • e k) x

/-- A Schauder basis, stated in the same unique-expansion form as the paper:
every vector has a unique scalar sequence whose partial sums converge in norm. -/
def IsSchauderBasis (e : ℕ → X) : Prop :=
  ∀ x : X, ∃! a : ℕ → ℝ,
    Filter.Tendsto (fun m => ∑ k ∈ range (m + 1), a k • e k)
      Filter.atTop (nhds x)

/-- **`con:coord`.** The coordinate functional: for `x`, `coord e hbasis x` is the unique
scalar sequence `aˣ` whose partial sums σ-order converge to `x`. `coord e hbasis x k = e_k#(x)`. -/
noncomputable def coord (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) : ℕ → ℝ :=
  Classical.choose (hbasis x)

/-- **`con:coord`.** The projection `P_m x = s_m(aˣ) = ∑_{k≤m} e_k#(x) e_k`. -/
noncomputable def proj (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (m : ℕ) (x : X) : X :=
  ∑ k ∈ range (m + 1), coord e hbasis x k • e k

end ThmA
