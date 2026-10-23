import Lean_Code

/-!
# Theorem A (σ-order form) — verified

This file states the target theorem **verbatim** from `Showcase_ThmA.lean` and proves it by
applying the fully-formalized `ThmA.theoremA_sigma_order_form` from `Lean_Code`.
`Showcase_ThmA.lean` itself is left untouched (it keeps its `sorry`; it is the spec).
-/

open Finset ThmA

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- **Theorem A (σ-order form).** -/
theorem theoremA_sigma_order_form (e : ℕ → X)
    (hbasis : IsSigmaOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    ∃ C : ℝ, ∀ (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℝ),
      ‖(range N).sup' (nonempty_range_iff.mpr (by omega))
          (fun m => |∑ k ∈ range (m + 1), a k • e k|)‖
        ≤ C * ‖∑ k ∈ range N, a k • e k‖ :=
  ThmA.theoremA_sigma_order_form e hbasis hspan
