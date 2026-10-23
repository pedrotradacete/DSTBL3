import Lean_Code.ThmA.Defs
import BanLat.Convergences.Order

/-!
# Order convergence versus σ-order convergence

This file formalizes Proposition `order-sigma` from the paper and supplies
the order-basis entry point used by Theorem A.
-/

namespace ThmA

open Filter Finset

universe u

set_option linter.unusedSectionVars false

variable {X : Type u}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- A sequence is an order basis when every vector has a unique coefficient
sequence whose partial sums order converge to it. -/
def IsOrderBasis (e : ℕ → X) : Prop :=
  ∀ x : X, ∃! a : ℕ → ℝ,
    OrderConvergesTo (fun m => ∑ k ∈ range (m + 1), a k • e k) x

/- A sequence of successive finite infima. -/
private def runningInf (d : ℕ → X) : ℕ → X
  | 0 => d 0
  | n + 1 => runningInf d n ⊓ d (n + 1)

private theorem runningInf_nonneg {d : ℕ → X} (hd : ∀ n, 0 ≤ d n) :
    ∀ n, 0 ≤ runningInf d n := by
  intro n
  induction n with
  | zero => exact hd 0
  | succ n ih => exact le_inf ih (hd (n + 1))

private theorem runningInf_succ_le (d : ℕ → X) (n : ℕ) :
    runningInf d (n + 1) ≤ runningInf d n := inf_le_left

private theorem runningInf_le (d : ℕ → X) (n : ℕ) : runningInf d n ≤ d n := by
  cases n with
  | zero => rfl
  | succ n => exact inf_le_right

omit [HasSolidNorm X] [IsOrderedAddMonoid X] [NormedSpace ℝ X] [PosSMulMono ℝ X]
    [CompleteSpace X] in
/-- Every σ-order convergent sequence is order convergent. -/
theorem SigmaOrderTendsto.orderConvergesTo {x : ℕ → X} {x0 : X}
    (h : SigmaOrderTendsto x x0) : OrderConvergesTo x x0 := by
  rcases h with ⟨z, hz, hbound⟩
  refine ⟨ULift.{u} ℕ, inferInstance, inferInstance, inferInstance, fun k => z k.down,
    ?_, fun k => hz.1 k.down, ?_, ?_⟩
  · intro k l hkl
    exact antitone_nat_of_succ_le hz.2.1 hkl
  · refine ⟨fun _ ⟨k, hk⟩ => hk ▸ hz.1 k.down, ?_⟩
    intro w hw
    have hpos : w⁺ = 0 := hz.2.2 w⁺ (posPart_nonneg w) fun m => by
      rw [posPart_def]
      exact sup_le (hw ⟨ULift.up m, rfl⟩) (hz.1 m)
    exact posPart_eq_zero.mp hpos
  · intro k
    rcases hbound k.down with ⟨n0, hn0⟩
    exact eventually_atTop.2 ⟨n0, hn0⟩

/-- In a separable Banach lattice, order convergence of sequences is
σ-order convergence. This is Proposition `order-sigma` in the paper. -/
theorem OrderConvergesTo.sigmaOrderTendsto [TopologicalSpace.SeparableSpace X]
    {x : ℕ → X} {x0 : X} (h : OrderConvergesTo x x0) :
    SigmaOrderTendsto x x0 := by
  rcases h with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnonneg, hrglb, hrevent⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκnon
  let S : Type u := Set.range r
  let : Nonempty S := by
    let k : κ := Classical.choice hκnon
    exact ⟨⟨r k, ⟨k, rfl⟩⟩⟩
  let d : ℕ → S := TopologicalSpace.denseSeq S
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq S
  let dX : ℕ → X := fun n => (d n : X)
  let z : ℕ → X := runningInf dX
  have hdnonneg : ∀ n, 0 ≤ dX n := by
    intro n
    rcases (d n).property with ⟨k, hk⟩
    simpa [dX, hk] using hrnonneg k
  have hzbound : ∀ m, ∀ᶠ n in atTop, |x n - x0| ≤ z m := by
    intro m
    induction m with
    | zero =>
        rcases (d 0).property with ⟨k, hk⟩
        simpa [z, runningInf, dX, hk] using hrevent k
    | succ m ih =>
        rcases (d (m + 1)).property with ⟨k, hk⟩
        exact (ih.and (hrevent k)).mono fun n hn => by
          change |x n - x0| ≤ runningInf dX m ⊓ dX (m + 1)
          exact le_inf hn.1 (by simpa [dX, hk] using hn.2)
  refine ⟨z, ⟨runningInf_nonneg hdnonneg, runningInf_succ_le dX, ?_⟩, ?_⟩
  · intro y hy0 hy
    have hydense : ∀ n, y ≤ (d n : X) := fun n =>
      (hy n).trans (runningInf_le dX n)
    have hyS : ∀ q : S, y ≤ (q : X) := by
      intro q
      exact isClosed_property hdense
        (isClosed_le continuous_const continuous_subtype_val) hydense q
    have hylower : y ∈ lowerBounds (Set.range r) := by
      rintro _ ⟨k, rfl⟩
      exact hyS ⟨r k, ⟨k, rfl⟩⟩
    exact le_antisymm (hrglb.2 hylower) hy0
  · intro m
    rcases eventually_atTop.1 (hzbound m) with ⟨n0, hn0⟩
    exact ⟨n0, hn0⟩

/-- In a separable Banach lattice, order and σ-order convergence agree for
sequences. -/
theorem orderConvergesTo_iff_sigmaOrderTendsto [TopologicalSpace.SeparableSpace X]
    {x : ℕ → X} {x0 : X} :
    OrderConvergesTo x x0 ↔ SigmaOrderTendsto x x0 :=
  ⟨OrderConvergesTo.sigmaOrderTendsto, SigmaOrderTendsto.orderConvergesTo⟩

/-- On a separable Banach lattice, order bases and σ-order bases coincide. -/
theorem isOrderBasis_iff_isSigmaOrderBasis [TopologicalSpace.SeparableSpace X]
    {e : ℕ → X} : IsOrderBasis e ↔ IsSigmaOrderBasis e := by
  constructor
  · intro hbasis x
    rcases hbasis x with ⟨a, ha, huniq⟩
    refine ⟨a, OrderConvergesTo.sigmaOrderTendsto ha, ?_⟩
    intro b hb
    exact huniq b hb.orderConvergesTo
  · intro hbasis x
    rcases hbasis x with ⟨a, ha, huniq⟩
    refine ⟨a, ha.orderConvergesTo, ?_⟩
    intro b hb
    exact huniq b (OrderConvergesTo.sigmaOrderTendsto hb)

/-- The dense-span hypothesis in Theorem A makes the ambient Banach lattice
separable, so an order basis is a σ-order basis. -/
theorem IsOrderBasis.isSigmaOrderBasis_of_denseSpan {e : ℕ → X}
    (hbasis : IsOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    IsSigmaOrderBasis e := by
  have hdense : Dense (Submodule.span ℝ (Set.range e) : Set X) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hspan
  have hseparable : TopologicalSpace.IsSeparable
      (Submodule.span ℝ (Set.range e) : Set X) :=
    (Set.countable_range e).isSeparable.span
  let : TopologicalSpace.SeparableSpace X := hdense.isSeparable_iff.mp hseparable
  exact isOrderBasis_iff_isSigmaOrderBasis.mp hbasis

end ThmA
