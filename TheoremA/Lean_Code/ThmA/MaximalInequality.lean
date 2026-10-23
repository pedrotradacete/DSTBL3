import Lean_Code.ThmA.Complete
import Lean_Code.ThmA.OrderSigma

/-!
# The maximal inequality and Schauder conclusion — Theorem A (paper Section 4)

`proj_of_finite`, `rho_eq_norm_sup`, and `exists_const_rho_le` lead to the
maximal inequality; the final results also prove norm convergence and uniqueness
of the expansion, hence the Schauder-basis conclusion.
-/

namespace ThmA

open Finset

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- **`lem:proj_finite`.** Projections of a finite combination `x = ∑_{k<N} a_k e_k`:
`P_m x = ∑_{k < min(m+1, N)} a_k e_k`. -/
theorem proj_of_finite (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (N : ℕ) (a : ℕ → ℝ) (m : ℕ) :
    proj e hbasis m (∑ k ∈ range N, a k • e k) = ∑ k ∈ range (min (m + 1) N), a k • e k := by
  -- truncating an `if k < N` sum over `range M` gives the `range (min M N)` sum
  have key : ∀ M : ℕ, (∑ k ∈ range M, (if k < N then a k else (0 : ℝ)) • e k)
                = ∑ k ∈ range (min M N), a k • e k := by
    intro M
    have hfilter : (range M).filter (· < N) = range (min M N) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    calc (∑ k ∈ range M, (if k < N then a k else (0 : ℝ)) • e k)
        = ∑ k ∈ range M, if k < N then a k • e k else 0 := by
          apply Finset.sum_congr rfl; intro k _; split_ifs <;> simp
      _ = ∑ k ∈ (range M).filter (· < N), a k • e k := by rw [Finset.sum_filter]
      _ = ∑ k ∈ range (min M N), a k • e k := by rw [hfilter]
  set x := ∑ k ∈ range N, a k • e k with hxdef
  have hcoord : coord e hbasis x = fun k => if k < N then a k else 0 := by
    symm
    apply coord_unique e hbasis
    apply sigmaOrderTendsto_of_eventuallyEq
    refine ⟨N, fun M hM => ?_⟩
    show (∑ k ∈ range (M + 1), (if k < N then a k else (0 : ℝ)) • e k) = x
    rw [key, show min (M + 1) N = N from by omega, hxdef]
  rw [proj, hcoord]
  exact key (m + 1)

/-- On the algebraic span of the basis vectors, the partial-sum projections
are eventually the identity. -/
theorem proj_eventually_eq_of_mem_span (e : ℕ → X) (hbasis : IsSigmaOrderBasis e)
    {x : X} (hx : x ∈ Submodule.span ℝ (Set.range e)) :
    ∃ N : ℕ, ∀ m ≥ N, proj e hbasis m x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨n, rfl⟩
      let a : ℕ → ℝ := fun k => if k = n then 1 else 0
      have heq : ∑ k ∈ range (n + 1), a k • e k = e n := by
        simp [a]
      refine ⟨n, fun m hm => ?_⟩
      rw [← heq, proj_of_finite, min_eq_right (by omega), heq]
  | zero =>
      exact ⟨0, fun m _ => proj_zero e hbasis m⟩
  | add x y _ _ hx hy =>
      rcases hx with ⟨Nx, hx⟩
      rcases hy with ⟨Ny, hy⟩
      refine ⟨max Nx Ny, fun m hm => ?_⟩
      rw [proj_add, hx m (le_trans (le_max_left _ _) hm),
        hy m (le_trans (le_max_right _ _) hm)]
  | smul a x _ hx =>
      rcases hx with ⟨N, hN⟩
      exact ⟨N, fun m hm => by rw [proj_smul, hN m hm]⟩

/-- Every partial-sum projection is bounded by the auxiliary norm. -/
theorem norm_proj_le_rho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (m : ℕ) (x : X) :
    ‖proj e hbasis m x‖ ≤ rho e hbasis x := by
  rw [rho_def]
  apply le_csInf ((rho_admissible_nonempty e hbasis x).image _)
  rintro _ ⟨u, ⟨hu0, hub⟩, rfl⟩
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg hu0]
  exact hub m

/-- **`lem:rho_eq_sup`.** For a finite combination, ρ equals the norm of the maximal function. -/
theorem rho_eq_norm_sup (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (N : ℕ) (hN : 1 ≤ N)
    (a : ℕ → ℝ) :
    rho e hbasis (∑ k ∈ range N, a k • e k)
      = ‖(range N).sup' (nonempty_range_iff.mpr (by omega))
          (fun m => |∑ k ∈ range (m + 1), a k • e k|)‖ := by
  have hne : (range N).Nonempty := nonempty_range_iff.mpr (by omega)
  set v : X := (range N).sup' hne (fun m => |∑ k ∈ range (m + 1), a k • e k|) with hvdef
  set x : X := ∑ k ∈ range N, a k • e k with hxdef
  have hv0 : 0 ≤ v := by
    rw [hvdef]
    exact le_trans (abs_nonneg _)
      (Finset.le_sup' (fun m => |∑ k ∈ range (m + 1), a k • e k|) (mem_range.mpr (by omega : 0 < N)))
  have hPm_le : ∀ m, |proj e hbasis m x| ≤ v := by
    intro m
    rw [hxdef, proj_of_finite]
    rw [hvdef, show min (m + 1) N = (min (m + 1) N - 1) + 1 from by omega]
    exact Finset.le_sup' (fun m => |∑ k ∈ range (m + 1), a k • e k|) (mem_range.mpr (by omega))
  refine le_antisymm ?_ ?_
  · rw [rho_def]
    exact csInf_le (admissible_bddBelow e hbasis x) ⟨v, ⟨hv0, hPm_le⟩, rfl⟩
  · rw [rho_def]
    apply le_csInf ((rho_admissible_nonempty e hbasis x).image _)
    rintro r ⟨u, ⟨hu0, hub⟩, rfl⟩
    have hvu : v ≤ u := by
      rw [hvdef]
      apply Finset.sup'_le
      intro m hm
      have hmN : m < N := mem_range.mp hm
      have hpeq : proj e hbasis m x = ∑ k ∈ range (m + 1), a k • e k := by
        rw [hxdef, proj_of_finite, min_eq_left (by omega)]
      rw [← hpeq]
      exact hub m
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg hv0, abs_of_nonneg hu0]
    exact hvu

/-- **`lem:const`.** The comparison constant: `∃ C, ∀ x, ρ(x) ≤ C‖x‖`.
The identity `ι : Xρ → X` is a continuous linear bijection between Banach spaces
(`Xρ` complete by `prop:rho_complete`), so its inverse is bounded. -/
theorem exists_const_rho_le (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    ∃ C : ℝ, ∀ x : X, rho e hbasis x ≤ C * ‖x‖ := by
  -- the linear identity `Xρ → X`
  let ιL : Xrho e hbasis →ₗ[ℝ] X :=
    { toFun := toX e hbasis
      map_add' := toX_add e hbasis
      map_smul' := fun c x => toX_smul e hbasis c x }
  have hbound : ∀ x : Xrho e hbasis, ‖ιL x‖ ≤ 1 * ‖x‖ := fun x => by
    rw [one_mul, norm_Xrho]; exact norm_le_rho e hbasis (toX e hbasis x)
  let ι : Xrho e hbasis →L[ℝ] X := ιL.mkContinuous 1 hbound
  have hιapp : ∀ y : Xrho e hbasis, ι y = toX e hbasis y := fun _ => rfl
  have hinj : Function.Injective ι := fun a b h => h
  have hsurj : Function.Surjective ι := fun z => ⟨ofX e hbasis z, rfl⟩
  have hker : (ι : Xrho e hbasis →ₗ[ℝ] X).ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : (ι : Xrho e hbasis →ₗ[ℝ] X).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let E := ContinuousLinearEquiv.ofBijective ι hker hrange
  refine ⟨‖(E.symm : X →L[ℝ] Xrho e hbasis)‖, fun x => ?_⟩
  have hEx : toX e hbasis (E.symm x) = x := by
    have h := E.apply_symm_apply x
    rwa [ContinuousLinearEquiv.coeFn_ofBijective, hιapp] at h
  have hnorm : ‖E.symm x‖ = rho e hbasis x := by rw [norm_Xrho, hEx]
  rw [← hnorm]
  exact (E.symm : X →L[ℝ] Xrho e hbasis).le_opNorm x

/-- **Schauder conclusion of Theorem A.** Under the dense-span hypothesis,
the canonical partial sums converge to every vector in norm. -/
theorem proj_tendsto_norm (e : ℕ → X) (hbasis : IsSigmaOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) (x : X) :
    Filter.Tendsto (fun m => proj e hbasis m x) Filter.atTop (nhds x) := by
  obtain ⟨C, hC⟩ := exists_const_rho_le e hbasis
  have hproj : ∀ m y, ‖proj e hbasis m y‖ ≤ |C| * ‖y‖ := by
    intro m y
    calc
      ‖proj e hbasis m y‖ ≤ rho e hbasis y := norm_proj_le_rho e hbasis m y
      _ ≤ C * ‖y‖ := hC y
      _ ≤ |C| * ‖y‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg y)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hK : 0 < |C| + 1 := by positivity
  have hxclosure : x ∈ closure (Submodule.span ℝ (Set.range e) : Set X) := by
    rw [← Submodule.topologicalClosure_coe, hspan]
    simp
  rcases Metric.mem_closure_iff.mp hxclosure (ε / (|C| + 1)) (div_pos hε hK) with
    ⟨y, hyspan, hxy⟩
  have hxynorm : ‖x - y‖ < ε / (|C| + 1) := by
    simpa [dist_eq_norm] using hxy
  rcases proj_eventually_eq_of_mem_span e hbasis hyspan with ⟨N, hN⟩
  refine ⟨N, fun m hm => ?_⟩
  have hdiff :
      ‖proj e hbasis m x - proj e hbasis m y‖ = ‖proj e hbasis m (x - y)‖ := by
    rw [proj_sub]
  calc
    dist (proj e hbasis m x) x = ‖proj e hbasis m x - x‖ := dist_eq_norm _ _
    _ = ‖(proj e hbasis m x - proj e hbasis m y) + (y - x)‖ := by
      rw [hN m hm]
      congr 1
      abel
    _ ≤ ‖proj e hbasis m x - proj e hbasis m y‖ + ‖y - x‖ := norm_add_le _ _
    _ = ‖proj e hbasis m (x - y)‖ + ‖y - x‖ := by rw [hdiff]
    _ ≤ |C| * ‖x - y‖ + ‖y - x‖ := add_le_add (hproj m (x - y)) le_rfl
    _ = (|C| + 1) * ‖x - y‖ := by rw [norm_sub_rev]; ring
    _ < ε := by simpa [mul_comm] using (lt_div_iff₀ hK).mp hxynorm

/-- A σ-order basis with dense span is a Schauder basis. This includes the
uniqueness argument from the proof of Theorem A, using continuity of each
partial-sum projection. -/
theorem isSchauderBasis_of_sigmaOrderBasis (e : ℕ → X)
    (hbasis : IsSigmaOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    IsSchauderBasis e := by
  intro x
  refine ⟨coord e hbasis x, ?_, ?_⟩
  · simpa [proj] using proj_tendsto_norm e hbasis hspan x
  · intro b hb
    obtain ⟨C, hC⟩ := exists_const_rho_le e hbasis
    have hproj : ∀ m y, ‖proj e hbasis m y‖ ≤ |C| * ‖y‖ := by
      intro m y
      calc
        ‖proj e hbasis m y‖ ≤ rho e hbasis y := norm_proj_le_rho e hbasis m y
        _ ≤ C * ‖y‖ := hC y
        _ ≤ |C| * ‖y‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg y)
    have hpartial : ∀ k,
        (∑ j ∈ range (k + 1), b j • e j) = proj e hbasis k x := by
      intro k
      let L : X →ₗ[ℝ] X :=
        { toFun := proj e hbasis k
          map_add' := proj_add e hbasis k
          map_smul' := fun c y => proj_smul e hbasis k c y }
      let P : X →L[ℝ] X := L.mkContinuous |C| (hproj k)
      have hmap : Filter.Tendsto
          (fun m => proj e hbasis k (∑ j ∈ range (m + 1), b j • e j))
          Filter.atTop (nhds (proj e hbasis k x)) := by
        change Filter.Tendsto
          (fun m => P (∑ j ∈ range (m + 1), b j • e j))
          Filter.atTop (nhds (P x))
        exact P.continuous.continuousAt.tendsto.comp hb
      have hconst : Filter.Tendsto
          (fun m => proj e hbasis k (∑ j ∈ range (m + 1), b j • e j))
          Filter.atTop (nhds (∑ j ∈ range (k + 1), b j • e j)) := by
        apply tendsto_atTop_of_eventually_const (i₀ := k)
        intro m hm
        rw [proj_of_finite, min_eq_left (by omega)]
      exact tendsto_nhds_unique hconst hmap
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hsum :
            (∑ k ∈ range (n + 1), b k • e k) =
              ∑ k ∈ range (n + 1), coord e hbasis x k • e k := by
          simpa [proj] using hpartial n
        rw [sum_range_succ, sum_range_succ] at hsum
        have hprefix :
            (∑ k ∈ range n, b k • e k) =
              ∑ k ∈ range n, coord e hbasis x k • e k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k (mem_range.mp hk)]
        rw [hprefix] at hsum
        exact (e_linearIndependent e hbasis).smul_left_injective n (add_left_cancel hsum)

/-- **Theorem A (σ-order form):** the maximal inequality. -/
theorem theoremA_sigma_order_form (e : ℕ → X)
    (hbasis : IsSigmaOrderBasis e)
    (_hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    ∃ C : ℝ, ∀ (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℝ),
      ‖(range N).sup' (nonempty_range_iff.mpr (by omega))
          (fun m => |∑ k ∈ range (m + 1), a k • e k|)‖
        ≤ C * ‖∑ k ∈ range N, a k • e k‖ := by
  obtain ⟨C, hC⟩ := exists_const_rho_le e hbasis
  refine ⟨C, fun N hN a => ?_⟩
  rw [← rho_eq_norm_sup e hbasis N hN a]
  exact hC _

/-- The Schauder-basis part of Theorem A for a σ-order basis. -/
theorem theoremA_sigma_order_schauder (e : ℕ → X)
    (hbasis : IsSigmaOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    IsSchauderBasis e :=
  isSchauderBasis_of_sigmaOrderBasis e hbasis hspan

/-- The maximal inequality in Theorem A for an order basis. The dense-span
hypothesis supplies separability, and Proposition `order-sigma` reduces this
case to the σ-order theorem. -/
theorem theoremA_order_form (e : ℕ → X)
    (hbasis : IsOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    ∃ C : ℝ, ∀ (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℝ),
      ‖(range N).sup' (nonempty_range_iff.mpr (by omega))
          (fun m => |∑ k ∈ range (m + 1), a k • e k|)‖
        ≤ C * ‖∑ k ∈ range N, a k • e k‖ :=
  theoremA_sigma_order_form e (hbasis.isSigmaOrderBasis_of_denseSpan hspan) hspan

/-- The Schauder-basis part of Theorem A for an order basis. -/
theorem theoremA_order_schauder (e : ℕ → X)
    (hbasis : IsOrderBasis e)
    (hspan : (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤) :
    IsSchauderBasis e :=
  isSchauderBasis_of_sigmaOrderBasis e
    (hbasis.isSigmaOrderBasis_of_denseSpan hspan) hspan

end ThmA
