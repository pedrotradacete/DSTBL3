import Lean_Code.ThmA.AuxNorm

/-!
# Completeness of `(X, ρ)` (paper Section 4)

`tower_eq_proj`, `rho_series`, and the `CompleteSpace Xρ` instance are proved here.
-/

namespace ThmA

open Finset

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- Coordinates are additive over finite sums. -/
theorem coord_sum (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (s : Finset ℕ) (f : ℕ → X) (k : ℕ) :
    coord e hbasis (∑ r ∈ s, f r) k = ∑ r ∈ s, coord e hbasis (f r) k := by
  classical
  induction s using Finset.induction with
  | empty => simp [coord_zero]
  | @insert a s h ih => rw [Finset.sum_insert h, coord_add, ih, Finset.sum_insert h]

/-- Projections are additive over finite sums. -/
theorem proj_sum (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (m : ℕ) (s : Finset ℕ) (f : ℕ → X) :
    proj e hbasis m (∑ r ∈ s, f r) = ∑ r ∈ s, proj e hbasis m (f r) := by
  classical
  induction s using Finset.induction with
  | empty => simp [proj_zero]
  | @insert a s h ih => rw [Finset.sum_insert h, proj_add, ih, Finset.sum_insert h]

/-- Projections are subtractive. -/
theorem proj_sub (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (m : ℕ) (x y : X) :
    proj e hbasis m (x - y) = proj e hbasis m x - proj e hbasis m y := by
  rw [sub_eq_add_neg, proj_add, ← neg_one_smul ℝ y, proj_smul, neg_one_smul, ← sub_eq_add_neg]

/-- Triangle inequality for finite sums in the (non-linear) lattice `X`.
Mathlib's `Finset.abs_sum_le_sum_abs` needs a `LinearOrder`, which `X` lacks. -/
theorem abs_sum_le (s : Finset ℕ) (f : ℕ → X) : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s h ih =>
    rw [Finset.sum_insert h, Finset.sum_insert h]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)

/-- **`lem:tower_eq_proj`.** A compatible tower of finite sections is the projection tower.
`c m k` are the coordinates of `y_m` in `E_m = span{e_0,…,e_m}`; condition `hcompat` is
`Q_m y_{m+1} = y_m`. -/
theorem proj_of_compatible_tower (e : ℕ → X) (hbasis : IsSigmaOrderBasis e)
    (y : ℕ → X) (x : X) (c : ℕ → ℕ → ℝ)
    (hy : ∀ m, y m = ∑ k ∈ range (m + 1), c m k • e k)
    (hcompat : ∀ m k, k ≤ m → c (m + 1) k = c m k)
    (hconv : SigmaOrderTendsto y x) :
    ∀ m, y m = proj e hbasis m x := by
  -- the coordinates stabilise: `c m k = c k k` for `k ≤ m`
  have hck : ∀ m k, k ≤ m → c m k = c k k := by
    intro m
    induction m with
    | zero => intro k hk; obtain rfl : k = 0 := Nat.le_zero.mp hk; rfl
    | succ m ih =>
      intro k hk
      rcases hk.lt_or_eq with h | h
      · rw [hcompat m k (by omega), ih k (by omega)]
      · rw [h]
  set a : ℕ → ℝ := fun k => c k k with ha_def
  have hy_eq : ∀ m, y m = ∑ k ∈ range (m + 1), a k • e k := by
    intro m
    rw [hy m]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [ha_def, hck m k (by omega)]
  have hconv' : SigmaOrderTendsto (fun m => ∑ k ∈ range (m + 1), a k • e k) x := by
    have heq : (fun m => ∑ k ∈ range (m + 1), a k • e k) = y := funext fun m => (hy_eq m).symm
    rw [heq]; exact hconv
  have ha := coord_unique e hbasis hconv'
  intro m
  rw [hy_eq m, ha]
  rfl

set_option maxHeartbeats 1000000 in
open Filter in
/-- **`lem:rho_series`.** Norm-summable series converge in ρ: if `∑_r ρ(v_r) < ∞` then the
partial sums `x_R = ∑_{r<R} v_r` ρ-converge to some `x`.

Cleaner than the TeX's finite-dimensional route: since `coord` is linear,
`coord(x_R) k = ∑_{r<R} coord(v_r) k`, so we define `d_k = ∑'_r coord(v_r) k` (summable
because `|coord(v_r) k| ‖e_k‖ ≤ 2‖u_r‖`) and take `y_m = ∑_{k≤m} d_k e_k` directly. -/
theorem rho_summable_of_rho_summable (e : ℕ → X) (hbasis : IsSigmaOrderBasis e)
    (v : ℕ → X) (hsum : Summable (fun r => rho e hbasis (v r))) :
    ∃ x : X, Filter.Tendsto (fun R => rho e hbasis (x - ∑ r ∈ range R, v r))
      Filter.atTop (nhds 0) := by
  classical
  -- Step 1: order bounds `u_r ∈ A(v_r)`
  have hchoice : ∀ r, ∃ w ∈ admissible e hbasis (v r), ‖w‖ ≤ rho e hbasis (v r) + (1/2)^r :=
    fun r => rho_approx e hbasis (v r) (by positivity)
  choose u hu_mem hu_norm using hchoice
  have hu_nonneg : ∀ r, 0 ≤ u r := fun r => (hu_mem r).1
  have hu_bound : ∀ r m, |proj e hbasis m (v r)| ≤ u r := fun r => (hu_mem r).2
  have hgeom : Summable (fun r : ℕ => (1/2 : ℝ)^r) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum_u : Summable (fun r => ‖u r‖) :=
    Summable.of_nonneg_of_le (fun r => norm_nonneg _) hu_norm (hsum.add hgeom)
  have hsum_v : Summable (fun r => ‖v r‖) :=
    Summable.of_nonneg_of_le (fun r => norm_nonneg _) (fun r => norm_le_rho e hbasis (v r)) hsum
  have hu_summable : Summable u := hsum_u.of_norm
  have hv_summable : Summable v := hsum_v.of_norm
  have habsv_summable : Summable (fun r => |v r|) :=
    Summable.of_norm (by simpa [norm_abs_eq_norm] using hsum_v)
  -- partial-sum splitting
  have hdiff : ∀ R S, (∑ r ∈ range (S + R), v r) - (∑ r ∈ range R, v r) = ∑ r ∈ range S, v (R + r) := by
    intro R S; rw [Nat.add_comm S R, Finset.sum_range_add]; abel
  -- e_k ≠ 0
  have he_norm_pos : ∀ k, 0 < ‖e k‖ :=
    fun k => norm_pos_iff.mpr ((e_linearIndependent e hbasis).ne_zero k)
  -- coordinate bounds and summability
  have hSk : ∀ r k, |∑ j ∈ range k, coord e hbasis (v r) j • e j| ≤ u r := by
    intro r k
    cases k with
    | zero => simpa using hu_nonneg r
    | succ k => exact hu_bound r k
  have hcoord_eq : ∀ r k, coord e hbasis (v r) k • e k
      = proj e hbasis k (v r) - ∑ j ∈ range k, coord e hbasis (v r) j • e j := by
    intro r k; rw [proj, Finset.sum_range_succ]; abel
  have hcoord_norm : ∀ r k, ‖coord e hbasis (v r) k • e k‖ ≤ 2 * ‖u r‖ := by
    intro r k
    have habs : |coord e hbasis (v r) k • e k| ≤ u r + u r := by
      rw [hcoord_eq r k]
      have htri : |proj e hbasis k (v r) - ∑ j ∈ range k, coord e hbasis (v r) j • e j|
          ≤ |proj e hbasis k (v r)| + |∑ j ∈ range k, coord e hbasis (v r) j • e j| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      exact htri.trans (add_le_add (hu_bound r k) (hSk r k))
    have h1 : ‖coord e hbasis (v r) k • e k‖ ≤ ‖u r + u r‖ := by
      apply norm_le_norm_of_abs_le_abs
      rwa [abs_of_nonneg (add_nonneg (hu_nonneg r) (hu_nonneg r))]
    exact h1.trans (by rw [two_mul]; exact norm_add_le _ _)
  have hcoord_scalar : ∀ r k, |coord e hbasis (v r) k| ≤ 2 * ‖u r‖ / ‖e k‖ := by
    intro r k
    rw [le_div_iff₀ (he_norm_pos k)]
    calc |coord e hbasis (v r) k| * ‖e k‖ = ‖coord e hbasis (v r) k • e k‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 2 * ‖u r‖ := hcoord_norm r k
  have hcoord_summable : ∀ k, Summable (fun r => coord e hbasis (v r) k) := by
    intro k
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun r => norm_nonneg _) (fun r => ?_) (hsum_u.mul_left (2 / ‖e k‖))
    rw [Real.norm_eq_abs, show 2 / ‖e k‖ * ‖u r‖ = 2 * ‖u r‖ / ‖e k‖ from by ring]
    exact hcoord_scalar r k
  set d : ℕ → ℝ := fun k => ∑' r, coord e hbasis (v r) k with hd_def
  set y : ℕ → X := fun m => ∑ k ∈ range (m + 1), d k • e k with hy_def
  have hcoord_xR : ∀ R k, coord e hbasis (∑ r ∈ range R, v r) k = ∑ r ∈ range R, coord e hbasis (v r) k :=
    fun R k => coord_sum e hbasis (range R) v k
  have hd_tendsto : ∀ k, Tendsto (fun R => coord e hbasis (∑ r ∈ range R, v r) k) atTop (nhds (d k)) := by
    intro k
    simp_rw [hcoord_xR]
    exact (hcoord_summable k).hasSum.tendsto_sum_nat
  have hproj_xR_tendsto : ∀ m, Tendsto (fun R => proj e hbasis m (∑ r ∈ range R, v r)) atTop (nhds (y m)) := by
    intro m
    rw [hy_def]
    simp_rw [proj]
    exact tendsto_finsetSum _ (fun k _ => (hd_tendsto k).smul_const (e k))
  refine ⟨∑' r, v r, ?_⟩
  set x : X := ∑' r, v r with hx_def
  have hx_tendsto : Tendsto (fun S => ∑ r ∈ range S, v r) atTop (nhds x) := hv_summable.hasSum.tendsto_sum_nat
  -- Step 3: |y_m - P_m x_R| ≤ U_R
  have hstep3 : ∀ m R, |y m - proj e hbasis m (∑ r ∈ range R, v r)| ≤ ∑' r, u (r + R) := by
    intro m R
    refine abs_le_of_tendsto (x := fun S => proj e hbasis m (∑ r ∈ range (S + R), v r) - proj e hbasis m (∑ r ∈ range R, v r)) ?_ ?_
    · exact ((hproj_xR_tendsto m).comp (tendsto_add_atTop_nat R)).sub tendsto_const_nhds
    · intro S
      rw [← proj_sub, hdiff R S, proj_sum]
      calc |∑ r ∈ range S, proj e hbasis m (v (R + r))|
          ≤ ∑ r ∈ range S, |proj e hbasis m (v (R + r))| := abs_sum_le _ _
        _ ≤ ∑ r ∈ range S, u (R + r) := Finset.sum_le_sum (fun r _ => hu_bound (R + r) m)
        _ = ∑ r ∈ range S, u (r + R) := Finset.sum_congr rfl (fun r _ => by rw [Nat.add_comm])
        _ ≤ ∑' r, u (r + R) := Summable.sum_le_tsum (range S) (fun r _ => hu_nonneg (r + R)) ((summable_nat_add_iff R).mpr hu_summable)
  -- Step 2: |x - x_R| ≤ T_R
  have hstep2 : ∀ R, |x - ∑ r ∈ range R, v r| ≤ ∑' r, |v (r + R)| := by
    intro R
    refine abs_le_of_tendsto (x := fun S => (∑ r ∈ range (S + R), v r) - (∑ r ∈ range R, v r)) ?_ ?_
    · exact (hx_tendsto.comp (tendsto_add_atTop_nat R)).sub tendsto_const_nhds
    · intro S
      rw [hdiff R S]
      calc |∑ r ∈ range S, v (R + r)|
          ≤ ∑ r ∈ range S, |v (R + r)| := abs_sum_le _ _
        _ = ∑ r ∈ range S, |v (r + R)| := Finset.sum_congr rfl (fun r _ => by rw [Nat.add_comm])
        _ ≤ ∑' r, |v (r + R)| := Summable.sum_le_tsum (range S) (fun r _ => abs_nonneg (v (r + R))) ((summable_nat_add_iff R).mpr habsv_summable)
  -- regulators
  have hU : DownToZero (fun R => ∑' r, u (r + R)) := downToZero_tsum_tail hu_nonneg hsum_u
  have hT : DownToZero (fun R => ∑' r, |v (r + R)|) :=
    downToZero_tsum_tail (fun r => abs_nonneg _) (by simpa [norm_abs_eq_norm] using hsum_v)
  -- regulators for P_m x_R ⟶σo x_R
  choose wR hw_dtz hw_bnd using
    (fun R => proj_sigmaOrderTendsto e hbasis (∑ r ∈ range R, v r) :
      ∀ R, SigmaOrderTendsto (fun m => proj e hbasis m (∑ r ∈ range R, v r)) (∑ r ∈ range R, v r))
  -- Step 4: y ⟶σo x  (diagonal regulator)
  have hconv : SigmaOrderTendsto y x := by
    refine sigmaOrderTendsto_of_diagonal (c := fun R => (∑' r, u (r + R)) + ∑' r, |v (r + R)|)
      (w := wR) (hU.add hT) hw_dtz ?_
    intro R j
    obtain ⟨n0, hn0⟩ := hw_bnd R j
    refine ⟨n0, fun m hm => ?_⟩
    have hb1 := hstep3 m R
    have hb2 := hn0 m hm
    have hb3 : |(∑ r ∈ range R, v r) - x| ≤ ∑' r, |v (r + R)| := by
      rw [abs_sub_comm]; exact hstep2 R
    have htri : y m - x = (y m - proj e hbasis m (∑ r ∈ range R, v r))
        + (proj e hbasis m (∑ r ∈ range R, v r) - (∑ r ∈ range R, v r))
        + ((∑ r ∈ range R, v r) - x) := by abel
    calc |y m - x|
        = |(y m - proj e hbasis m (∑ r ∈ range R, v r))
            + (proj e hbasis m (∑ r ∈ range R, v r) - (∑ r ∈ range R, v r))
            + ((∑ r ∈ range R, v r) - x)| := by rw [htri]
      _ ≤ |(y m - proj e hbasis m (∑ r ∈ range R, v r))
            + (proj e hbasis m (∑ r ∈ range R, v r) - (∑ r ∈ range R, v r))|
            + |(∑ r ∈ range R, v r) - x| := abs_add_le _ _
      _ ≤ (|y m - proj e hbasis m (∑ r ∈ range R, v r)|
            + |proj e hbasis m (∑ r ∈ range R, v r) - (∑ r ∈ range R, v r)|)
            + |(∑ r ∈ range R, v r) - x| := add_le_add (abs_add_le _ _) (le_refl _)
      _ ≤ ((∑' r, u (r + R)) + wR R j) + ∑' r, |v (r + R)| := add_le_add (add_le_add hb1 hb2) hb3
      _ = ((∑' r, u (r + R)) + ∑' r, |v (r + R)|) + wR R j := by abel
  -- Step 5: y_m = P_m x
  have htower := proj_of_compatible_tower e hbasis y x (fun _ k => d k) (fun _ => rfl)
    (fun _ _ _ => rfl) hconv
  -- Step 6: U_R ∈ A(x - x_R), so ρ(x - x_R) ≤ ‖U_R‖ → 0
  have hUR_tendsto : Tendsto (fun R => ‖∑' r, u (r + R)‖) atTop (nhds 0) := by
    simpa using (tendsto_sum_nat_add u).norm
  refine squeeze_zero (fun R => rho_nonneg e hbasis _) (fun R => ?_) hUR_tendsto
  rw [rho_def]
  refine csInf_le (admissible_bddBelow e hbasis _) ⟨∑' r, u (r + R), ⟨tsum_nonneg (fun r => hu_nonneg _), fun m => ?_⟩, rfl⟩
  rw [proj_sub, ← htower m]
  exact hstep3 m R

/-- `toX` is additive over finite sums. -/
theorem toX_sum (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (s : Finset ℕ) (g : ℕ → Xrho e hbasis) :
    toX e hbasis (∑ i ∈ s, g i) = ∑ i ∈ s, toX e hbasis (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s h ih => rw [Finset.sum_insert h, toX_add, ih, Finset.sum_insert h]

open Filter in
/-- **`prop:rho_complete`.** `Xρ` is a Banach space. Every ρ-norm-summable series converges
(`rho_series`), which is the completeness criterion. -/
instance instCompleteSpaceXrho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    CompleteSpace (Xrho e hbasis) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro f hf
  have hsum : Summable (fun r => rho e hbasis (toX e hbasis (f r))) := by
    simpa only [norm_Xrho] using hf
  obtain ⟨x, hx⟩ := rho_summable_of_rho_summable e hbasis (fun r => toX e hbasis (f r)) hsum
  refine ⟨ofX e hbasis x, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ n, ‖(∑ i ∈ range n, f i) - ofX e hbasis x‖
      = rho e hbasis (x - ∑ r ∈ range n, toX e hbasis (f r)) := by
    intro n
    rw [norm_Xrho, toX_sub, toX_sum, toX_ofX, ← neg_sub, rho_neg]
  simp_rw [heq]
  exact hx

end ThmA
