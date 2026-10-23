import Lean_Code.ThmA.Coordinates

/-!
# The auxiliary norm ρ and the second normed structure (paper Section 4)

`rho` and the type synonym `Xrho` are the formal counterparts of the
auxiliary norm and renormed space in the paper.
-/

namespace ThmA

open Finset

set_option linter.unusedSectionVars false

variable {X : Type*}
  [NormedAddCommGroup X] [Lattice X] [HasSolidNorm X] [IsOrderedAddMonoid X]
  [NormedSpace ℝ X] [PosSMulMono ℝ X] [CompleteSpace X]

/-- **`con:rho`.** The admissible set `A(x) = {u ≥ 0 : ∀ m, |P_m x| ≤ u}`. -/
def admissible (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) : Set X :=
  {u | 0 ≤ u ∧ ∀ m, |proj e hbasis m x| ≤ u}

/-- **`con:rho`.** `ρ(x) = inf { ‖u‖ : u ∈ A(x) }`. -/
noncomputable def rho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) : ℝ :=
  sInf ((fun u => ‖u‖) '' admissible e hbasis x)

/-- The set `{‖u‖ : u ∈ A(x)}` is bounded below by `0`. -/
theorem admissible_bddBelow (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    BddBelow ((fun u => ‖u‖) '' admissible e hbasis x) :=
  ⟨0, by rintro r ⟨u, _, rfl⟩; exact norm_nonneg u⟩

theorem rho_def (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    rho e hbasis x = sInf ((fun u => ‖u‖) '' admissible e hbasis x) := rfl

/-- **`lem:rho_wd`.** `A(x)` is nonempty. -/
theorem rho_admissible_nonempty (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    (admissible e hbasis x).Nonempty := by
  obtain ⟨u, hu0, hub⟩ := (proj_sigmaOrderTendsto e hbasis x).orderBounded
  exact ⟨u, hu0, hub⟩

/-- `0 ≤ ρ(x)`. -/
theorem rho_nonneg (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    0 ≤ rho e hbasis x := by
  rw [rho_def]
  apply le_csInf ((rho_admissible_nonempty e hbasis x).image _)
  rintro r ⟨u, _, rfl⟩
  exact norm_nonneg u

/-- **`lem:norm_le_rho`.** `‖x‖ ≤ ρ(x)`. -/
theorem norm_le_rho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    ‖x‖ ≤ rho e hbasis x := by
  rw [rho_def]
  apply le_csInf ((rho_admissible_nonempty e hbasis x).image _)
  rintro r ⟨u, ⟨hu0, hub⟩, rfl⟩
  have habs : |x| ≤ u := (proj_sigmaOrderTendsto e hbasis x).abs_le hu0 hub
  have hbu : |x| ≤ |u| := by rw [abs_of_nonneg hu0]; exact habs
  exact norm_le_norm_of_abs_le_abs hbu

/-- **`lem:rho_approx`.** ε-approximation of the infimum ρ. -/
theorem rho_approx (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ admissible e hbasis x, ‖u‖ ≤ rho e hbasis x + ε := by
  have hne := (rho_admissible_nonempty e hbasis x).image (fun u => ‖u‖)
  have hlt : sInf ((fun u => ‖u‖) '' admissible e hbasis x) < rho e hbasis x + ε := by
    rw [← rho_def]; linarith
  obtain ⟨r, hr_mem, hr_lt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨u, hu_mem, rfl⟩ := hr_mem
  exact ⟨u, hu_mem, le_of_lt hr_lt⟩

/-- `ρ(0) = 0`. -/
theorem rho_zero_eq (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) : rho e hbasis (0 : X) = 0 := by
  refine le_antisymm ?_ (rho_nonneg e hbasis 0)
  rw [rho_def]
  refine csInf_le (admissible_bddBelow e hbasis 0) ⟨0, ⟨le_refl 0, fun m => ?_⟩, norm_zero⟩
  rw [proj_zero]; simp

/-- **`lem:rho_zero`.** `ρ(x) = 0 ↔ x = 0`. -/
theorem rho_eq_zero_iff (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    rho e hbasis x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : ‖x‖ ≤ 0 := h ▸ norm_le_rho e hbasis x
    exact norm_le_zero_iff.mp this
  · rintro rfl; exact rho_zero_eq e hbasis

/-- **`lem:rho_smul`** (`≤` half, valid for all `α`). -/
theorem rho_smul_le (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (α : ℝ) (x : X) :
    rho e hbasis (α • x) ≤ |α| * rho e hbasis x := by
  rcases eq_or_ne α 0 with h0 | h0
  · subst h0; rw [abs_zero, zero_mul, zero_smul]; exact le_of_eq (rho_zero_eq e hbasis)
  · have hpos : 0 < |α| := abs_pos.mpr h0
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u, ⟨hu0, hub⟩, hu⟩ := rho_approx e hbasis x (div_pos hε hpos)
    have hmem : |α| • u ∈ admissible e hbasis (α • x) := by
      refine ⟨smul_nonneg (abs_nonneg α) hu0, fun m => ?_⟩
      rw [proj_smul, abs_smul_vectorLattice]
      exact smul_le_smul_of_nonneg_left (hub m) (abs_nonneg α)
    calc rho e hbasis (α • x) ≤ ‖|α| • u‖ :=
          csInf_le (admissible_bddBelow e hbasis (α • x)) ⟨|α| • u, hmem, rfl⟩
      _ = |α| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_abs]
      _ ≤ |α| * (rho e hbasis x + ε / |α|) := mul_le_mul_of_nonneg_left hu (le_of_lt hpos)
      _ = |α| * rho e hbasis x + ε := by field_simp

/-- **`lem:rho_smul`.** `ρ(α • x) = |α| * ρ(x)`. -/
theorem rho_smul (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (α : ℝ) (x : X) :
    rho e hbasis (α • x) = |α| * rho e hbasis x := by
  refine le_antisymm (rho_smul_le e hbasis α x) ?_
  rcases eq_or_ne α 0 with h0 | h0
  · subst h0; rw [abs_zero, zero_mul]; exact rho_nonneg e hbasis _
  · have hpos : 0 < |α| := abs_pos.mpr h0
    have h1 : rho e hbasis x ≤ |α|⁻¹ * rho e hbasis (α • x) := by
      have := rho_smul_le e hbasis α⁻¹ (α • x)
      rwa [inv_smul_smul₀ h0, abs_inv] at this
    calc |α| * rho e hbasis x
        ≤ |α| * (|α|⁻¹ * rho e hbasis (α • x)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hpos)
      _ = rho e hbasis (α • x) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]

/-- **`lem:rho_add`.** `ρ(x + y) ≤ ρ(x) + ρ(y)`. -/
theorem rho_add_le (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x y : X) :
    rho e hbasis (x + y) ≤ rho e hbasis x + rho e hbasis y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, ⟨hu0, hub⟩, hu⟩ := rho_approx e hbasis x (half_pos hε)
  obtain ⟨v, ⟨hv0, hvb⟩, hv⟩ := rho_approx e hbasis y (half_pos hε)
  have hmem : u + v ∈ admissible e hbasis (x + y) := by
    refine ⟨add_nonneg hu0 hv0, fun m => ?_⟩
    calc |proj e hbasis m (x + y)| = |proj e hbasis m x + proj e hbasis m y| := by rw [proj_add]
      _ ≤ |proj e hbasis m x| + |proj e hbasis m y| := abs_add_le _ _
      _ ≤ u + v := add_le_add (hub m) (hvb m)
  calc rho e hbasis (x + y) ≤ ‖u + v‖ :=
        csInf_le (admissible_bddBelow e hbasis (x + y)) ⟨u + v, hmem, rfl⟩
    _ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
    _ ≤ (rho e hbasis x + ε / 2) + (rho e hbasis y + ε / 2) := add_le_add hu hv
    _ = rho e hbasis x + rho e hbasis y + ε := by ring

/-- `ρ` is invariant under negation (from `lem:rho_smul`; helper for `con:Xrho`). -/
theorem rho_neg (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : X) :
    rho e hbasis (-x) = rho e hbasis x := by
  rw [show -x = (-1 : ℝ) • x from (neg_one_smul ℝ x).symm, rho_smul e hbasis]; simp

/-! ### Construction `con:Xrho`: the vector space `X` re-normed by ρ.

Lean cannot carry two `NormedAddCommGroup` instances on `X`, so `Xrho` is a type synonym.
`toX`/`ofX` are the (definitional) identity coercions; they act as a syntactic barrier so
that the `ρ`-structure and `X`'s structure do not get confused during elaboration. -/

set_option linter.unusedVariables false in
/-- **`con:Xrho`.** Type synonym for `X` carrying the norm `ρ`. -/
def Xrho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) : Type _ := X

set_option linter.unusedVariables false in
/-- Identity coercion `Xrho → X` (the linear map `ι` of the TeX). -/
def toX (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) : Xrho e hbasis → X := id

set_option linter.unusedVariables false in
/-- Identity coercion `X → Xrho`. -/
def ofX (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) : X → Xrho e hbasis := id

/-- Transport the additive group structure. -/
instance instAddCommGroupXrho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    AddCommGroup (Xrho e hbasis) := inferInstanceAs (AddCommGroup X)

/-- Transport the `ℝ`-module structure. -/
instance instModuleXrho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    Module ℝ (Xrho e hbasis) := inferInstanceAs (Module ℝ X)

@[simp] theorem toX_zero (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    toX e hbasis 0 = 0 := rfl
@[simp] theorem toX_add (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x y : Xrho e hbasis) :
    toX e hbasis (x + y) = toX e hbasis x + toX e hbasis y := rfl
@[simp] theorem toX_neg (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : Xrho e hbasis) :
    toX e hbasis (-x) = -(toX e hbasis x) := rfl
@[simp] theorem toX_smul (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (α : ℝ) (x : Xrho e hbasis) :
    toX e hbasis (α • x) = α • toX e hbasis x := rfl
@[simp] theorem toX_sub (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x y : Xrho e hbasis) :
    toX e hbasis (x - y) = toX e hbasis x - toX e hbasis y := rfl
@[simp] theorem ofX_toX (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : Xrho e hbasis) :
    ofX e hbasis (toX e hbasis x) = x := rfl
@[simp] theorem toX_ofX (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (y : X) :
    toX e hbasis (ofX e hbasis y) = y := rfl

/-- ρ as a bundled `AddGroupNorm` on `Xrho`. -/
noncomputable def rhoAGN (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    AddGroupNorm (Xrho e hbasis) where
  toFun x := rho e hbasis (toX e hbasis x)
  map_zero' := (rho_eq_zero_iff e hbasis 0).mpr rfl
  add_le' x y := by rw [toX_add]; exact rho_add_le e hbasis _ _
  neg' x := by rw [toX_neg]; exact rho_neg e hbasis _
  eq_zero_of_map_eq_zero' x := fun h => (rho_eq_zero_iff e hbasis (toX e hbasis x)).mp h

/-- The ρ-normed additive group structure on `Xrho`. -/
noncomputable instance instNormedAddCommGroupXrho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    NormedAddCommGroup (Xrho e hbasis) :=
  AddGroupNorm.toNormedAddCommGroup (rhoAGN e hbasis)

/-- The norm on `Xrho` is exactly `ρ` of the underlying vector (definitional). -/
theorem norm_Xrho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) (x : Xrho e hbasis) :
    ‖x‖ = rho e hbasis (toX e hbasis x) := rfl

/-- `Xrho` is a normed `ℝ`-space (homogeneity of ρ). -/
noncomputable instance instNormedSpaceXrho (e : ℕ → X) (hbasis : IsSigmaOrderBasis e) :
    NormedSpace ℝ (Xrho e hbasis) where
  norm_smul_le α x := le_of_eq <| by
    show rho e hbasis (toX e hbasis (α • x)) = ‖α‖ * rho e hbasis (toX e hbasis x)
    rw [toX_smul, rho_smul e hbasis, Real.norm_eq_abs]

end ThmA
