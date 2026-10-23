import ThmBC.Tree.FiniteRank

/-!
# Intrinsic structure on the weighted ambient space

The paper treats `V_E`, `Z_E`, and `Y` as normed vector lattices, not merely
as sets equipped with closure predicates. This file installs the pointwise
algebra and order on `V_E` and verifies that the weighted supremum norm is a
lattice norm.
-/

namespace DSTBL3
namespace WeightedTree

universe u

set_option linter.unusedVariables false

instance instAddCommGroupV {E : Type u} [SeminormedAddCommGroup E] :
    AddCommGroup (V E) where
  add_assoc a b c := by apply Subtype.ext; funext s; exact add_assoc _ _ _
  add_zero a := by apply Subtype.ext; funext s; exact add_zero _
  zero_add a := by apply Subtype.ext; funext s; exact zero_add _
  neg_add_cancel a := by apply Subtype.ext; funext s; exact neg_add_cancel _
  add_comm a b := by apply Subtype.ext; funext s; exact add_comm _ _
  sub_eq_add_neg a b := by apply Subtype.ext; funext s; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModuleV {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Module ℝ (V E) where
  zero_smul x := by apply Subtype.ext; funext s; exact zero_smul ℝ (x s)
  one_smul x := by apply Subtype.ext; funext s; exact one_smul ℝ (x s)
  smul_zero a := by apply Subtype.ext; funext s; exact smul_zero a
  smul_add a x y := by apply Subtype.ext; funext s; exact smul_add a (x s) (y s)
  add_smul a b x := by apply Subtype.ext; funext s; exact add_smul a b (x s)
  mul_smul a b x := by apply Subtype.ext; funext s; exact mul_smul a b (x s)

theorem weightedNorm_neg_eq {E : Type u} [NormedAddCommGroup E] (x : V E) :
    ‖-x‖ = ‖x‖ := by
  apply le_antisymm
  · apply weightedNorm_le_of_forall
    intro s
    change weight s * ‖-x s‖ ≤ ‖x‖
    rw [norm_neg]
    exact weighted_coordinate_le_norm x s
  · apply weightedNorm_le_of_forall
    intro s
    change weight s * ‖x s‖ ≤ ‖-x‖
    rw [← norm_neg (x s)]
    exact weighted_coordinate_le_norm (-x) s

noncomputable instance instMetricSpaceV {E : Type u} [NormedAddCommGroup E] :
    MetricSpace (V E) where
  dist x y := ‖x - y‖
  dist_self x := by rw [sub_self, weightedNorm_zero]
  dist_comm x y := by
    rw [show x - y = -(y - x) by abel, weightedNorm_neg_eq]
  dist_triangle := weightedNorm_sub_le
  eq_of_dist_eq_zero := by
    intro x y hxy
    apply Subtype.ext
    funext s
    have hcoord := coordinate_norm_le_div_weight (x - y) s
    rw [hxy, zero_div] at hcoord
    have hz : (x - y : V E) s = 0 := norm_eq_zero.mp (le_antisymm hcoord (norm_nonneg _))
    exact sub_eq_zero.mp hz

noncomputable instance instSeminormedAddCommGroupV {E : Type u}
    [NormedAddCommGroup E] : SeminormedAddCommGroup (V E) where
  __ := instMetricSpaceV (E := E)
  __ := instNormV
  dist_eq x y := by
    change ‖x - y‖ = ‖-x + y‖
    rw [show -x + y = -(x - y) by abel, weightedNorm_neg_eq]

noncomputable instance instNormedAddCommGroupV {E : Type u}
    [NormedAddCommGroup E] : NormedAddCommGroup (V E) where
  __ := instSeminormedAddCommGroupV (E := E)
  __ := instMetricSpaceV (E := E)

instance instNormedSpaceV {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (V E) where
  __ := instModuleV (E := E)
  norm_smul_le a x := by
    calc
      ‖a • x‖ = ‖(a • x) - a • (0 : V E)‖ := by rw [smul_zero, sub_zero]
      _ ≤ ‖a‖ * ‖x - (0 : V E)‖ := weightedNorm_smul_sub_smul_le a x 0
      _ = ‖a‖ * ‖x‖ := by rw [sub_zero]

instance instLEV {E : Type u} [NormedAddCommGroup E] [LE E] : LE (V E) :=
  ⟨fun x y => ∀ s, x s ≤ y s⟩

instance instLTV {E : Type u} [NormedAddCommGroup E] [LE E] : LT (V E) :=
  ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩

instance instPartialOrderV {E : Type u} [NormedAddCommGroup E] [PartialOrder E] :
    PartialOrder (V E) where
  le_refl x s := le_rfl
  le_trans x y z hxy hyz s := (hxy s).trans (hyz s)
  le_antisymm x y hxy hyx := by
    apply Subtype.ext
    funext s
    exact le_antisymm (hxy s) (hyx s)

instance instLatticeV {E : Type u} [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [HasSolidNorm E] : Lattice (V E) where
  sup := Max.max
  inf := Min.min
  sup_le x y z hx hy s := sup_le (hx s) (hy s)
  le_sup_left x y s := le_sup_left
  le_sup_right x y s := le_sup_right
  le_inf x y z hx hy s := le_inf (hx s) (hy s)
  inf_le_left x y s := inf_le_left
  inf_le_right x y s := inf_le_right

instance instIsOrderedAddMonoidV {E : Type u} [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [HasSolidNorm E] : IsOrderedAddMonoid (V E) where
  add_le_add_left x y h z s := IsOrderedAddMonoid.add_le_add_left (x s) (y s) (h s) (z s)
  add_le_add_right x y h z s := IsOrderedAddMonoid.add_le_add_right (x s) (y s) (h s) (z s)

instance instPosSMulMonoV {E : Type u} [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] :
    PosSMulMono ℝ (V E) where
  smul_le_smul_of_nonneg_left _a ha _x _y hxy s :=
    PosSMulMono.smul_le_smul_of_nonneg_left ha (hxy s)

instance instHasSolidNormV {E : Type u} [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [HasSolidNorm E] : HasSolidNorm (V E) where
  solid {x y} hxy := by
    apply weightedNorm_le_of_forall
    intro s
    calc
      weight s * ‖x s‖ ≤ weight s * ‖y s‖ :=
        mul_le_mul_of_nonneg_left (HasSolidNorm.solid (hxy s)) (weight_nonneg s)
      _ ≤ ‖y‖ := weighted_coordinate_le_norm y s

noncomputable instance instVectorLatticeV {E : Type u} [NormedAddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [HasSolidNorm E] [NormedSpace ℝ E] [PosSMulMono ℝ E] :
    VectorLattice (V E) := VectorLattice.mk

noncomputable instance instNormedVectorLatticeV {E : Type u}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
    [NormedSpace ℝ E] [PosSMulMono ℝ E] : NormedVectorLattice (V E) :=
  NormedVectorLattice.mk

end WeightedTree
end DSTBL3
