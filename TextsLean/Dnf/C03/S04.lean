import TextsLean.Basic

namespace Dnf.C03.S04

/- Proposition 3.21 -/
example [CommGroup G] [Finite G] (p : ℕ) (hp : p.Prime) (hG : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by sorry

/- Definition 3.4.1 **simple** group

  A simple group is a nontrivial group that has only itself and the
  trivial subgroup as its normal subgroups
-/
example [Group G] : IsSimpleGroup G ↔ Nontrivial G ∧ ∀ (H : Subgroup G) (hH : H.Normal), H = ⊥ ∨ H = ⊤ := by sorry
#check IsSimpleGroup
#check IsSimpleAddGroup

example [Group G] (hG : (Nat.card G).Prime) : IsSimpleGroup G := by sorry

namespace QuotientGroup

end QuotientGroup

namespace JordanHolderModule

#check QuotientGroup.quotientMapSubgroupOfOfLe
#check QuotientGroup.equivQuotientSubgroupOfOfEq
#check QuotientGroup.quotientInfEquivProdNormalQuotient

def IsMaximalNormal [Group G] (X Y : Subgroup G) := X ⋖ Y ∧ (X.subgroupOf Y).Normal

/-- An isomorphism `X₂ / X₁ ∩ X₂ ≅ Y₂ / Y₁ ∩ Y₂` of modules for pairs
`(X₁,X₂) (Y₁,Y₂) : Subgroup G × Subgroup G`, given that `X₁ ∩ X₂ ⊴ X₂` and `Y₁ ∩ Y₂ ⊴ Y₂` -/
def Iso [Group G]  (X Y : Subgroup G × Subgroup G) : Prop :=
  ∃ (_ : (X.1.subgroupOf X.2).Normal) (_ : (Y.1.subgroupOf Y.2).Normal),
  Nonempty <| (_ ⧸ X.1.subgroupOf X.2) ≃* _ ⧸ Y.1.subgroupOf Y.2

theorem iso_symm [Group G] {X Y : Subgroup G × Subgroup G} : Iso X Y → Iso Y X :=
  fun ⟨xN, yN, ⟨f⟩⟩ => ⟨yN, xN, ⟨f.symm⟩⟩

theorem iso_trans [Group G] {X Y Z : Subgroup G × Subgroup G} : Iso X Y → Iso Y Z → Iso X Z :=
  fun ⟨xN, _, ⟨f⟩⟩ ⟨_, zN, ⟨g⟩⟩ => ⟨xN, zN, ⟨f.trans g⟩⟩

-- TODO
-- theorem second_iso [Group G] {X Y : Subgroup G} (hM : IsMaximalNormal X (X ⊔ Y)) :
--     Iso (X, X ⊔ Y) (X ⊓ Y, Y) := by
--   rcases hM with ⟨hcov, hN⟩
--   have hN' : ((X ⊓ Y).subgroupOf ((X ⊔ Y) ⊓ Y)).Normal :=
--     Subgroup.inf_subgroupOf_inf_normal_of_left _ (le_sup_left : X ≤ X ⊔ Y)
--   rw [inf_of_le_right (@le_sup_right _ _ X Y)] at hN'
--   have hiso := QuotientGroup.quotientInfEquivProdNormalQuotient (Y.subgroupOf (X ⊔ Y)) (X.subgroupOf (X ⊔ Y))
--   simp at hiso
--   use hN, hN'
--   constructor
--   dsimp
--   have h1 : _ ⧸ X.subgroupOf (X ⊔ Y) ≃* _ ⧸ (X.subgroupOf (X ⊔ Y)).subgroupOf (Y.subgroupOf (X ⊔ Y) ⊔ X.subgroupOf (X ⊔ Y)) := by sorry

end JordanHolderModule

#check JordanHolderModule.instJordanHolderLattice

namespace Exercises
/- Exercise 3.4.1 -/

end Exercises

end Dnf.C03.S04
