import TextsLean.Basic

namespace Dnf.C02.S03

/- Definition 2.3.1 **cyclic group**, **Cyclic subgroup** -/
example [Group G] : IsCyclic G ↔ ∃ g : G, Function.Surjective (g ^ · : ℤ → G) := by
  constructor <;> intro h
  · apply exists_zpow_surjective
  · exact { exists_zpow_surjective := h }
#check IsCyclic
#check IsAddCyclic

-- Note: In Mathlib, the conventional way to state that a subgroup is cyclic is exhibit a zpowers generator, but there exists a predicate IsCommutative to state that a Subgroup is abelian.
#check Subgroup.zpowers
#check AddSubgroup.zmultiples

example [Group G] (x : G) : Subgroup.zpowers x = Subgroup.zpowers x⁻¹ :=
  eq_of_forall_ge_iff fun _ ↦ by simp only [Subgroup.zpowers_le, inv_mem_iff]
#check Subgroup.zpowers_inv

example [hG : Group G] [IsCyclic G] : CommGroup G := {
  hG with
  mul_comm := fun x y ↦
      let ⟨_, hg⟩ := IsCyclic.exists_generator (α := G)
      let ⟨_, hn⟩ := hg x
      let ⟨_, hm⟩ := hg y
      hm ▸ hn ▸ zpow_mul_comm _ _ _
}
#check IsCyclic.commGroup
#check IsAddCyclic.addCommGroup

#check Subgroup.zpowers_isCommutative
#check AddSubgroup.zmultiples_isCommutative

/- Example 2.3.1.1 -/
open DihedralGroup in
example (n : ℕ) : Nat.card (Subgroup.zpowers (r 1 : DihedralGroup n)) = n := by sorry
--TODO: show that Dn itself is not cyclic due to it not being abelian

/- Example 2.3.1.2 -/
example : AddSubgroup.zmultiples (1 : ℤ) = ⊤ := by sorry
example : Nat.card (AddSubgroup.zmultiples (1 : ℤ)) = 0 := by sorry
example : ¬IsOfFinAddOrder (1 : ℤ) := by sorry
example : AddSubgroup.zmultiples (-1 : ℤ) = ⊤ := by sorry

/- Proposition 2.2 -/
-- Note that by convention, 0 is used exactly to denote infinite order and cardinality here.
example [Group G] (a : G) : Nat.card (Subgroup.zpowers a) = orderOf a := by sorry
#check Nat.card_zpowers

/- Proposition 2.3 -/
-- TODO

/- Theorem 2.4 -/
-- TODO

/- Proposition 2.5 -/
-- TODO

namespace Exercises
end Exercises

end Dnf.C02.S03
