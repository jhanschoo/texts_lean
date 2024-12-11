import TextsLean.Basic

namespace Dnf.C02.S03

/- Definition 2.3.1 **cyclic group**, **Cyclic subgroup** -/
#check IsCyclic
#check IsAddCyclic
-- Note: In Mathlib, the conventional way to state that a subgroup is cyclic is exhibit a zpowers generator, but there exists a predicate IsCommutative to state that a Subgroup is abelian.
#check Subgroup.zpowers
#check AddSubgroup.zmultiples

example [Group α] (x : α) : Subgroup.zpowers x = Subgroup.zpowers x⁻¹ := by sorry
#check Subgroup.zpowers_inv

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
example [Group α] (a : α) : Nat.card (Subgroup.zpowers a) = orderOf a := by sorry
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
