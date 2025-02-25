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

open DihedralGroup in
/-- Example 2.3.1.1 -/
example (n : ℕ) : Nat.card (Subgroup.zpowers (r 1 : DihedralGroup n)) = n := by sorry
--TODO: show that Dn itself is not cyclic due to it not being abelian

/-- Example 2.3.1.2 -/
example : AddSubgroup.zmultiples (1 : ℤ) = ⊤ := by sorry
example : Nat.card (AddSubgroup.zmultiples (1 : ℤ)) = 0 := by sorry
example : ¬IsOfFinAddOrder (1 : ℤ) := by sorry
example : AddSubgroup.zmultiples (-1 : ℤ) = ⊤ := by sorry

/- Proposition 2.2 -/
-- Note that by convention, 0 is used exactly to denote infinite order and cardinality here.
example [Group G] (a : G) : Nat.card (Subgroup.zpowers a) = orderOf a := by sorry
#check Nat.card_zpowers

/-- Proposition 2.3 -/
example [Group G] (x : G) (m n : ℤ) (hm : x ^ m = 1) (hn : x ^ n = 1) : x ^ gcd m n = 1 := sorry
example [Group G] (x : G) (m : ℤ) (hm : x ^ m = 1) :  (orderOf x : ℤ) ∣ m := sorry

/-- Theorem 2.4.(1) -/
example [Group G] [Group H] [IsCyclic G] [IsCyclic H] (hcard : Nat.card G = Nat.card H) : G ≃* H := sorry
-- Note that this statement is more general than what's in the book, which only considers the case where G and H are finite.
/-- Theorem 2.4.(2) -/
example [Group G] [IsCyclic G] [Infinite G] : ℤ ≃* G := sorry

/-- Proposition 2.5.(1) -/
example [Group G] (x : G) (a : ℤ) (hazero : a ≠ 0) (hx : orderOf x = 0) : orderOf (x ^ a) = 0 := sorry
/-- Proposition 2.5.(2) -/
example [Group G] (x : G) (a : ℤ) (hazero : a ≠ 0) (hx : orderOf x = 0) (n : ℕ) (hnzero : n ≠ 0) : orderOf x * gcd a n = n := sorry
/-- Proposition 2.5.(3) -/
example [Group G] (x : G) (a n : ℕ) (hazero : a ≠ 0) (hnzero : n ≠ 0) (han : a ∣ n) : orderOf x * a = n := sorry

/-- Proposition 2.6.(1)&(2) -/
example [Group G] (x : G) (a : ℤ) : Subgroup.zpowers x = Subgroup.zpowers (x ^ a) ↔ IsCoprime (orderOf x:ℤ) a := sorry
/-- Proposition 2.6.(2).1 -/
example [Group G] (x : G) : { x' : G | ∃ a, x' = x ^ a ∧ Subgroup.zpowers x = Subgroup.zpowers (x ^ a) }.ncard = Nat.totient (orderOf x) := sorry

/-- Example 2.3.2 -/
example (n : ℕ) (a : ZMod n) : AddSubgroup.zmultiples a = ⊤ ↔ Nat.Coprime n a.val := sorry

/-- Proposition 2.7.(1) -/
example [Group G] (x : G) (H : Subgroup G) (hHle : H ≤ Subgroup.zpowers x) : ∃ a : ℤ, a ≥ 0 ∧ H = Subgroup.zpowers (x ^ a) := sorry
/-- Proposition 2.7.(2) -/
example [Group G] (x : G) (hx : orderOf x = 0) (a b : ℤ) : Subgroup.zpowers (x ^ a) = Subgroup.zpowers (x ^ b) ↔ a = b ∨ a = -b := sorry
/-- Proposition 2.7.(3).1 -/
example [Group G] (x : G) (a : ℕ) (ha : a ∣ orderOf x) : Subgroup.zpowers (x ^ (orderOf x / a)) ≤ Subgroup.zpowers x ∧ Nat.card (Subgroup.zpowers (x ^ (orderOf x / a))) = a := sorry
/-- Proposition 2.7.(3).2 -/
example [Group G] (x : G) (a : ℤ) : Subgroup.zpowers (x ^ a) = Subgroup.zpowers (x ^ gcd a (orderOf x)) := sorry

/- Example 2.3.3.1 TODO -/
/- Example 2.3.3.2 TODO -/

namespace Exercises
end Exercises

end Dnf.C02.S03
