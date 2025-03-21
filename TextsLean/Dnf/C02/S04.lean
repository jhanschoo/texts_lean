import TextsLean.Basic

namespace Dnf.C02.S04

/-- Proposition 2.8 -/
example [Group G] (A : Set (Subgroup G)) : ∃ (Hi : Subgroup G), (Hi : Set G) = ⋂ H ∈ A, H := sorry

/-- Definition 2.4.1 **subgroup generated by a subset** -/
example [Group G] (S : Set G) : Subgroup.closure S = sInf { K : Subgroup G | S ⊆ K } := sorry

/-- Proposition 2.9 -/
example [Group G] (S : Set G) : Subgroup.closure S = { g : G | ∃ (l : List G), { g' | g' ∈ l } ⊆ S ∧ g = List.prod l } := sorry

namespace Exercises
end Exercises

end Dnf.C02.S04
