import TextsLean.Basic

namespace Dnf.C03.S02

/- Theorem 3.8 -/
example [Group G] (H : Subgroup G) : Nat.card H ∣ Nat.card G := by sorry
open Pointwise in
example [Group G] (H : Subgroup G) : Nat.card G = Nat.card H * Nat.card (G ⧸ H) := by sorry
#check Subgroup.index_mul_card

/- Definition 3.2.1 -/
#check Subgroup.index
#check Subgroup.card_eq_card_quotient_mul_card_subgroup
#check Subgroup.card_subgroup_dvd_card

/- Corollary 3.9 -/
#check orderOf_dvd_card

/- Corollary 3.10 -/
#check isCyclic_of_prime_card
#check zmodAddCyclicAddEquiv
#check zmodCyclicMulEquiv

/- Example 3.1.1 -/
-- TODO

--TODO counterexample to converse of Lagrange's Theorem
-- TODO converse for abelian groups

/- Corollary 3.11 -/
#check exists_prime_orderOf_dvd_card
#check exists_prime_addOrderOf_dvd_card

/- Theorem 3.12 Sylow -/
#check Sylow.exists_subgroup_card_pow_prime

-- TODO
/- Proposition 3.13 -/
open Pointwise in
example [Group G] (H K : Subgroup G) : (Nat.card ((H:Set G) * (K:Set G))) * Nat.card (H ⊓ K : Subgroup G) = Nat.card H * Nat.card K := by sorry

/- Proposition 3.14 -/
open Pointwise in
example [Group G] (H K : Subgroup G) : (H:Set G) * K = H ⊔ K ↔ (H:Set G) * K = K * H := by sorry

/- Corollary 3.15 -/
open Pointwise in
example [Group G] (H K : Subgroup G) (hH : H ≤ K.normalizer) : (H:Set G) * K = H ⊔ K := by sorry
open Pointwise in
example [Group G] (H K : Subgroup G) [K.Normal] : (H:Set G) * K = H ⊔ K := by sorry

/- Definition 3.2.2 **normalizes** **centralizes** -/
def normalizes [Group G] (A : Set G) (K : Subgroup G) := A ⊆ K.normalizer
def centralizes [Group G] (A : Set G) (K : Subgroup G) := A ⊆ Set.centralizer K

end Dnf.C03.S02
