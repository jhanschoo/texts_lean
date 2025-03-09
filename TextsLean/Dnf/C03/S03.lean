import TextsLean.Basic

namespace Dnf.C03.S03

/- Theorem 3.16 **first isomorphism theorem** -/
example [Group G] [Group H] (φ : G →* H) : φ.ker.Normal := by sorry
example [Group G] [Group H] (φ : G →* H) : G ⧸ φ.ker ≃* (⊤ : Subgroup G).map φ := by sorry
#check QuotientGroup.quotientKerEquivRange
#check QuotientAddGroup.quotientKerEquivRange

/- Corollary 3.17.(1) -/
example [Group G] [Group H] (φ : G →* H) : Function.Injective φ ↔ φ.ker = ⊥ := by sorry
#check injective_iff_map_eq_zero
#check injective_iff_map_eq_zero'
#check injective_iff_map_eq_one
#check injective_iff_map_eq_one'
/- Corollary 3.17.(2) -/
example [Group G] [Group H] (φ : G →* H) : φ.ker.index = Nat.card ((⊤ : Subgroup G).map φ) := by sorry
#check Subgroup.index_ker
#check Subgroup.relindex_ker
#check AddSubgroup.index_ker
#check AddSubgroup.relindex_ker

/- Theorem 3.18 **second isomorphism theorem**

  Let (A ≤ B.normalizer), where A and B are subgroups of G. Then

  - AB is a subgroup of G,
  - B is normal in AB
  - A ⊓ B is normal in A
  - AB ⧸ B ≃* A ⧸ (A ⊓ B)

  The isomorphism `f` is given by identifying
  $a(A ⊓ B) ↔ aB$ for each $a ∈ A$.

  In Lean, there is no API for the notion of being normal in respect
  to some `Subgroup _`. We need to convert the result into a statement
  about being normal, when considered as a Subgroup of the normalizer
  considered as a type itself. Hence

  Let (A ≤ B.normalizer). Then
  - AB = (A ⊔ B) when considered as sets of group elements
  - B is normal when considered as a subgroup of A ⊔ B
  - A ⊓ B is normal when considered as a subgroup of B
  - A ⊔ B ⧸ (B.subgroupOf (A ⊔ B)) ≃* A ⧸ B.subgroupOf A
-/
theorem theorem_3_18_aux_1 [Group G] (A B : Subgroup G) (hLE : A ≤ B.normalizer) : (B.subgroupOf A).Normal := by sorry
theorem theorem_3_18_aux_2 [Group G] (A B : Subgroup G) (hLE : A ≤ B.normalizer) : (B.subgroupOf (A ⊔ B)).Normal := by sorry

open Pointwise in
theorem mul_normalizer [Group G] (N H : Subgroup G) (hLE : N ≤ H.normalizer) : (↑(N ⊔ H) : Set G) = N * H := by sorry

open Pointwise in
example [Group G] (A B : Subgroup G) (hLE : A ≤ B.normalizer) :
  (A:Set G) * (B:Set G) = A ⊔ B ∧
  A ⊔ B ≤ B.normalizer ∧
  (B.subgroupOf A).Normal ∧
  (B.subgroupOf (A ⊔ B)).Normal := by sorry

example [Group G] (A B : Subgroup G) (hLE : A ≤ B.normalizer)
  (_ : (B.subgroupOf A).Normal := theorem_3_18_aux_1 A B hLE)
  (_ : (B.subgroupOf (A ⊔ B)).Normal := theorem_3_18_aux_2 A B hLE) :
  (_ ⧸ (B.subgroupOf (A ⊔ B)) ≃* _ ⧸ B.subgroupOf A) := by sorry
#check Subgroup.normal_in_normalizer
#check Subgroup.subgroupOf
-- #check QuotientGroup.quotientInfEquivProdNormalizerQuotient
#check QuotientGroup.quotientInfEquivProdNormalQuotient
#check QuotientAddGroup.quotientInfEquivSumNormalQuotient

/- Theorem 3.19 **third isomorphism theorem**
  If (H K : Subroup G) are normal with H ≤ K, then K ⧸ H is a normal subgroup of G ⧸ H such that (G ⧸ H) ⧸ (K ⧸ H) ≃* G ⧸ K.
-/
example [Group G] (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ≤ K) :
  (K.map (QuotientGroup.mk' H)).Normal := by sorry
example [Group G] (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ≤ K) :
  _ ⧸ K.map (QuotientGroup.mk' H) ≃* _ ⧸ K := by sorry
#check QuotientGroup.quotientQuotientEquivQuotient
#check QuotientAddGroup.quotientQuotientEquivQuotient

/- Theorem 3.20 The Isomorphism Theorem -/
example [Group G] (N : Subgroup G) [N.Normal] :
  ∃ f : Subgroup G → Subgroup (G ⧸ N),
  Set.InjOn f { A : Subgroup G | N ≤ A } ∧
  Set.SurjOn f { A : Subgroup G | N ≤ A } ⊤ ∧
  ∀ A ∈ { A : Subgroup G | N ≤ A }, ∀ B ∈ { A : Subgroup G | N ≤ A },
  (A ≤ B ↔ f A ≤ f B) ∧
  (A ≤ B → (A.subgroupOf B).index = ((f A).subgroupOf (f B)).index) ∧
  f (A ⊔ B) = (f A) ⊔ (f B) ∧
  f (A ⊓ B) = (f A) ⊓ (f B) ∧
  (A.Normal ↔ (f A).Normal) := by
    use Subgroup.map (QuotientGroup.mk' N)
    sorry
#check QuotientGroup.comapMk'OrderIso

/- Example 3.3.1 -/

/- Example 3.3.2 -/

namespace Exercises
/- Exercise 3.3.1 -/
/- Exercise 3.3.2 -/
/- Exercise 3.3.3 -/
/- Exercise 3.3.4 -/
/- Exercise 3.3.5 -/

end Exercises

end Dnf.C03.S03
