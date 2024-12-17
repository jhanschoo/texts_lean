import TextsLean.Basic

namespace Dnf.C03.S01

/- Example 3.1.1 -/
section
def φ : ℤ →+ ZMod n := ({
  toFun : ℤ → ZMod n := fun a ↦ a,
  map_zero' := by simp only [Int.cast_zero],
  map_add' := by simp only [Int.cast_add, implies_true],
} : AddMonoidHom ℤ (ZMod n))

/-- Example 3.1.1 -/
example (a : ZMod n) : φ ⁻¹' {a} = { m : ℤ | m ≡ a.cast [ZMOD n] } := by
  simp only [Set.preimage, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Set.mem_singleton_iff]
  ext m
  simp only [Set.mem_setOf_eq, ← ZMod.intCast_eq_intCast_iff, ZMod.intCast_cast, ZMod.cast_id', id_eq]
end

/-- Definition 3.1.1 **kernel** -/
example [Group G] [Group H] (φ : G →* H) : φ.ker = { g : G | φ g = 1 } := by
  ext g
  rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
example [AddGroup G] [AddGroup H] (φ : G →+ H) : φ.ker = { g : G | φ g = 0 } := by
  ext g
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_setOf_eq]
#check MonoidHom.ker

/-- Proposition 3.1.(1) -/
example [Group G] [Group H] (φ : G →* H) : φ 1 = 1 := by rw [map_one]
#check MonoidHom.map_one
#check map_one

/-- Proposition 3.1.(2) -/
example [Group G] [Group H] (φ : G →* H) (g : G) : φ g⁻¹ = (φ g)⁻¹ := by rw [map_inv]
#check MonoidHom.map_inv
#check map_inv

/-- Proposition 3.1.(3) -/
example [Group G] [Group H] (φ : G →* H) (g : G) (n : ℕ) : φ (g ^ n) = φ g ^ n := by rw [map_pow]
#check MonoidHom.map_pow

/- Proposition 3.1.(4) -/
example [Group G] [Group H] (φ : G →* H) : ∃ (K : Subgroup G), K = { g : G | φ g = 1 } := by
  use φ.ker
  ext g
  rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
#check fun {G H : Type*} [Group G] [Group H] (φ : G →* H) ↦ φ.ker

/- Proposition 3.1.(5) -/
example [Group G] [Group H] (φ : G →* H) : ∃ (I : Subgroup H), I = φ '' (⊤ : Subgroup G) := by
  use φ.range
  ext h
  rw [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_image, Subgroup.coe_top]
  simp only [Set.mem_univ, true_and]
#check Subgroup.map

/-- Definition 3.1.2 **quotient group** -/
example [Group G] [Group H] (φ : G →* H) (_ : G ⧸ φ.ker) : True := by simp

open scoped Pointwise in
/-- Proposition 3.2.(1) **pointwise multiplication** -/
example [Group G] [Group H] (φ : G →* H) (a : H) (X : Set G) (u : G) (hu : u ∈ X) (hX : X = φ⁻¹' {a}) : u • (φ.ker : Set G) = X := by sorry
open scoped Pointwise in
/-- Proposition 3.2.(2) **pointwise multiplication** -/
example [Group G] [Group H] (φ : G →* H) (a : H) (X : Set G) (u : G) (hu : u ∈ X) (hX : X = φ⁻¹' {a}) : MulOpposite.op u • (φ.ker : Set G) = X := by sorry

open scoped Pointwise in
/-- Definition 3.1.3.(1) **left coset** (note here we say that the notation is generalized to subsets) -/
example [Mul G] (a : G) (S : Set G) : a • S = { e : G | ∃ a s, s ∈ S ∧ e = a * s } := by sorry
open scoped Pointwise in
/-- Definition 3.1.3.(2) **right coset** (note here we say that the notation is generalized to subsets) -/
example [Mul G] (a : G) (S : Set G) : MulOpposite.op a • S = { e : G | ∃ a s, s ∈ S ∧ e = s * a } := by sorry

open scoped Pointwise in
example [Add G] (a : G) (S : Set G) : a +ᵥ S = { e : G | ∃ a s, s ∈ S ∧ e = a + s } := by sorry
open scoped Pointwise in
example [Add G] (a : G) (S : Set G) : AddOpposite.op a +ᵥ S = { e : G | ∃ a s, s ∈ S ∧ e = s + a } := by sorry

open scoped Pointwise in
/-- Definition 3.1.3.(3) **representative** -/
example [Group G] (a : G) (H : Subgroup G) : a ∈ a • (H:Set G) := by sorry
open scoped Pointwise in
example [Group G] (a : G) (H : Subgroup G) : a ∈ MulOpposite.op a • (H : Set G) := by sorry

/- Theorem 3.3 -/
open scoped Pointwise in
example [Group G] (H : Subgroup G) (a b : G) : (a • (H:Set G)) * (b • H) = (a * b) • H := by sorry

-- TODO: examples

/- Proposition 3.4 -/
open scoped Pointwise in
example [Group G] (N : Subgroup G) (hNn : N.Normal) (a b : G) : (a • (N:Set G)) = b • N ↔ b ∈ (a • (N:Set G)) := by sorry

/- Proposition 3.5.1 -/
open scoped Pointwise in
example [Group G] (N : Subgroup G) : (∀ (a b : G), (a • (N:Set G)) * (b • (N:Set G)) = (a * b) • (N:Set G)) ↔ N.Normal := by sorry

/- Proposition 3.5.2 -/
open scoped Pointwise in
example [Group G] (N : Subgroup G) : ∃(_ : Group (G ⧸ N)), True ↔  N.Normal := by sorry
#check QuotientGroup.Quotient.group
#check one_leftCoset

/- Definition 3.1.4 **conjugate** -/
-- These notions of conjugate are not parametrized by the element by which an element and its conjugate are conjugate.
#check IsConj
example [Monoid M] (a b : M) : IsConj a b ↔ IsConj a b := by sorry
example [Group G] (n gngi : G) : IsConj n gngi ↔ ∃ g, g * n * g⁻¹ = gngi := by sorry
#check conjugatesOf
#check Group.conjugatesOfSet
-- This gives a definition of conjugation by an element, as an action of a group, acting on a patient group, to produce conjugates.
#check MulAut.conj
#check ConjAct

open Pointwise in
example [Group G] {N : Subgroup G} : (∀ (g : G), MulAut.conj g • N = N) ↔ N.Normal := by sorry
#check Subgroup.Normal.of_conjugate_fixed

/- Theorem 3.6.(1)-(2) -/
example [Group G] (N : Subgroup G) : N.Normal ↔ N.normalizer = ⊤ := by sorry
/- Theorem 3.6.(1)-(3) -/
open Pointwise in
example [Group G] (N : Subgroup G) : N.Normal ↔ (∀ g : G, g • (N:Set G) = MulOpposite.op g • (N:Set G)) := by sorry
/- Theorem 3.6.(1)-(4) -/
example [Group G] (N : Subgroup G) : N.Normal ↔ ∃(_ : Group (G ⧸ N)), True := by sorry
/- Theorem 3.6.(1)-(5) -/
open Pointwise in
example [Group G] (N : Subgroup G) : N.Normal ↔ (∀ g : G, MulAut.conj g • (N:Set G) ⊆ N) := by sorry

/- Proposition 3.7 -/
example [Group G] (N : Subgroup G) : N.Normal ↔ ∃ (H : Type*) (_ : MulOneClass H) (φ : G →* H), N = φ.ker := by sorry

/- Proposition 3.8 **natural projection** -/
-- Note that even without the condition, π is uniquely determined.
example [Group G] (N : Subgroup G) [N.Normal] : ∃ (π : G →* G⧸N), ∀ (Hbar : Subgroup (G⧸N)), ∃ (H' : Subgroup G), H' = π ⁻¹' (Hbar:Set (G⧸N)) := by sorry

end Dnf.C03.S01
