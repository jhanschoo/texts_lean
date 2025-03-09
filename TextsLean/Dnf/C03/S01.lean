import TextsLean.Basic

namespace Dnf.C03.S01

section
/-- Example 3.1.1 -/
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

/-- Proposition 3.1.(4) -/
example [Group G] [Group H] (φ : G →* H) : ∃ (K : Subgroup G), K = φ.ker := by
  use φ.ker
#check fun {G H : Type*} [Group G] [Group H] (φ : G →* H) ↦ φ.ker

/-- Proposition 3.1.(5) -/
example [Group G] [Group H] (φ : G →* H) : ∃ (I : Subgroup H), I = φ '' (⊤ : Subgroup G) := by
  use φ.range
  ext h
  rw [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_image, Subgroup.coe_top]
  simp only [Set.mem_univ, true_and]
#check Subgroup.map

-- Note that the book uses a different definition of quotient group. We show that they are equivalent.
/-- Definition 3.1.2 **quotient group**

  Let $φ : G →* H$ have kernel $K$. The **quotient group**, or **factor group**, $G ⧸ K$ is the group whose elements are the fibers of $φ$ and whose binary operation is characterized as follows: the product of the fibers above $a b : G$ is the fiber above $ab : G$.
-/
example [Group G] [Group H] (φ : G →* H) : Group (G ⧸ φ.ker) := by infer_instance
example [Group G] [Group H] (φ : G →* H) (a b : G) : (a : G ⧸ φ.ker) * (b : G ⧸ φ.ker) = (a * b : G) := by rfl
-- Mathlib defines quotients in terms of equivalence classes, so we cannot definitionally say that the elements of `G ⧸ φ.ker` are related to the fibers of `φ`. But we do not need something so heavyweight as to draw an isomorphism either.
example [Group G] [Group H] (φ : G →* H) (a b : G) : (a : G ⧸ φ.ker) = (b : G ⧸ φ.ker) ↔ φ ⁻¹' {φ a} = φ ⁻¹' {φ b} := by sorry
example [Group G] [Group H] (φ : G →* H) : (∃ (i : Group (G ⧸ φ.ker)), i = (QuotientGroup.con (φ.ker)).group) ∧ ∀ p ∈ (QuotientGroup.con (φ.ker)).classes, ∃ h, p = φ ⁻¹' h := by
  simp [Setoid.classes]
  intro g
  use {φ g}
  ext g'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  simp [QuotientGroup.con, QuotientGroup.leftRel, MulAction.orbitRel, MulAction.orbit]
  constructor
  · intro ⟨n, hn1, hn2⟩
    simpa [hn2.symm]
  · intro heq
    use (g⁻¹ * g')
    simp [heq]

/-- Proposition 3.2 -/
example [Group G] [Group H] (φ : G →* H) (a : H) (u : G) (hu : u ∈ φ⁻¹' {a}) : φ⁻¹' {a} = { x : G | ∃ k ∈ φ.ker, x = u * k } ∧ φ⁻¹' {a} = { x : G | ∃ k ∈ φ.ker, x = k * u } := by sorry

open scoped Pointwise in
/-- Definition 3.1.3.(1) **left coset** (note here we say that the notation is generalized to subsets) -/
example [Mul G] (a : G) (S : Set G) : a • S = { e : G | ∃ s ∈ S, e = a * s } := by sorry
open scoped Pointwise in
/-- Definition 3.1.3.(2) **right coset** (note here we say that the notation is generalized to subsets) -/
example [Mul G] (a : G) (S : Set G) : MulOpposite.op a • S = { e : G | ∃ s ∈ S, e = s * a } := by sorry

open scoped Pointwise in
example [Add G] (a : G) (S : Set G) : a +ᵥ S = { e : G | ∃ s ∈ S, e = a + s } := by sorry
open scoped Pointwise in
example [Add G] (a : G) (S : Set G) : AddOpposite.op a +ᵥ S = { e : G | ∃ s ∈ S, e = s + a } := by sorry

open scoped Pointwise in
/-- Definition 3.1.3.(3) **representative** -/
example [Group G] (a : G) (H : Subgroup G) : a ∈ a • (H:Set G) := by sorry
open scoped Pointwise in
example [Group G] (a : G) (H : Subgroup G) : a ∈ MulOpposite.op a • (H : Set G) := by sorry

open scoped Pointwise in
/-- Theorem 3.3 -/
example [Group G] [Group H] (φ : G →* H) (a b : G) : (a • (φ.ker:Set G)) * (b • (φ.ker:Set G)) = (a * b) • φ.ker := by sorry
open scoped Pointwise in
example [Group G] [Group H] (φ : G →* H) (a b : G) : (a : G ⧸ φ.ker) * (b : G ⧸ φ.ker) = (a * b : G) := by sorry

open scoped Pointwise in
/-- Proposition 3.4 -/
example [Group G] (N : Subgroup G) [hNn : N.Normal] : ∃ (hs : Setoid G), s ∈ hs.classes ↔ ∃ (a : G), s = (a • (N : Set G) : Set G) := by sorry
open scoped Pointwise in
example [Group G] (N : Subgroup G) [hNn : N.Normal] (a b : G) : (a • (N:Set G)) = b • N ↔ b⁻¹ * a ∈ (N:Set G) := by sorry
open scoped Pointwise in
example [Group G] (N : Subgroup G) [hNn : N.Normal] (a b : G) : (a • (N:Set G)) = b • N ↔ b ∈ a • (N:Set G) := by sorry

open scoped Pointwise in
/-- Proposition 3.5.1 -/
example [Group G] (N : Subgroup G) : (∀ (a b : G), (a • (N:Set G)) * (b • (N:Set G)) = (a * b) • (N:Set G)) ↔ N.Normal := by sorry

open scoped Pointwise in
/-- Proposition 3.5.2 -/
example [Group G] (N : Subgroup G) : ∃(_ : Group (G ⧸ N)), True ↔  N.Normal := by sorry
#check QuotientGroup.Quotient.group
#check one_leftCoset

/- Definition 3.1.4 **conjugate** -/
example [Group G] (g n : G) : MulAut.conj g n = g * n * g⁻¹ := by simp only [MulAut.conj_apply]
#check MulAut.conj
#check AddAut.conj
example [Group G] (g : G) (n : G) : ConjAct.toConjAct g • n = g * n * g⁻¹ := ConjAct.toConjAct_smul _ _
#check ConjAct
-- These notions of conjugate are not parametrized by the element by which an element and its conjugate are conjugate.
#check IsConj
example [Monoid M] (a b : M) : IsConj a b ↔ IsConj b a := by sorry
example [Group G] (n gngi : G) : IsConj n gngi ↔ ∃ g, g * n * g⁻¹ = gngi := by sorry
#check conjugatesOf
#check Group.conjugatesOfSet
-- This gives a definition of conjugation by an element, as an action of a group, acting on a patient group, to produce conjugates.

open Pointwise in
example [Group G] {N : Subgroup G} : (∀ (g : G), MulAut.conj g • N = N) ↔ N.Normal := ⟨Subgroup.Normal.of_conjugate_fixed, (fun h g ↦ @Subgroup.smul_normal _ _ g _ h)⟩
#check Subgroup.Normal.of_conjugate_fixed
#check Subgroup.smul_normal

/-- Theorem 3.6.(1)-(2) -/
example [Group G] (N : Subgroup G) : N.Normal ↔ N.normalizer = ⊤ := by sorry

open Pointwise in
/-- Theorem 3.6.(1)-(3) -/
example [Group G] (N : Subgroup G) : N.Normal ↔ (∀ g : G, g • (N:Set G) = MulOpposite.op g • (N:Set G)) := by sorry
/-- Theorem 3.6.(1)-(4) -/
example [Group G] (N : Subgroup G) : N.Normal ↔ ∃(_ : Group (G ⧸ N)), True := by sorry
open Pointwise in
/-- Theorem 3.6.(1)-(5) -/
example [Group G] (N : Subgroup G) : N.Normal ↔ (∀ g : G, MulAut.conj g • (N:Set G) ⊆ N) := by sorry

/-- Proposition 3.7 -/
example [Group G] (N : Subgroup G) : N.Normal ↔ ∃ (H : Type*) (_ : MulOneClass H) (φ : G →* H), N = φ.ker := by sorry

open scoped Pointwise in
/-- Definition 3.8 **natural projection**

  Let $N ⊴ G$. Then there exists a **natural projection** $π  G →* G ⧸ N$
  such that $π(g) = gN$. Suppose $H'≤ G⧸N$. Then the **complete preimage** of $H'$ in $G$ is $π⁻¹\[H'\]$, and itself a subgroup of $G$.
-/
example [Group G] (N : Subgroup G) [N.Normal] :
  (∀ (g : G), (QuotientGroup.mk' N) g = (g : G ⧸ N)) ∧
  ∀ (Hbar : Subgroup (G⧸N)), ∃ (H' : Subgroup G),
    H' = (QuotientGroup.mk' N) ⁻¹' (Hbar : Set (G⧸N)) := by sorry
#check QuotientGroup.mk'
#check QuotientAddGroup.mk'

example [Group G] (N : Subgroup G) : N.Normal ↔ N.normalizer = ⊤ := by sorry
#check Subgroup.normalizer_eq_top_iff

/- ## Exercises -/
section Exercises

section
variable [Group G] [Group H] (φ : G →* H)

/- Exercise 3.1.1 -/
example (E : Subgroup H) : ∃ (E' : Subgroup G), φ ⁻¹' E = E' := by sorry
example (E : Subgroup H) : (E.comap φ) ≤ ⊤ := by sorry
example (E : Subgroup H) [E.Normal] : (E.comap φ).Normal := by sorry
#check Subgroup.comap

/- Exercise 3.1.2 -/
example (u w : G) (X Y Z : G ⧸ φ.ker)
    (hu1 : X = u)
    (hw : Z = w)
    (hXYZ : Z = X * Y) :
    ∃ v : G, v = Y ∧ u * v = w := by
  have hint : (u⁻¹ * w : G) = Y := by sorry
  sorry

/- Exercise 3.1.3 -/
example [CommGroup A] (B : Subgroup A) : CommGroup (A ⧸ B) := by sorry
example : ∃ (G : Type*) (_ : Group G) (N : Subgroup G),
  (CommGroup G → False) ∧
  N ≠ ⊤ ∧ ∃ (_ : N.Normal) (_ : CommGroup (G ⧸ N)), True := by sorry

/- Exercise 3.1.4 -/
example (N : Subgroup G) [N.Normal] (g : G) (a : ℤ) :
    (g : G ⧸ N) ^ a = (g ^ a : G) := by sorry

/- Exercise 3.1.5 -/
example (N : Subgroup G) [N.Normal] (g : G) (n : ℕ)
  (hn : IsLeast { n | n > 0 ∧ (g ^ n : G) = (1 : G ⧸ N) } n) :
    orderOf (g : G ⧸ N) = n := by sorry

/- TODO -/

end

end Exercises

end Dnf.C03.S01
