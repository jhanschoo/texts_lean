import TextsLean.Basic

namespace Dnf.C02.S02

/-- Definition 2.2.1 **centralizer** -/
example [Group G] (A : Set G) : Subgroup.centralizer A = { g : G | ∀ a ∈ A, g * a * g⁻¹ = a } := by
  simp only [Subgroup.centralizer, Set.centralizer, Subgroup.coe_set_mk]
  conv_rhs =>
    ext x
    lhs
    ext g a ha
    rw [← @mul_right_cancel_iff _ _ _ g _ _, eq_comm]
    simp
#check Subgroup.centralizer

/- Definition 2.2.2 **center** -/
example [Group G] : Subgroup.center G = { g : G | ∀ a, a * g = g * a } := by
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_setOf_eq]
#check Subgroup.center

/-- Definition 2.2.3 **normalizer** -/
example [Group G] (A : Subgroup G) : Subgroup.normalizer A = { g : G | {gaginv : G | ∃ a ∈ A, gaginv = g * a * g⁻¹ } = A } := by
  ext x
  simp [SetLike.mem_coe, Subgroup.mem_normalizer_iff, Set.mem_setOf_eq]
  constructor
  · intro H
    ext h
    simp
    constructor
    · intro ⟨h', hh'1, hh'2⟩
      subst hh'2
      rwa [H h'] at hh'1
    · sorry
  · sorry
#check Subgroup.normalizer
#check Subgroup.setNormalizer

example [Group G] (A : Set G) : Subgroup.centralizer A ≤ Subgroup.setNormalizer A := by
  simp [Subgroup.centralizer, Subgroup.setNormalizer, Set.centralizer]
  intro g hcA h
  constructor
  · intro hmem
    have hh := hcA h hmem
    rw [← hh]
    simp [hmem]
  · intro hghmem
    have hgh := hcA (g * h * g⁻¹) hghmem
    simp at hgh
    rwa [hgh]

/- Example 2.2.1 TODO  -/

/- Definition 2.2.4 **stabilizer** -/
example [Group G] [MulAction G α] (a : α) : MulAction.stabilizer G a = { g : G | g • a = a } := by
  ext x
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_setOf_eq]
#check MulAction.stabilizer
#check AddAction.stabilizer

-- TODO proof that the kernel of an action is a subgroup

/- Example 2.2.2 TODO -/

-- TODO
#check Subgroup.centralizer_eq_comap_stabilizer

namespace Exercises
/-- Exercise 2.2.1 -/
example [Group G] (A : Set G) : Subgroup.centralizer A = { g : G | ∀ a ∈ A, g⁻¹ * a * g = a } := by
  simp only [Subgroup.centralizer, Set.centralizer, Subgroup.coe_set_mk]
  conv_rhs =>
    ext x
    lhs
    ext g a ha
    rw [← @mul_left_cancel_iff _ _ _ g _ _, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Exercise 2.2.2 -/
example [Group G] : Subgroup.centralizer (Subgroup.center G : Set G) = (⊤ : Subgroup G) := by sorry
example [Group G] : (Subgroup.center G).normalizer = (⊤ : Subgroup G) := by sorry

/-- Exercise 2.2.3 -/
example [Group G] (A B : Set G) (hAB : A ⊆ B) : Subgroup.centralizer B ≤ Subgroup.centralizer A := by sorry

/-- Exercise 2.2.4 TODO -/
example [Group G] (A B : Set G) (hAB : A ⊆ B) : Subgroup.centralizer B ≤ Subgroup.centralizer A := by sorry

/-- Exercise 2.2.5.(a) -/
example : Subgroup.centralizer ({1, c[0, 1, 2], c[0, 2, 1]} : Set (Equiv.Perm (Fin 3))) = ({1, c[0, 1, 2], c[0, 2, 1]} : Set (Equiv.Perm (Fin 3))) := by sorry
example : Subgroup.setNormalizer ({1, c[0, 1, 2], c[0, 2, 1]} : Set (Equiv.Perm (Fin 3))) = (⊤ : Subgroup (Equiv.Perm (Fin 3))) := by sorry

open DihedralGroup in
/-- Exercise 2.2.5.(b) -/
example : Subgroup.centralizer ({ g | g = 1 ∨ g = sr 0 ∨ g = r 2 ∨ g = sr 2} : Set (DihedralGroup 4)) = ({ g | g = 1 ∨ g = sr 0 ∨ g = r 2 ∨ g = sr 2} : Set (DihedralGroup 4)) := by sorry
open DihedralGroup in
example : Subgroup.setNormalizer ({ g | g = 1 ∨ g = sr 0 ∨ g = r 2 ∨ g = sr 2} : Set (DihedralGroup 4)) = (⊤ : Subgroup (DihedralGroup 4)) := by sorry

open DihedralGroup in
/-- Exercise 2.2.5.(c) -/
example : Subgroup.centralizer (Subgroup.zpowers (r 1) : Subgroup (DihedralGroup 10)) = (Subgroup.zpowers (r 1) : Subgroup (DihedralGroup 10)) := by sorry
open DihedralGroup in
example : (Subgroup.zpowers (r 1) : Subgroup (DihedralGroup 10)).normalizer = (⊤ : Subgroup (DihedralGroup 10)) := by sorry

/-- Exercise 2.2.6.(a) -/
example [Group G] (H : Subgroup G) : H ≤ H.normalizer := by sorry
/- Exercise 2.2.6.(b) -/
example [Group G] (H : Subgroup G) : H ≤ (H:Set G).centralizer ↔ H.IsCommutative := by sorry

open DihedralGroup in
/-- Exercise 2.2.7.(a) -/
example (n : ℕ) (hn : 3 ≤ n) (hnodd : Odd n) (H : Subgroup (DihedralGroup n)) : Subgroup.center (DihedralGroup n) = ⊥ := by sorry
open DihedralGroup in
/-- Exercise 2.2.7.(b) -/
example (k : ℕ) (hn : 3 ≤ 2 * k) (H : Subgroup (DihedralGroup (2 * k))) : Subgroup.center (DihedralGroup (2 * k)) = ({ g | g = 1 ∨ g = r k} : Set (DihedralGroup (2 * k))) := by sorry

/-- Exercise 2.2.8 -/
-- Note: use group actions
example (n : ℕ) (i : Fin n) : ∃ (Gi : Subgroup (Equiv.Perm (Fin n))), Gi = { g : Equiv.Perm (Fin n) | g i = i } := by sorry
example (n : ℕ) (i : Fin n) : MulAction.stabilizer (Equiv.Perm (Fin n)) i = { g : Equiv.Perm (Fin n) | g i = i } := by sorry
example (n : ℕ) (i : Fin n) : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin n)) i) = (n - 1).factorial := by sorry

open Pointwise in
/-- Exercise 2.2.9 -/
example [Group G] (H : Subgroup G) (A : Set G) [hAne : Nonempty A] : Subgroup.setNormalizer A ⊓ H = { h : G | h ∈ H ∧ A = ({h} : Set G) * A * {h⁻¹} } := by sorry

/-- Exercise 2.2.10 -/
example [Group G] (H : Subgroup G) (hHcard : Nat.card H = 2) : H.normalizer = Subgroup.centralizer (H : Set G) := by sorry
example [Group G] (H : Subgroup G) (hHcard : Nat.card H = 2) (hNorm : H.normalizer = ⊤) : H ≤ Subgroup.center G := by sorry

/-- Exercise 2.2.11 -/
example [Group G] (A : Set G) : Subgroup.center G ≤ Subgroup.centralizer A := by sorry

/- Exercise 2.2.12 -/
section
open MvPolynomial

noncomputable instance sm : SMul (Equiv.Perm (Fin 4)) (MvPolynomial (Fin 4) ℤ) := ⟨λ σ p => p.rename σ⟩

/-- Exercise 2.2.12.(b) -/
noncomputable instance : MulAction (Equiv.Perm (Fin 4)) (MvPolynomial (Fin 4) ℤ) := by
  have rename_one (p : MvPolynomial (Fin 4) ℤ) : rename (1 : Equiv.Perm (Fin 4)) p = p := by
    simp only [Equiv.Perm.coe_one, rename_id, AlgHom.coe_id, id_eq]

  have mul_smul (σ τ : Equiv.Perm (Fin 4)) (p : MvPolynomial (Fin 4) ℤ) : rename (σ * τ) p = rename σ (rename τ p) := by simp only [Equiv.Perm.coe_mul, rename_rename]
  exact {
    one_smul := rename_one,
    mul_smul := mul_smul,
  }

/- Exercise 2.2.12.(a) -/
section
abbrev MP4Z := MvPolynomial (Fin 4) ℤ
abbrev S4 := Equiv.Perm (Fin 4)
noncomputable def p : MP4Z :=
    C 12 * X 1 ^ 5 * X 2 ^ 7           * X 4
  - C 18           * X 2 ^ 3 * X 3
  + C 11 * X 1 ^ 6 * X 2     * X 3 ^ 3 * X 4 ^ 23
def σ : Equiv.Perm (Fin 4) := c[1, 2, 3, 4]
def τ : Equiv.Perm (Fin 4) := c[1, 2, 3]
example : σ • p = (
    C 12 * X 2 ^ 5 * X 3 ^ 7           * X 1
  - C 18           * X 3 ^ 3 * X 4
  + C 11 * X 2 ^ 6 * X 3     * X 4 ^ 3 * X 1 ^ 23) := by
    unfold HSMul.hSMul instHSMul SMul.smul sm
    simp only [σ, Fin.isValue, Cycle.formPerm_coe, p, map_add, map_sub, map_mul, map_pow, MvPolynomial.rename_X, MvPolynomial.rename_C]
    congr
example : τ • σ • p = sorry := by sorry
example : (τ * σ) • p = sorry := by sorry
example : (σ * τ) • p = sorry := by sorry
end

/-- Exercise 2.2.12.(c) -/
example : MulAction.stabilizer S4 (X 4 : MP4Z) ≃* Equiv.Perm (Fin 3) := by sorry

/-- Exercise 2.2.12.(d) -/
example (H : Subgroup S4) (hH : H = MulAction.stabilizer S4 (X 1 + X 2 : MP4Z)) : H.IsCommutative ∧ Nat.card H = 4 := by sorry

/-- Exercise 2.2.12.(e) -/
example : MulAction.stabilizer S4 (X 1 * X 2 + X 3 * X 4 : MP4Z) ≃* DihedralGroup 4 := by sorry

/-- Exercise 2.2.12.(f) -/
example : MulAction.stabilizer S4 (X 1 + X 2 : MP4Z) = MulAction.stabilizer S4 ((X 1 + X 2) * (X 3 + X 4) : MP4Z) := by sorry
end

/- Exercise 2.2.13 -/
section
open MvPolynomial

noncomputable instance smn (n : ℕ) : SMul (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) ℤ) := ⟨λ σ p => p.rename σ⟩

noncomputable instance (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) ℤ) := by
  have rename_one (p : MvPolynomial (Fin n) ℤ) : rename (1 : Equiv.Perm (Fin n)) p = p := by
    simp only [Equiv.Perm.coe_one, rename_id, AlgHom.coe_id, id_eq]
  have mul_smul (σ τ : Equiv.Perm (Fin n)) (p : MvPolynomial (Fin n) ℤ) : rename (σ * τ) p = rename σ (rename τ p) := by simp only [Equiv.Perm.coe_mul, rename_rename]
  exact {
    one_smul := rename_one,
    mul_smul := mul_smul,
  }
end

/- Exercise 2.2.14 TODO -/

-- TODO
end Exercises

end Dnf.C02.S02
