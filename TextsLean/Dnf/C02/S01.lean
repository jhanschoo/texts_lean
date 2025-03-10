import TextsLean.Basic

namespace Dnf.C02.S01

/-- Definition 2.1.1 Subgroup -/
example [Group G] (H : Set G) [hH : Nonempty H] : (∃ H' : Subgroup G, H' = H) ↔ ∀ (x y : G) (_ : x ∈ H) (_ : y ∈ H), x * y ∈ H ∧ x⁻¹ ∈ H := by sorry

#check Subgroup
#check Submonoid.one_mem
#check Subgroup.inv_mem'
#check Subsemigroup.mul_mem'
#check Subsemigroup.carrier
/- Basically, showing closure under the operations that make a group a group -/
#check AddSubgroup
-- Note that subgroups have commutativity automatically instantiated once the group is commutative.
-- Note that elements of a subgroup immediately obey structures of the larger group, and in Lean this comes automatically since the elements are typed as elements of the larger group, and membership is defined as a property of subgroup structure.

/-- Examples 2.1.1 -/
example : ∃ (Q : AddSubgroup ℝ), Q = { x : ℝ | ∃ q : ℚ, x = ↑q } := sorry
example : ∃ (Z : AddSubgroup ℚ), Z = { q : ℚ | ∃ n : ℤ, q = (n:ℝ) } := sorry
#synth RatCast ℝ
/- TODO -/

/-- Examples 2.1.2 -/
example [Group G] : (Unique (⊥ : Subgroup G)) := inferInstance
example [Group G] : Subgroup G := ⊥
example [Group G] : ∃ (H : Subgroup G), H = ({(1 : G)} : Set G) := by
  simp [← Subgroup.coe_bot]
example [Group G] : (⊥ : Subgroup G) ≃* Fin 1 := sorry
example [Group G] : ∃ (H : Subgroup G), H = (Set.univ : Set G) := by
  simp only [Subgroup.coe_eq_univ, exists_eq]
example [Group G] : Subgroup G := ⊤
example [Group G] : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv

/-- Examples 2.1.3 -/
example (n : ℕ) : Subgroup (DihedralGroup n) := Subgroup.closure {DihedralGroup.r 1}

example (n : ℕ) [NeZero n] : Nat.card (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)) = n := by
  symm
  calc
    n = orderOf (DihedralGroup.r 1 : DihedralGroup n) := DihedralGroup.orderOf_r_one.symm
    _ = Nat.card (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)) := by
      rw [Nat.card_zpowers]

/-- Examples 2.1.4 -/
example : ∃ (G : AddSubgroup ℤ), G = { n : ℤ | Even n } := ⟨{
  carrier := { n : ℤ | Even n },
  zero_mem' := even_zero,
  add_mem' := Even.add,
  neg_mem' := Even.neg
}, rfl⟩

/- Examples 2.1.5.(a) -/
/- TODO -/


/-- Examples 2.1.6 -/
example [Group α] (G : Subgroup α) (H : Subgroup α) (K : Subgroup α) (hGH : G ≤ H) (hHK : H ≤ K) : G ≤ K := by
  intro x hx
  exact hHK (hGH hx)
#check CompleteLattice (AddSubgroup ℤ)

/-- Proposition 2.1 -/
example [Group G] (H : Set G) (h1 : Inhabited H) (h2 : ∀ (x y : G), x ∈ H → y ∈ H → x * y⁻¹ ∈ H) : ∃ H' : Subgroup G, H = H' := by
  have one_mem' : 1 ∈ H := by
    rcases h1 with ⟨x, hx⟩
    have := h2 x x hx hx
    simp only [mul_inv_cancel] at this
    exact this
  have inv_mem' {x : G} : x ∈ H → x⁻¹ ∈ H := by
    intros hx
    have := h2 1 x one_mem' hx
    simp only [one_mul] at this
    exact this
  have mul_mem' {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := by
    intros hx hy
    have := inv_mem' hy
    have := h2 x (y⁻¹) hx this
    simp only [inv_inv] at this
    exact this
  exact ⟨{
    carrier := H,
    one_mem' := one_mem',
    mul_mem' := mul_mem',
    inv_mem' := inv_mem'
  }, rfl⟩
#check Subgroup.ofDiv

namespace Exercises

-- This is needed and not in Mathlib
theorem Rat.add_den_dvd_lcm (q₁ q₂: ℚ) : (q₁ + q₂).den ∣ q₁.den.lcm q₂.den := by
  rw [
    Rat.add_def, Rat.normalize_eq,
    Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _) (Nat.gcd_ne_zero_right (mul_ne_zero (Rat.den_ne_zero _) (Rat.den_ne_zero _))),
    ← Nat.gcd_mul_lcm _ _,
    mul_dvd_mul_iff_right (Nat.lcm_ne_zero (Rat.den_ne_zero _) (Rat.den_ne_zero _)),
    Nat.dvd_gcd_iff
  ]
  constructor
  · rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    apply Int.dvd_add
      <;> apply Dvd.dvd.mul_left <;> rw [Int.natCast_dvd_natCast]
      <;> [exact Nat.gcd_dvd_right _ _ ; exact Nat.gcd_dvd_left _ _]
  · exact dvd_mul_right _ _

/-- Exercise 2.1.1.(a) -/
example : ∃ (G : AddSubgroup ℂ), G = { z : ℂ | z.re = z.im } := ⟨{
    carrier := { z : ℂ | z.re = z.im },
    zero_mem' := by simp,
    add_mem' := by
      intros x y hx hy
      simp only [Set.mem_setOf_eq, Complex.add_re, Complex.add_im] at *
      rw [hx, hy],
    neg_mem' := by
      intros x hx
      simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.neg_im] at *
      rw [hx]
  }, rfl⟩

/-- Exercise 2.1.1.(b) -/
example : ∃ (G : Subgroup ℂˣ), G = { z : ℂˣ | ‖(z:ℂ)‖ = 1 } := ⟨{
    carrier := { z : ℂˣ | ‖(z:ℂ)‖ = 1 },
    one_mem' := by simp only [Set.mem_setOf_eq, Units.val_one, norm_one],
    mul_mem' := by
      intros x y hx hy
      simp only [Set.mem_setOf_eq, Units.val_mul, Complex.norm_mul] at hx hy ⊢;
      rw [hx, hy]; simp,
    inv_mem' := by
      intros x hx
      simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at *
      rw [hx]
  }, rfl⟩
#check Circle.coeHom

/-- Exercise 2.1.1.(c) -/
example (n : ℕ) : ∃ (G : AddSubgroup ℚ), G = { q : ℚ | q.den ∣ n } := ⟨{
    carrier := { q : ℚ | q.den ∣ n },
    zero_mem' := by simp only [Set.mem_setOf_eq, Rat.den_ofNat, isUnit_one, IsUnit.dvd],
    add_mem' := by
      intros x y hx hy
      simp only [Set.mem_setOf_eq] at *
      exact dvd_trans (Rat.add_den_dvd_lcm x y) (Nat.lcm_dvd hx hy)
    ,
    neg_mem' := by
      intros x hx
      simp only [Set.mem_setOf_eq] at *
      rwa [Rat.neg_den]
  }, rfl⟩

/-- Exercise 2.1.1.(d) -/
example (n : ℕ) : ∃ (G : AddSubgroup ℚ), G = { q : ℚ | q.den.Coprime n } := ⟨{
    carrier := { q : ℚ | q.den.Coprime n },
    zero_mem' := by simp only [Set.mem_setOf_eq, Rat.den_ofNat, Nat.coprime_one_left_eq_true],
    add_mem' := by
      intros x y hx hy
      simp only [Set.mem_setOf_eq] at *
      exact Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd x y) (Nat.Coprime.mul hx hy)
    ,
    neg_mem' := by
      intros x hx
      simp only [Set.mem_setOf_eq] at *
      rwa [Rat.neg_den]
  }, rfl⟩

/-- Exercise 2.1.1.(e) -/
example : ∃ (G : Subgroup ℝˣ), G = { x : ℝˣ | ∃ r : ℚ, (r:ℝ) = x ^ 2 } := ⟨{
    carrier := { x : ℝˣ | ∃ r : ℚ, (r:ℝ) = x ^ 2 },
    one_mem' := by
      simp only [Set.mem_setOf_eq, Units.val_one, one_pow]
      use 1
      rw [Rat.cast_one]
    ,
    mul_mem' := by
      intros x y hx hy
      simp only [Set.mem_setOf_eq] at *
      rcases hx with ⟨x', hx⟩
      rcases hy with ⟨y', hy⟩
      use (x' * y')
      push_cast
      rw [hx, hy, sq, sq, sq, mul_assoc]
      nth_rw 2 [← mul_assoc, mul_comm]
      rw [← mul_assoc, ← mul_assoc]
    ,
    inv_mem' := by
      intros x hx
      simp only [Set.mem_setOf_eq] at *
      rcases hx with ⟨x', hx⟩
      use x'⁻¹
      push_cast
      rw [hx, sq, sq, mul_inv]
  }, rfl⟩
#check Fin.mk_zero

/-- Exercise 2.1.2.(a) TODO: need to clarify if 1 is a reflection in the wording of the problem -/
example (n : ℕ) (hn : 3 ≤ n) (G : Subgroup (Equiv.Perm (Fin n))) (hG : G = { σ : Equiv.Perm (Fin n) | σ.IsSwap } ) : False := by
  let zero : Fin n := ⟨0, by linarith⟩
  let one : Fin n := ⟨1, by linarith⟩
  let two : Fin n := ⟨2, by linarith⟩
  let s01 : Equiv.Perm (Fin n) := Equiv.swap zero one
  let s02 : Equiv.Perm (Fin n) := Equiv.swap zero two
  let c012 : Equiv.Perm (Fin n) := s02 * s01
  have h01 : s01 ∈ G := by
    simp [← SetLike.mem_coe, hG, Equiv.Perm.IsSwap, s01]
    use zero, one
    constructor
    · simp [zero, one]
    · rfl
  have h02 : s02 ∈ G := by
    simp [← SetLike.mem_coe, hG, Equiv.Perm.IsSwap, s01]
    use zero, two
    constructor
    · simp [zero, two]
    · rfl
  have h012 : c012 ∈ G := G.mul_mem h02 h01
  simp [← SetLike.mem_coe, hG, Equiv.Perm.IsSwap, c012, s02, s01] at h012
  rcases h012 with ⟨x, y, hxy, hxy'⟩
  by_cases hx0 : x = zero
  · subst hx0
    have hy1 : y = one := by
      calc
        y = (Equiv.swap zero y) zero := by simp
        _ = (Equiv.swap zero two * Equiv.swap zero one) zero := by rw [hxy']
        _ = one := by
          simp [Equiv.swap_apply_of_ne_of_ne (by simp [zero, one]: one ≠ zero) (by simp [one, two] : one ≠ two)]
    subst hy1
    have contra : zero = two := by
      calc
        zero = (Equiv.swap zero one) one := by simp
        _ = (Equiv.swap zero two * Equiv.swap zero one) one := by rw [hxy']
        _ = two := by simp
    simp [zero, two] at contra
  by_cases hx1 : x = one
  · subst hx1
    have hy2 : y = two := by
      calc
        y = (Equiv.swap one y) one := by simp
        _ = (Equiv.swap zero two * Equiv.swap zero one) one := by rw [hxy']
        _ = two := by simp
    subst hy2
    have contra : one = zero := by
      calc
        one = (Equiv.swap one two) two := by simp
        _ = (Equiv.swap zero two * Equiv.swap zero one) two := by rw [hxy']
        _ = zero := by simp [Equiv.swap_apply_of_ne_of_ne (by simp [zero, two]: two ≠ zero) (by simp [one, two] : two ≠ one)]
    simp [zero, one] at contra
  by_cases hx2 : x = two
  · subst hx2
    have hy0 : y = zero := by
      calc
        y = (Equiv.swap two y) two := by simp
        _ = (Equiv.swap zero two * Equiv.swap zero one) two := by rw [hxy']
        _ = zero := by simp [Equiv.swap_apply_of_ne_of_ne (by simp [zero, two]: two ≠ zero) (by simp [one, two] : two ≠ one)]
    subst hy0
    have contra : two = one := by
      calc
        two = (Equiv.swap two zero) zero := by simp
        _ = (Equiv.swap zero two * Equiv.swap zero one) zero := by rw [hxy']
        _ = one := by simp [Equiv.swap_apply_of_ne_of_ne (by simp [zero, one]: one ≠ zero) (by simp [one, two] : one ≠ two)]
    simp [one, two] at contra
  · have contra : y = x := by
      calc
        y = (Equiv.swap x y) x := by simp
        _ = (Equiv.swap zero two * Equiv.swap zero one) x := by rw [hxy']
        _ = x := by simp [Equiv.swap_apply_of_ne_of_ne hx0 hx1, Equiv.swap_apply_of_ne_of_ne hx0 hx2]
    exact hxy contra.symm

/-- Exercise 2.1.2.(b) TODO: need to clarify if 1 is a reflection in the wording of the problem -/
example (n : ℕ) (hn : 3 ≤ n) (G : Subgroup (DihedralGroup n)) (hg : G = { g : DihedralGroup n | ∃ i, g = DihedralGroup.sr i } ) : False := sorry
/-- Exercise 2.1.2.(c) -/
example (n : ℕ) (hn : 1 ≤ n) (hnnprime : ¬Nat.Prime n) [Group G] (hg : ∃ (g : G), orderOf g = n) (H : Subgroup G) (hh : H = {g : G | g = 1 ∨ orderOf g = n} ) : False := sorry
/-- Exercise 2.1.2.(d) -/
example (G : AddSubgroup ℤ) (hg : G = {x : ℤ | x = 0 ∨ Odd x} ) : False := sorry
/-- Exercise 2.1.2.(e) -/
example (G : AddSubgroup ℝ) (hg : G = {x : ℝ | ∃ (q : ℚ), (q:ℝ) = x ^ 2 } ) : False := sorry

/-- Exercise 2.1.3.(a) -/
example : ∃ (G : Subgroup (DihedralGroup 4)), G = { g : DihedralGroup 4 | g = 1 ∨ g = DihedralGroup.r 2 ∨ g = DihedralGroup.sr 0 ∨ g = DihedralGroup.sr 2 } := ⟨{
  carrier := { g : DihedralGroup 4 | g = 1 ∨ g = DihedralGroup.r 2 ∨ g = DihedralGroup.sr 0 ∨ g = DihedralGroup.sr 2 }
  mul_mem' := sorry
  one_mem' := by simp
  inv_mem' := sorry
}, rfl⟩
/-- Exercise 2.1.3.(b) -/
example : ∃ (G : Subgroup (DihedralGroup 4)), G = { g : DihedralGroup 4 | g = 1 ∨ g = DihedralGroup.r 2 ∨ g = DihedralGroup.sr 1 ∨ g = DihedralGroup.sr 3 } := sorry

/-- Exercise 2.1.4 -/
example : ∃ (G : Type) (ha : Group G) (H : Set G) (_ : Infinite H), ∀ (H' : Subgroup G) (hHH' : H' = H), False := sorry

/-- Exercise 2.1.5 -/
example [Group G] (hcard : 2 < Nat.card G) (H : Subgroup G) : Nat.card H + 1 < Nat.card G := sorry

/-- Exercise 2.1.6 -/
example [CommGroup G] : ∃ (H : Subgroup G), H = { g : G | IsOfFinOrder g } := sorry
example : ∃ (G : Type) (ha : Group G), ∀ (H : Subgroup G), ¬H = { g : G | IsOfFinOrder g } := sorry
#check CommGroup.torsion

/-- Exercise 2.1.7 -/
example (n : ℕ) (hn : 1 < n) : ∃ (H : AddSubgroup (ℤ × ZMod n)), H = { g : ℤ × ZMod n | IsOfFinOrder g } := sorry
example (n : ℕ) (hn : 1 < n) : ∀ (H : AddSubgroup (ℤ × ZMod n)), ¬H = { g : ℤ × ZMod n | g = 1 ∨ ¬IsOfFinOrder g } := sorry
#check fun (n : ℕ) ↦ AddCommGroup.torsion (ℤ × ZMod n)

/-- Exercise 2.1.8 -/
example [Group G] (H K S : Subgroup G) (hS : S = (H:Set G) ∪ K) : (H:Set G) ⊆ K ∨ (K:Set G) ⊆ H := sorry
example [Group G] (H K : Subgroup G) (hU : H ⊔ K = (H:Set G) ∪ K) : (H:Set G) ⊆ K ∨ (K:Set G) ⊆ H := sorry

/-- Exercise 2.1.9 -/
example (n : ℕ) [CommRing R] : ∃ (SL : Subgroup (GL (Fin n) R)), SL = { A : GL (Fin n) R | A.det = 1 } := sorry
open MatrixGroups in
example (n : ℕ) [CommRing R] : ∃ (SL : Subgroup (GL (Fin n) R)), SL = Subgroup.map Matrix.SpecialLinearGroup.toGL (⊤ : Subgroup (SL(n, R))) := sorry
#check Matrix.SpecialLinearGroup
#check Matrix.GeneralLinearGroup
#check Matrix.SpecialLinearGroup.toGL
#check Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

/-- Exercise 2.1.10.(a) -/
example [Group G] (H K : Subgroup G) : ∃ (I : Subgroup G), I = (H : Set G) ∩ K:= ⟨H ⊓ K, rfl⟩
example [Group G] (H K : Subgroup G) : ∃ (I : Subgroup G), I = (H : Set G) ∩ K:= ⟨{
  carrier := (H : Set G) ∩ K,
  one_mem' := by
    simp only [Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨H.one_mem, K.one_mem⟩,
  mul_mem' := by
    intros x y hx hy
    simp only [Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨H.mul_mem hx.1 hy.1, K.mul_mem hx.2 hy.2⟩,
  inv_mem' := by
    intros x hx
    simp only [Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨H.inv_mem hx.1, K.inv_mem hx.2⟩
}, rfl⟩
/-- Exercise 2.1.10.(b) -/
example [Group G] (S : Set (Subgroup G)) : ∃ (I : Subgroup G), I = ⋂ H ∈ S, (H : Set G) := ⟨(⨅ G ∈ S, G), by simp only [Subgroup.coe_iInf]⟩
example [Group G] (S : Set (Subgroup G)) : ∃ (I : Subgroup G), I = ⋂ H ∈ S, (H : Set G) := ⟨{
  carrier := ⋂ H ∈ S, (H : Set G),
  one_mem' := by
    simp only [Set.mem_iInter, SetLike.mem_coe]
    intro G hG
    exact G.one_mem,
  mul_mem' := by
    simp only [Set.mem_iInter, SetLike.mem_coe]
    intros x y hx hy G hG
    exact G.mul_mem (hx G hG) (hy G hG),
  inv_mem' := by
    simp only [Set.mem_iInter, SetLike.mem_coe]
    intros x hx G hG
    exact G.inv_mem (hx G hG)
}, rfl⟩
/-- Exercise 2.1.11.(a) -/
example [Group A] [Group B] : ∃ (H : Subgroup (A × B)), H = { (_, b) : A × B | b = 1 } := ⟨{
  carrier := { (_, b) : A × B | b = 1 },
  one_mem' := by simp only [Set.mem_setOf_eq, Prod.snd_one],
  mul_mem' := by simp only [Set.mem_setOf_eq, Prod.snd_mul, Prod.forall, forall_eq_apply_imp_iff, mul_one, imp_self, implies_true],
  inv_mem' := by simp only [Set.mem_setOf_eq, Prod.snd_inv, inv_eq_one, imp_self, implies_true]
}, rfl⟩
/-- Exercise 2.1.11.(b) -/
example [Group A] [Group B] : ∃ (H : Subgroup (A × B)), H = { (a, _) : A × B | a = 1 } := ⟨{
  carrier := { (a, _) : A × B | a = 1 },
  one_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_one],
  mul_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.forall, forall_const, forall_eq_apply_imp_iff, mul_one, imp_self, implies_true],
  inv_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_inv, inv_eq_one, imp_self, implies_true]
}, rfl⟩
/-- Exercise 2.1.11.(c) -/
example [Group G] : ∃ (H : Subgroup (G × G)), H = { (a, b) : G × G | a = b } := ⟨{
  carrier := { (a, b) : G × G | a = b },
  one_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_one, Prod.snd_one],
  mul_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, Prod.forall,
    forall_apply_eq_imp_iff, mul_left_inj, imp_self, implies_true],
  inv_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, inv_inj, imp_self,
    implies_true]
}, rfl⟩
/-- Exercise 2.1.12.(a) -/
example (n : ℤ) [CommGroup G] : ∃ (H : Subgroup G), H = { g : G | ∃ a, g = a ^ n } := ⟨{
  carrier := { g : G | ∃ a, g = a ^ n },
  one_mem' := by simp only [Set.mem_setOf_eq]; use 1; simp only [one_zpow],
  mul_mem' := by
    simp only [Set.mem_setOf_eq, forall_exists_index]
    intro x y x' hx y' hy
    use x' * y'
    rw [mul_zpow, hx, hy],
  inv_mem' := by
    simp only [Set.mem_setOf_eq, forall_exists_index]
    intro x x' hx
    use x'⁻¹
    rw [inv_zpow, hx]
}, rfl⟩
/-- Exercise 2.1.12.(b) -/
example (n : ℤ) [CommGroup G] : ∃ (H : Subgroup G), H = { g : G | g ^ n = 1 } := ⟨{
  carrier := { g : G | g ^ n = 1 },
  one_mem' := by simp only [Set.mem_setOf_eq, one_zpow],
  mul_mem' := by
    simp only [Set.mem_setOf_eq]
    intro x y hx hy
    rw [mul_zpow, hx, hy, mul_one],
  inv_mem' := by
    simp only [Set.mem_setOf_eq, inv_zpow', zpow_neg, inv_eq_one, imp_self, implies_true]
}, rfl⟩

/-- Exercise 2.1.13 -/
example (H : AddSubgroup ℚ) (mH : ∀ (q : ℚ), q⁻¹ ∈ H) : H = ⊥ ∨ H = ⊤ := by
  by_cases hntriv : H = ⊥
  · exact Or.inl hntriv
  · sorry
    -- a nonzero rational q exists. q.num and q.den are coprime. By Bezout's identity, we can find some multiple of q that added to some multiple of q⁻¹ gives 1. Now, consider an arbitrary rational r. By multiplication we have r.den in the subgroup, so r.den⁻¹ is in it too, and so r.num copies of it give that r lies in the subgroup.
/-- Exercise 2.1.14 -/
example (n : ℕ) (hn : 3 ≤ n) (H : Subgroup (DihedralGroup n)) : ¬H = { g : DihedralGroup n | g ^ 2 = 1 } := sorry
/-- Exercise 2.1.15 -/
example [Group G] (C : Set (Subgroup G)) (hU : SuccChain (· ≤ · ) C) : ∃ (U : Subgroup G), U = ⋃ H ∈ C, (H : Set G) := sorry
/-- Exercise 2.1.16 -/
example (n : ℕ) (hn : 0 < n) [CommRing R] : ∃ (Utm : Subgroup (GL (Fin n) R)), Utm = { A : GL (Fin n) R | ∀ i j (hij : j < i), A i j = 0 } := sorry
/-- Exercise 2.1.17 -/
example (n : ℕ) (hn : 0 < n) [CommRing R] : ∃ (Ltm : Subgroup (GL (Fin n) R)), Ltm = { A : GL (Fin n) R | (∀ i j (hij : i < j), A i j = 0) ∧ (∀ i, A i i = 1) } := sorry

end Exercises

end Dnf.C02.S01
