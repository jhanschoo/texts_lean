import TextsLean.Basic

namespace Dnf.C01.S06

/- Definition 1.6.1 Homomorphism -/
#check MonoidHom
#check AddMonoidHom

variable [Group G] [Group H]
variable [AddGroup A] [AddGroup B]

example (φ : G →* H) (x y : G) : φ (x * y) = φ x * φ y := φ.map_mul x y
example (σ : A →+ B) (a b : A) : σ (a + b) = σ a + σ b := σ.map_add a b

#check MulEquiv
#check AddEquiv

/- Definition 1.6.2 Isomorphism -/
section
variable (ρ : G ≃* H) (τ : A ≃+ B)

#check ρ.toMonoidHom
#check ρ.left_inv
#check ρ.right_inv
#check τ.toAddMonoidHom
#check τ.left_inv
#check τ.right_inv
end

/- Examples 1.6.3.1 -/
example : G ≃* G := MulEquiv.refl G
#synth Inhabited (G ≃* G)
/- Examples 1.6.3.2 -/
#check Real.expMonoidHom
noncomputable example : MonoidHom (Multiplicative ℝ) ℝ :=
  { toFun := fun x => Real.exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [Real.exp_add] }
/- TODO show that image is ℝ+ -/
/- Examples 1.6.3.3 -/
-- Equiv.permCongr defines the bijection between the symmetric groups, but falls short of showing that it is a group isomorphism (even though it is, in the way that it is defined).
instance {α' β' : Type*} (e : α' ≃ β') : Equiv.Perm α' ≃ Equiv.Perm β' :=
  {
    toFun := Equiv.permCongr e,
    invFun := Equiv.permCongr e.symm,
    left_inv := by intro; ext; simp,
    right_inv := by intro; ext; simp
  }

namespace Exercises

/- Exercise 1.6.1.(a) -/
example (φ : G →* H) (x : G) (n : ℕ) : φ (x ^ n) = φ x ^ n := by
  induction n
  case zero => simp
  case succ n ih =>
    calc φ (x ^ n.succ)
      _ = φ (x ^ n * x) := by rw [pow_succ]
      _ = φ (x ^ n) * φ x := by rw [φ.map_mul]
      _ = φ x ^ n * φ x := by rw [ih]
      _ = φ x ^ n.succ := by rw [pow_succ]
example (φ : G →* H) (x : G) (n : ℕ) : φ (x ^ n) = φ x ^ n := MonoidHom.map_pow φ x n
/- Exercise 1.6.1.(b) -/
example (φ : G →* H) (x : G) (n : ℤ) : φ (x ^ n) = φ x ^ n := MonoidHom.map_zpow φ x n
-- the proof is located here, and is in respect to a more general context:
#check map_zpow'

/- Exercise 1.6.2 -/
example (e : G ≃* H) (x : G) : orderOf (e x) = orderOf x := orderOf_injective e.toMonoidHom e.injective x
example (e : G ≃* H) (x : G) : orderOf (e x) = orderOf x := MulEquiv.orderOf_eq e x
example (e : A ≃+ B) (x : A) : addOrderOf (e x) = addOrderOf x := AddEquiv.addOrderOf_eq e x
/- The result holds whenever φ is injective. -/
#check orderOf_injective
#check addOrderOf_injective
/- Otherwise, the following counterexample exists. -/
example (f : ZMod 2 →+ Unit) : f 1 = () ∧ addOrderOf (1 : ZMod 2) = 2 ∧ addOrderOf (() : Unit) = 1 := by simp only [ZMod.addOrderOf_one,
  AddMonoid.addOrderOf_eq_one_iff, PUnit.zero_eq, and_self]

/- Exercise 1.6.3 -/
example {G' : Type*} [CommGroup G'] (e : G' ≃* H) (x y : H) : x * y = y * x :=
  calc
    x * y = e (e.symm x * e.symm y) := by simp
    _ = e (e.symm y * e.symm x) := by rw [mul_comm _ _]
    _ = y * x := by simp
/- Note the following more generalizable similar results; the transferred structure is equal once the equivalence is a monoid isomorphism -/
#check Equiv.commMonoid
#check Equiv.addCommMonoid
#check Equiv.commGroup
#check Equiv.addCommGroup
/- Sufficient conditions: (note that notion of subgroup may be defined in terms of this property); some abelian quotient Q of G exists such that Q ->* H exists. Stricter sufficient condition: G/C ->* H exists, where C is the commutator subgroup of G -/

/- Exercise 1.6.3 -/
example (eqv : ℝˣ ≃* ℂˣ) : False := by
  have f := eqv.symm.toMonoidHom
  -- set I := Units.mk0 Complex.I Complex.I_ne_zero with hI
  have : orderOf Complex.I = 4 := by
    rw [orderOf_eq_iff]
    simp
    intro m hmub hmlb hcontra
    interval_cases m
      <;> simp [pow_succ, pow_one] at hcontra
      <;> injection hcontra with hcontra1 hcontra2
      <;> norm_num at hcontra1 hcontra2
    norm_num
  set I := Units.mk0 Complex.I Complex.I_ne_zero with hI
  have hcontra : orderOf (eqv.symm (Units.mk0 Complex.I Complex.I_ne_zero)) = 4 := by
    simp [MulEquiv.orderOf_eq eqv.symm I, hI, ← orderOf_units, this]
  have (x : ℝ) : orderOf x = 0 ∨ orderOf x = 1 ∨ orderOf x = 2 := by
    rw [orderOf_eq_zero_iff']
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    · rcases lt_trichotomy x (-1) with (hx' | rfl | hx')
      · left
        intro n hn contra
        apply_fun (|·|) at contra
        have : 1 < -x := by linarith
        have : 1 < |x| := by rw [lt_abs]; tauto
        have :=
          calc
            |x ^ n| = |1| := by rw [contra]
            _ = 1 ^ (n:ℝ) := by simp
            _ < |x| ^ (n:ℝ) := (Real.rpow_lt_rpow_iff (by positivity : (0:ℝ) ≤ 1) (by positivity : 0 ≤ |x|) (by positivity : 0 < (n:ℝ))).mpr this
            _ = |x ^ n| := by simp
        linarith
      · right; right; simp
      · left
        intro n hn contra
        apply_fun (|·|) at contra
        have : -x < 1 := by linarith
        have : x < 1 := by linarith
        have : 0 ≤ |x| := by rw [le_abs]; right; linarith
        have : |x| < 1 := by rw [abs_lt]; tauto
        have :=
          calc
            |x ^ n| = |1| := by rw [contra]
            _ = 1 ^ (n:ℝ) := by simp
            _ > |x| ^ (n:ℝ) := (Real.rpow_lt_rpow_iff (by positivity : 0 ≤ |x|) (by positivity : 0 ≤ (1:ℝ)) (by positivity : 0 < (n:ℝ))).mpr this
            _ = |x ^ n| := by simp
        linarith
    · left
      intro n hn; rw [zero_pow (by positivity)]; linarith
    · rcases lt_trichotomy x 1 with (hx' | rfl | hx')
      · left
        intro n hn contra
        rw [← Real.rpow_lt_rpow_iff (by positivity : 0 ≤ x) (by positivity : 0 ≤ (1:ℝ)) (by positivity : 0 < (n:ℝ))] at hx'
        norm_cast at hx'
        rw [contra] at hx'
        norm_cast at hx'
        rw [one_pow] at hx'
        linarith
      · right; left; simp
      · left
        intro n hn contra
        rw [← Real.rpow_lt_rpow_iff (by positivity : 0 ≤ (1:ℝ)) (by positivity : 0 ≤ (x:ℝ)) (by positivity : 0 < (n:ℝ))] at hx'
        norm_cast at hx'
        rw [contra] at hx'
        norm_cast at hx'
        rw [one_pow] at hx'
        linarith
  have (x : ℝˣ) : orderOf x = 0 ∨ orderOf x = 1 ∨ orderOf x = 2 := by
    have := this x
    rwa [orderOf_units] at this
  have := this (eqv.symm (Units.mk0 Complex.I Complex.I_ne_zero))
  rw [hcontra] at this
  tauto

/- Exercise 1.6.4 -/
example (e : ℝˣ ≃* ℂˣ) : False := by sorry

/- Exercise 1.6.5 -/
example (e : ℝ ≃+ ℚ) : False := by sorry
/- Exercise 1.6.6 -/
example (e : ℤ ≃+ ℚ) : False := by sorry
/- Exercise 1.6.7 -/
example (e : DihedralGroup 4 ≃* QuaternionGroup 2) : False := by sorry
/- Exercise 1.6.8 -/
example (n m : ℕ) (e : Equiv.Perm (Fin n) ≃* Equiv.Perm (Fin m)) : False := by sorry
/- Exercise 1.6.9 -/
example (e : DihedralGroup 12 ≃* Equiv.Perm (Fin 4)) : False := by sorry
/- Exercise 1.6.10 -/
example (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β := by
  set φ' : Equiv.Perm α → (β → β) := fun σ ↦ e ∘ σ ∘ e.symm
  /- Exercise 1.6.10.(a) -/
  set φ : Equiv.Perm α → Equiv.Perm β := by sorry
  exact {
    toFun := φ,
    /- Exercise 1.6.10.(b) -/
    invFun := by sorry,
    left_inv := by sorry,
    right_inv := by sorry,
    /- Exercise 1.6.10.(c) -/
    map_mul' := by sorry
  }
end Exercises

/- Exercise 1.6.11 -/
example : G × H ≃* H × G := by sorry

/- Exercise 1.6.12 -/
example [Group F] : (F × G) × H ≃* F × G × H := by sorry

/- Exercise 1.6.13 -/
-- TODO

/- Exercise 1.6.14 -/
-- TODO
#check MonoidHom.ker

/- Exercise 1.6.15 -/
example : ℝ × ℝ →+ ℝ := {
  toFun := Prod.fst,
  map_zero' := by simp,
  map_add' := by simp
}

/- Exercise 1.6.16 -/
def fst [Group G] [Group H] : G × H →* G := {
  toFun := Prod.fst,
  map_one' := by simp,
  map_mul' := by simp
}
#check (fst : G × H →* _).ker
def snd : G × H →* H := {
  toFun := Prod.snd,
  map_one' := by simp,
  map_mul' := by simp
}
#check (snd : G × H →* _).ker

/- Exercise 1.6.17 -/
example [hG : Group G] : (∃ (φ : G →* G), (φ : G → G) = (· ⁻¹)) ↔ ∃ (e : CommGroup G), e.toGroup = hG := by sorry

/- Exercise 1.6.18 -/
example [hG : Group G] : (∃ (φ : G →* G), (φ : G → G) = (· ^ 2)) ↔ ∃ (e : CommGroup G), e.toGroup = hG := by sorry

/- Exercise 1.6.18 -/
example [hG : Group G] : (∃ (φ : G →* G), (φ : G → G) = (· ^ 2)) ↔ ∃ (e : CommGroup G), e.toGroup = hG := by sorry

end Dnf.C01.S06
