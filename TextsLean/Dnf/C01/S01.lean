import TextsLean.Basic

namespace Dnf.C01.S01

/- Definition 1.1.1.(1) **binary operation** -/
#check {α : Type*} → (α → α → α)
/- Definition 1.1.1.(2) **associative** -/
#check Std.Associative
/- Definition 1.1.1.(3) **commutative** -/
#check Std.Commutative

/- Example 1.1.1.(1) -/
#synth (Std.Commutative (· + · : ℤ → ℤ → ℤ))
#synth (Std.Commutative (· + · : ℚ → ℚ → ℚ))
#synth (Std.Commutative (· + · : ℝ → ℝ → ℝ))
#synth (Std.Commutative (· + · : ℂ → ℂ → ℂ))

/- Example 1.1.1.(2) -/
#synth (Std.Commutative (· * · : ℤ → ℤ → ℤ))
#synth (Std.Commutative (· * · : ℚ → ℚ → ℚ))
#synth (Std.Commutative (· * · : ℝ → ℝ → ℝ))
#synth (Std.Commutative (· * · : ℂ → ℂ → ℂ))

/- Example 1.1.1.(3) -/
#check (· - · : ℤ → ℤ → ℤ)
example : ¬Std.Commutative (· - · : ℤ → ℤ → ℤ) := by
  intro contra
  have := contra.comm
  revert this
  simp
  use 0, 1
  norm_num

/- Example 1.1.1.(4) -/
example : ¬∀ (a b : ℤ), a > 0 → b > 0 → a - b > 0 := by
  push_neg
  use 1, 1
  norm_num
example : ¬∀ (a b : ℚ), a > 0 → b > 0 → a - b > 0 := by
  push_neg
  use 1, 1
  norm_num
example : ¬∀ (a b : ℝ), a > 0 → b > 0 → a - b > 0 := by
  push_neg
  use 1, 1
  norm_num

/- Example 1.1.1.(5) -/
section
open Matrix
example : ¬Std.Associative ((·: (Fin 3 → ℝ)) ×₃ ·) := by
  intro contra
  have := contra.assoc
  revert this
  simp
  use ![0, 1, 0], ![0, 1, 0], ![1, 0, 0]
  simp [crossProduct]
  by_contra h
  have :=
    calc (0:ℝ) = vecHead ![0, 0, 0] := by rfl
    _ = vecHead ![-1, 0, 0] := by rw [h]
    _ = -1 := by rfl
  norm_num at this
example : ¬Std.Commutative ((·: (Fin 3 → ℝ)) ×₃ ·) := by
  intro contra
  have := contra.comm
  revert this
  simp
  use ![0, 1, 0], ![0, 0, 1]
  simp [crossProduct]
  by_contra h
  have :=
    calc (1:ℝ) = vecHead ![1, 0, 0] := by rfl
    _ = vecHead ![-1, 0, 0] := by rw [h]
    _ = -1 := by rfl
  norm_num at this
end

/- Definition of **closure** -/

/- Definition 1.1.2.(1) **group** -/
#check Group
#check AddGroup
class DnfGroup (α : Type*) extends One α, Mul α, Inv α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
  mul_inv : ∀ a : α, a * a⁻¹ = 1
  inv_mul : ∀ a : α, a⁻¹ * a = 1
/- Lean defines a notion of a group with an element outside the invertibility structure added to it. -/
#check GroupWithZero
class DnfGroupWithZero (α : Type*) extends Zero α, One α, Mul α, Inv α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
  exists_pair_ne : ∃ (x y : α), x ≠ y
  inv_zero : (0 : α)⁻¹ = 0
  mul_inv_cancel : ∀ a : α, a ≠ 0 → a * a⁻¹ = 1
  inv_mul_cancel : ∀ a : α, a ≠ 0 → a⁻¹ * a = 1

/- Definition 1.1.2.(2) **abelian group** -/
#check CommGroup
#check AddCommGroup
class DnfCommGroup (α : Type* ) extends DnfGroup α where
  mul_comm : ∀ a b : α, a * b = b * a
#check CommGroupWithZero
class DnfCommGroupWithZero (α : Type* ) extends DnfGroupWithZero α where
  mul_comm : ∀ a b : α, a * b = b * a

/- Example 1.1.2.(1) -/
#synth AddCommGroup ℤ
example : DnfGroup ℤ where
  mul := (· + · : ℤ → ℤ → ℤ)
  one := (0 : ℤ)
  inv := (- · : ℤ → ℤ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  mul_inv := Int.add_right_neg
  inv_mul := Int.add_left_neg

#synth AddCommGroup ℚ
example : DnfGroup ℚ where
  mul := (· + · : ℚ → ℚ → ℚ)
  one := (0 : ℚ)
  inv := (- · : ℚ → ℚ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv_mul := neg_add_cancel
  mul_inv := add_neg_cancel

#synth AddCommGroup ℝ
example : DnfGroup ℝ where
  mul := (· + · : ℝ → ℝ → ℝ)
  one := (0 : ℝ)
  inv := (- · : ℝ → ℝ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv_mul := neg_add_cancel
  mul_inv := add_neg_cancel

#synth AddCommGroup ℂ
example : DnfGroup ℂ where
  mul := (· + · : ℂ → ℂ → ℂ)
  one := (0 : ℂ)
  inv := (- · : ℂ → ℂ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv_mul := neg_add_cancel
  mul_inv := add_neg_cancel

/- Example 1.1.2.(2) -/
#synth CommGroupWithZero ℚ
example : DnfGroupWithZero ℚ where
  zero := (0 : ℚ)
  one := (1 : ℚ)
  mul := (· * · : ℚ → ℚ → ℚ)
  inv := (·⁻¹ : ℚ → ℚ)
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  exists_pair_ne := ⟨_, _, Rat.zero_ne_one⟩
  inv_zero := inv_zero
  mul_inv_cancel := Rat.mul_inv_cancel
  inv_mul_cancel := Rat.inv_mul_cancel

#synth CommGroupWithZero ℝ
noncomputable example : DnfGroupWithZero ℝ where
  zero := (0 : ℝ)
  one := (1 : ℝ)
  mul := (· * · : ℝ → ℝ → ℝ)
  inv := (·⁻¹ : ℝ → ℝ)
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  exists_pair_ne := Real.field.exists_pair_ne
  inv_zero := inv_zero
  mul_inv_cancel := Real.field.mul_inv_cancel
  inv_mul_cancel := by
    intro a ha
    rw [Real.field.mul_comm]
    exact Real.field.mul_inv_cancel a ha

#synth CommGroupWithZero ℂ
noncomputable example : DnfGroupWithZero ℂ where
  zero := (0 : ℂ)
  one := (1 : ℂ)
  mul := Complex.instField.mul
  inv := Complex.instField.inv
  mul_assoc := Complex.instField.mul_assoc
  one_mul := Complex.instField.one_mul
  mul_one := Complex.instField.mul_one
  exists_pair_ne := Complex.instField.exists_pair_ne
  inv_zero := Complex.instField.inv_zero
  mul_inv_cancel := Complex.instField.mul_inv_cancel
  inv_mul_cancel := by
    intro a ha
    rw [Complex.instField.mul_comm]
    exact Complex.instField.mul_inv_cancel a ha

#synth CommMonoidWithZero ℤ
-- A more satisfying formal specification would be as in the below comment:
-- example (hG : CommGroupWithZero ℤ) (hzero : hG.zero = (0:ℤ)) (hmul : hG.mul = Int.mul) ... : False := by
example : ¬∃ (inv : ℤ → ℤ), ∀ a : ℤ, a ≠ 0 → a * inv a = 1 := by
  intro h
  rcases h with ⟨inv, h⟩
  have := h 2
  simp at this
  have hd1 : 2 ∣ 2 * inv 2 := by use inv 2
  rw [this] at hd1
  have hd2 : (1:ℤ) ∣ 2 := Int.one_dvd 2
  have : (1:ℤ) = 2 := Int.dvd_antisymm (by norm_num) (by norm_num) hd2 hd1
  norm_num at this
  -- apply this
  -- use hG.inv
  -- intro a ha
  -- exact hG.mul_inv_cancel a ha

section
variable {α β : Type*} [Group α] [Group β]

/- Example 1.1.2.(3) -/
section
-- Vector spaces are additive groups with respect to vector addition.
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
end

/- Example 1.1.2.(4) -/
#synth {n : ℕ} → AddCommGroup (ZMod n)

/- Example 1.1.2.(5) -/
#synth {n : ℕ} → CommGroup (ZMod n)ˣ

/- Example 1.1.2.(6) -/
#synth Group (α × β)

#check mul_left_eq_self
#check mul_right_eq_self
/- Proposition 1.1.(1) -/
example (i j : α) (hi : ∀ a : α, i * a = a) (hj : ∀ a : α, a * j = a) : i = 1 ∧ j = 1 := by
  have (i j : α) (hi : ∀ a : α, i * a = a) (hj : ∀ a : α, a * j = a) :  i = j := by
   rw [← hi j, hj i]
  exact ⟨this i 1 hi mul_one, (this 1 j one_mul hj).symm⟩
/- Note that the equivalent `mul_left_eq_self`, `mul_right_eq_self` in Mathlib is proved in terms of general cancellation lemmas -/
#check mul_left_eq_self
#check mul_right_eq_self

/- Proposition 1.1.(2) -/
example (a i j : α) (hi : i * a = 1) (hj : a * j = 1) : i = a⁻¹ ∧ j = a⁻¹ := by
  have (a i j : α) (hi : i * a = 1) (hj : a * j = 1)  :  i = j :=
    calc i = i * 1 := (mul_one i).symm
      _ = i * (a * j) := by rw [hj]
      _ = (i * a) * j := by rw [mul_assoc]
      _ = 1 * j := by rw [hi]
      _ = j := one_mul j
  exact ⟨this a i a⁻¹ hi (mul_inv_cancel a),
  (this a a⁻¹ j (inv_mul_cancel a) hj).symm⟩
#check left_inv_eq_right_inv

/- Proposition 1.1.(3) -/
example (a : α) : a⁻¹⁻¹ = a := (left_inv_eq_right_inv (mul_inv_cancel _) (mul_inv_cancel _)).symm
#check inv_inv

/- Proposition 1.1.(4) -/
example (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  set c := (a * b)⁻¹
  have : a * (b * c) = 1 := by
    rw [← mul_assoc, mul_inv_cancel]
  have : a⁻¹ * (a * (b * c)) = a⁻¹ := by
    rw [this, mul_one]
  rw [← mul_assoc, inv_mul_cancel, one_mul] at this
  have : b⁻¹ * (b * c) = b⁻¹ * a⁻¹ := by
    rw [this]
  rw [← mul_assoc, inv_mul_cancel, one_mul] at this
  exact this
#check mul_inv_rev

/- Proposition 1.1.(5) -/
def bracket_l_r (a : α) : Tree Unit → α
  | Tree.nil => a
  | Tree.node _ l r => bracket_l_r a l * bracket_l_r a r
theorem prop_1_5 (a : α) (t : Tree Unit) : bracket_l_r a t = a ^ t.numLeaves := by
  induction t
  case nil => simp [bracket_l_r]
  case node _ l r IHL IHR =>
    dsimp [bracket_l_r]
    rw [IHL, IHR, pow_add]

/-
Proposition 1.2.(1)
-/
example (a u v : α) (h : a * u = a * v) : u = v :=
  calc
    u = 1 * u := (one_mul u).symm
    _ = (a⁻¹ * a) * u := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * u) := by rw [mul_assoc]
    _ = a⁻¹ * (a * v) := by rw [h]
    _ = (a⁻¹ * a) * v := by rw [mul_assoc]
    _ = 1 * v := by rw [inv_mul_cancel]
    _ = v := one_mul v
#check mul_left_cancel

/-
Proposition 1.2.(2)
-/
example (a u v : α) (h : u * a = v * a) : u = v :=
  calc
    u = u * 1 := (mul_one u).symm
    _ = u * (a * a⁻¹) := by rw [mul_inv_cancel]
    _ = (u * a) * a⁻¹ := by rw [mul_assoc]
    _ = (v * a) * a⁻¹ := by rw [h]
    _ = v * (a * a⁻¹) := by rw [mul_assoc]
    _ = v * 1 := by rw [mul_inv_cancel]
    _ = v := mul_one v
#check mul_right_cancel

/- Definition 1.1.3
The **order** of a group element is the smallest positive integer `n` such that `a ^ n = 1`.
-/
#check orderOf
#check addOrderOf

/- Example 1.1.3.(1) -/
example (a : α) : orderOf a = 1 ↔ a = 1 := by
  constructor
  · intro h
    rw [← pow_orderOf_eq_one a, h]
    simp
  · intro ident
    rw [ident]
    simp
/- Example 1.1.3.(2) -/
example (a : ℤ) : addOrderOf a = 0 ↔ a ≠ 0 := by
  rw [addOrderOf_eq_zero_iff']
  constructor
  · intro h contra
    specialize h 1 (by norm_num)
    simp at h
    contradiction
  · intro h n hnpos contra
    simp at contra
    rcases contra with rfl | rfl
    · linarith [hnpos]
    · apply h
      rfl
example (a : ℚ) : addOrderOf a = 0 ↔ a ≠ 0 := by
  rw [addOrderOf_eq_zero_iff']
  constructor
  · intro h contra
    specialize h 1 (by norm_num)
    simp at h
    contradiction
  · intro h n hnpos contra
    simp at contra
    rcases contra with rfl | rfl
    · linarith [hnpos]
    · apply h
      rfl
example (a : ℝ) : addOrderOf a = 0 ↔ a ≠ 0 := by
  rw [addOrderOf_eq_zero_iff']
  constructor
  · intro h contra
    specialize h 1 (by norm_num)
    simp at h
    contradiction
  · intro h n hnpos contra
    simp at contra
    rcases contra with rfl | rfl
    · linarith [hnpos]
    · apply h
      rfl
example (a : ℂ) : addOrderOf a = 0 ↔ a ≠ 0 := by
  rw [addOrderOf_eq_zero_iff']
  constructor
  · intro h contra
    specialize h 1 (by norm_num)
    simp at h
    contradiction
  · intro h n hnpos contra
    simp at contra
    rcases contra with rfl | rfl
    · linarith [hnpos]
    · apply h
      rfl
/- Example 1.1.3.(3) -/
example : orderOf (-1 : ℚ) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · norm_num
  · intro m hm1 hm2
    interval_cases m
    norm_num
example : orderOf (-1 : ℝ) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · norm_num
  · intro m hm1 hm2
    interval_cases m
    norm_num
example (a : ℚ) : orderOf a = 0 ↔ (a ≠ 1 ∧ a ≠ -1) := by
  rw [orderOf_eq_zero_iff']
  constructor
  · intro h
    constructor
    · specialize h 1 (by norm_num)
      simp at h
      exact h
    · specialize h 2 (by norm_num)
      simp at h
      exact h.2
  · intro ⟨hp1, hn1⟩ n npos contra
    by_cases h0 : a = 0
    · subst h0
      have : (0 : ℚ) ^ n = 0 := by exact Mathlib.Tactic.Ring.zero_pow npos
      rw [this] at contra
      norm_num at contra
    · have asqpos : 0 < a ^ 2 := pow_two_pos_of_ne_zero h0
      have : (a ^ 2) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, contra]
        simp
      have : |(a ^ 2) ^ n| = 1 := by rw [this, abs_one]
      have hnne0 : n ≠ 0 := by linarith
      have : |a ^ 2| = 1 := by rwa [abs_pow_eq_one _ hnne0] at this
      simp at this
      rcases this with rfl | rfl <;> norm_num at *
example (a : ℝ) : orderOf a = 0 ↔ (a ≠ 1 ∧ a ≠ -1) := by
  rw [orderOf_eq_zero_iff']
  constructor
  · intro h
    constructor
    · specialize h 1 (by norm_num)
      simp at h
      exact h
    · specialize h 2 (by norm_num)
      simp at h
      exact h.2
  · intro ⟨hp1, hn1⟩ n npos contra
    by_cases h0 : a = 0
    · subst h0
      have : (0 : ℝ) ^ n = 0 := by exact Mathlib.Tactic.Ring.zero_pow npos
      rw [this] at contra
      norm_num at contra
    · have asqpos : 0 < a ^ 2 := pow_two_pos_of_ne_zero h0
      have : (a ^ 2) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, contra]
        simp
      have : |(a ^ 2) ^ n| = 1 := by rw [this, abs_one]
      have hnne0 : n ≠ 0 := by linarith
      have : |a ^ 2| = 1 := by rwa [abs_pow_eq_one _ hnne0] at this
      simp at this
      rcases this with rfl | rfl <;> norm_num at *
/- Example 1.1.3.(4) -/
example : addOrderOf (6 : ZMod 9) = 3 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (5 : ZMod 9) = 9 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
/- Example 1.1.3.(5) -/
example : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction

/- Definition 1.1.4 **group table** -/

namespace Exercises
/- Exercise 1.1.1.(a) -/
example : ¬Std.Associative (· - · : ℤ → ℤ → ℤ) := by
  intro contra
  have := contra.assoc
  revert this
  simp
  use 0, 1, 2
  norm_num
/- Exercise 1.1.1.(b) -/
example : Std.Associative (fun (a b : ℝ) ↦ a + b + a * b) := by
  constructor
  intros a b c
  ring
/- Exercise 1.1.1.(c) -/
example : ¬Std.Associative (fun (a b : ℚ) ↦ (a + b) / 5) := by
  intro contra
  have := contra.assoc
  revert this
  simp
  use 1, 0, 0
  simp
  intro contra'
  norm_num at contra'
/- Exercise 1.1.1.(d) -/
example : Std.Associative (fun (a, b) (c, d) ↦ (a * d + b * c, b * d) : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) ) := by
  constructor
  intros a b c
  ring_nf
/- Exercise 1.1.1.(e) -/
example : ¬Std.Associative (fun (a b : ℚ) ↦ a / b) := by
  intro contra
  have := contra.assoc
  revert this
  simp
  use 1, 2, 2
  simp
  intro contra'
  norm_num at contra'

/- Exercise 1.1.2.(a) -/
example : ¬Std.Commutative (· - · : ℤ → ℤ → ℤ) := by
  intro contra
  have := contra.comm
  revert this
  simp
  use 0, 1
  norm_num
/- Exercise 1.1.2.(b) -/
example : Std.Commutative (fun (a b : ℝ) ↦ a + b + a * b) := by
  constructor
  intros a b
  ring
/- Exercise 1.1.2.(c) -/
example : Std.Commutative (fun (a b : ℚ) ↦ (a + b) / 5) := by
  constructor
  intros a b
  ring
/- Exercise 1.1.2.(d) -/
example : Std.Commutative (fun (a, b) (c, d) ↦ (a * d + b * c, b * d) : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) ) := by
  constructor
  intros a b
  ring_nf
/- Exercise 1.1.2.(e) -/
example : ¬Std.Commutative (fun (a b : ℚ) ↦ a / b) := by
  intro contra
  have := contra.comm
  revert this
  simp
  use 2, 1
  simp
  intro contra'
  norm_num at contra'

/- Exercise 1.1.3 -/
example (n : ℕ) : Std.Associative (· + · : ZMod n → ZMod n → ZMod n) := by
  constructor
  intros a b c
  group

/- Exercise 1.1.4 -/
example (n : ℕ) : Std.Associative (· * · : ZMod n → ZMod n → ZMod n) := by
  constructor
  intros a b c
  group

/- Exercise 1.1.5 -/
example (n : ℕ) (ngt1 : n > 1) : ¬∀ (a : ZMod n), IsUnit a := by
  push_neg
  use 0
  intro h
  have h1 := IsUnit.val_inv_mul h
  norm_num at h1
  have h1val : (1 : ZMod n).val = 1 := by rw [ZMod.val_eq_one ngt1 1]
  have h1val : (1 : ZMod n).val ≠ 0 := by rw [h1val]; norm_num
  rw [ZMod.val_ne_zero] at h1val
  exact h1val h1.symm

/- Exercise 1.1.6 TODO -/

/- Exercise 1.1.7 TODO -/

/- Exercise 1.1.8 TODO -/

/- Exercise 1.1.9 TODO -/

/- Exercise 1.1.10 TODO -/

/- Exercise 1.1.11 -/
example : addOrderOf (0 : ZMod 12) = 1 := by simp only [addOrderOf_zero]
example : addOrderOf (1 : ZMod 12) = 12 := by simp only [ZMod.addOrderOf_one]
example : addOrderOf (2 : ZMod 12) = 6 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (3 : ZMod 12) = 4 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (4 : ZMod 12) = 3 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (5 : ZMod 12) = 12 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (6 : ZMod 12) = 2 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m ; intro contra ; contradiction
example : addOrderOf (7 : ZMod 12) = 12 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (8 : ZMod 12) = 3 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (9 : ZMod 12) = 4 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (10 : ZMod 12) = 6 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (11 : ZMod 12) = 12 := by
  calc
    addOrderOf (11 : ZMod 12) = addOrderOf (-1 : ZMod 12) := rfl
    _ = addOrderOf (1 : ZMod 12) := by simp only [addOrderOf_neg]
    _ = 12 := by simp only [ZMod.addOrderOf_one]

/- Exercise 1.1.12 -/
example : orderOf (1 : ZMod 12) = 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m
example : orderOf (-1 : ZMod 12) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m ; intro contra ; contradiction
example : orderOf (5 : ZMod 12) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m ; intro contra ; contradiction
example : orderOf (7 : ZMod 12) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m ; intro contra ; contradiction
example : orderOf (-7 : ZMod 12) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m ; intro contra ; contradiction
example : orderOf (13 : ZMod 12) = 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m

/- Exercise 1.1.13 -/
example : addOrderOf (1 : ZMod 36) = 36 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (2 : ZMod 36) = 18 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (6 : ZMod 36) = 6 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (9 : ZMod 36) = 4 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (10 : ZMod 36) = 18 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (12 : ZMod 36) = 3 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (-1 : ZMod 36) = 36 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (-10 : ZMod 36) = 18 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m <;> intro contra <;> contradiction
example : addOrderOf (-18 : ZMod 36) = 2 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m mub mlb
    interval_cases m ; intro contra ; contradiction

/- Exercise 1.1.14 -/
example : orderOf (1 : ZMod 36) = 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m
example : orderOf (-1 : ZMod 36) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m ; intro contra ; contradiction
example : orderOf (5 : ZMod 36) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m <;> intro contra <;> contradiction
example : orderOf (13 : ZMod 36) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m <;> intro contra <;> contradiction
example : orderOf (-13 : ZMod 36) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m <;> intro contra <;> contradiction
example : orderOf (17 : ZMod 36) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rfl
  · intro m hm1 hm2
    interval_cases m ; intro contra ; contradiction

/- Exercise 1.1.15 -/
example (l : List α) : (List.prod l)⁻¹ = List.prod (List.reverse (List.map (·⁻¹) l)) := by
  induction l
  case nil => simp
  case cons head tail ih => simp [ih]

/- Exercise 1.1.16 -/
example (x : α) : x ^ 2 = 1 ↔ orderOf x = 1 ∨ orderOf x = 2 := by
  constructor
  · intro h
    have h1 := orderOf_le_of_pow_eq_one (by positivity) h
    have h2 := orderOf_dvd_of_pow_eq_one h
    interval_cases orderOf x <;> simp
    · have : ¬0 ∣ 2 := by norm_num
      contradiction
  · intro h
    rcases h with h | h
    · simp at h
      subst h
      simp
    · rw [← h]
      exact pow_orderOf_eq_one x

/- Exercise 1.1.17 -/
example (x : α) (n : ℕ) (_npos : orderOf x > 0) (hord : orderOf x = n) : x⁻¹ = x ^ ((n:ℤ)-1) :=
  calc
    x⁻¹ = 1 * x⁻¹ := by group
    _ = x ^ n * x⁻¹ := by rw [← hord, pow_orderOf_eq_one x]
    _ = x ^ (n:ℤ) * x⁻¹:= by norm_cast
    _ = x ^ ((n:ℤ) - 1) * x * x⁻¹:= by group
    _ = x ^ ((n:ℤ) - 1) := by group

example (x : α) (orderOf_pos : orderOf x > 0) : x⁻¹ = x ^ (orderOf x - 1) := by
  have := orderOf_pos_iff.mp orderOf_pos
  rw [← IsOfFinOrder.val_inv_unit this]
  simp only [Units.val_inv_eq_inv_val, IsOfFinOrder.val_unit]

/- Exercise 1.1.18 -/
example (x y : α) : x * y = y * x ↔ (y⁻¹ * x * y = x ∧ x⁻¹ * y⁻¹ * x * y = 1) := by
  constructor
  · intro h
    constructor
    · calc
        y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [h]
        _ = x := by group
    · calc
        x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by group
        _ = x⁻¹ * y⁻¹ * (y * x) := by rw [h]
        _ = 1 := by group
  · intro ⟨h1, h2⟩
    calc
      x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by rw [h1]

/- Exercise 1.1.19 (we have access to stronger results and so demonstrate the stronger results; the exercise in the book proves these stronger results) -/
/- Exercise 1.1.19.(a), Exercise 1.1.19.(c) -/
example (x : α) (a b : ℤ) : x ^ (a + b) = x ^ a * x ^ b := by group
example (x : α) (a b : ℤ) : (x ^ a) ^ b = x ^ (a * b) := by group
/- Exercise 1.1.19.(b), Exercise 1.1.19.(c) -/
example (x : α) (a : ℤ) : (x ^ a)⁻¹ = x ^ (-a) := by group

/- Exercise 1.1.20 -/
example (x : α) : orderOf x⁻¹ = orderOf x := orderOf_inv x

/- TODO -/
end Exercises
end
end Dnf.C01.S01
