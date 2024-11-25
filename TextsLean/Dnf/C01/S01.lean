import TextsLean.Basic

namespace Dnf.C01.S01

class DnfGroup (α : Type* ) extends One α, Mul α, Inv α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
  mul_inv : ∀ a : α, a * a⁻¹ = 1
  inv_mul : ∀ a : α, a⁻¹ * a = 1

class DnfCommGroup (α : Type* ) extends DnfGroup α where
  mul_comm : ∀ a b : α, a * b = b * a

class DnfGroupWithZero (α : Type* ) extends Zero α, One α, Mul α, Inv α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
  exists_pair_ne : ∃ (x y : α), x ≠ y
  inv_zero : (0 : α)⁻¹ = 0
  mul_inv_cancel : ∀ a : α, a ≠ 0 → a * a⁻¹ = 1
  inv_mul_cancel : ∀ a : α, a ≠ 0 → a⁻¹ * a = 1

class DnfCommGroupWithZero (α : Type* ) extends DnfGroupWithZero α where
  mul_comm : ∀ a b : α, a * b = b * a

section Examples

instance : DnfGroup ℤ where
  mul := (· + · : ℤ → ℤ → ℤ)
  one := (0 : ℤ)
  inv := (- · : ℤ → ℤ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  mul_inv := Int.add_right_neg
  inv_mul := Int.add_left_neg

instance : DnfGroup ℚ where
  mul := (· + · : ℚ → ℚ → ℚ)
  one := (0 : ℚ)
  inv := (- · : ℚ → ℚ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv_mul := neg_add_cancel
  mul_inv := add_neg_cancel

instance : DnfGroup ℝ where
  mul := (· + · : ℝ → ℝ → ℝ)
  one := (0 : ℝ)
  inv := (- · : ℝ → ℝ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv_mul := neg_add_cancel
  mul_inv := add_neg_cancel

instance : DnfGroup ℂ where
  mul := (· + · : ℂ → ℂ → ℂ)
  one := (0 : ℂ)
  inv := (- · : ℂ → ℂ)
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv_mul := neg_add_cancel
  mul_inv := add_neg_cancel

instance : DnfGroupWithZero ℚ where
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

noncomputable instance : DnfGroupWithZero ℝ where
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

#check (ℝ × ℝ)

noncomputable instance : DnfGroupWithZero ℂ where
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

example : ¬ ∃a, a * (2 : ℤ) = 1 := by
  rintro ⟨a, h⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h with rfl | rfl
  · simp at *
  · simp at *

-- therefore no DnfGroupWithZero instance for ℤ exists with the usual mul

-- TODO: continued examples

end Examples

/- From hereon we use Mathlib's Group for access to its trivial lemmas -/
variable {α : Type*} [Group α]

/--
We allow ourselves the following lemmas and  from Mathlib's `Group`:
  `mul_assoc`, `one_mul`, `mul_one`


Proposition 1.(1)
Equivalent to: `mul_left_eq_self`, `mul_right_eq_self`
  which in Mathlib is proved in terms of general cancellation lemmas
-/
theorem prop_1_1 : (∀ i j : α, (∀ a : α, i * a = a) → (∀ a : α, a * j = a) → i = 1 ∧ j = 1) := by
  have prop_1_1_aux : (∀ i j : α, (∀ a : α, i * a = a) → (∀ a : α, a * j = a) → i = j) := by
   intros i j hi hj
   have hi' := hi j
   have hj' := hj i
   rw [← hi', hj']
  intro i j hi hj
  exact ⟨prop_1_1_aux i 1 hi mul_one, (prop_1_1_aux 1 j one_mul hj).symm⟩

/--
Proposition 1.(2)
Equivalent to: `left_inv_eq_right_inv`
-/
theorem prop_1_2 : (∀ a i j : α, i * a = 1 → a * j = 1 → i = a⁻¹ ∧ j = a⁻¹) := by
  have prop_1_2_aux : (∀ a i j : α, i * a = 1 → a * j = 1 → i = j) := by
    intros a i j hi hj
    calc i = i * 1 := (mul_one i).symm
      _ = i * (a * j) := by rw [hj]
      _ = (i * a) * j := by rw [mul_assoc]
      _ = 1 * j := by rw [hi]
      _ = j := one_mul j
  intro a i j hi hj
  exact ⟨prop_1_2_aux a i a⁻¹ hi (mul_inv_cancel a),
  (prop_1_2_aux a a⁻¹ j (inv_mul_cancel a) hj).symm⟩

/--
Proposition 1.(3)
Equivalent to: `inv_inv`
-/
theorem prop_1_3 : ∀ a : α, a⁻¹⁻¹ = a :=
  λ a => (prop_1_2 a⁻¹ a a (mul_inv_cancel a) (inv_mul_cancel a)).left.symm

/--
Proposition 1.(3)
Equivalent to: `mul_inv_rev`
-/
theorem prop_1_4 : ∀ a b : α, (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  intros a b
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

/--
Proposition 1.(5)

we additionally allow ourselves the use of `pow_add`.
-/
def bracket_l_r (a : α) : Tree Unit → α
  | Tree.nil => a
  | Tree.node _ l r => bracket_l_r a l * bracket_l_r a r
theorem prop_1_5 : ∀ (a : α) (t : Tree Unit), bracket_l_r a t = a ^ t.numLeaves := by
  intro a t
  cases t
  case nil => simp [bracket_l_r]
  case node _ l r =>
    have IHL := prop_1_5 a l
    have IHR := prop_1_5 a r
    dsimp [bracket_l_r]
    rw [IHL, IHR, pow_add]

/--
Proposition 2.(1)

Equivalent to: `mul_left_cancel`
-/
theorem prop_2_1 : ∀ a u v : α, a * u = a * v → u = v := by
  intros a u v h
  calc
    u = 1 * u := (one_mul u).symm
    _ = (a⁻¹ * a) * u := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * u) := by rw [mul_assoc]
    _ = a⁻¹ * (a * v) := by rw [h]
    _ = (a⁻¹ * a) * v := by rw [mul_assoc]
    _ = 1 * v := by rw [inv_mul_cancel]
    _ = v := one_mul v

/--
Proposition 2.(1)

Equivalent to: `mul_right_cancel`
-/
theorem prop_2_2 : ∀ a u v : α, u * a = v * a → u = v := by
  intros a u v h
  calc
    u = u * 1 := (mul_one u).symm
    _ = u * (a * a⁻¹) := by rw [mul_inv_cancel]
    _ = (u * a) * a⁻¹ := by rw [mul_assoc]
    _ = (v * a) * a⁻¹ := by rw [h]
    _ = v * (a * a⁻¹) := by rw [mul_assoc]
    _ = v * 1 := by rw [mul_inv_cancel]
    _ = v := mul_one v

/-
Mathlib chooses not to define the order of a group, but uses cardinality and the `Infinite` predicate instead.
-/
