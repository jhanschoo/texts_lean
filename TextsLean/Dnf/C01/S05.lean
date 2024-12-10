import TextsLean.Basic

namespace Dnf.C01.S05

open QuaternionGroup

/- Definition 1.5.1 -/
#check QuaternionGroup

abbrev Q := QuaternionGroup 2
/-
Identification of a n, xa n with {+,-} e, i, j, k

First identify a with i as in the complex plane
a 0 <-> +1
a 1 <-> i
a 2 <-> -1
a 3 <-> -i
Then consider the xa n to be similar but in the opposite direction
xa 0 <-> j
xa 1 <-> -k
xa 2 <-> -j
xa 3 <-> k
-/
-- 1 * q = q * 1 ∀ q : Q
example : a 0 = (1 : Q) := rfl
-- -1 * q = q * -1 ∀ q : Q
example (g : Q) : a 2 * g = g * a 2 := by
  rcases g with i | i <;> simp <;> abel
-- i ^ 2 = -1
example : (a 1 : Q) ^ 2 = a 2 := rfl
-- j ^ 2 = -1
example : (xa 0 : Q) ^ 2 = a 2 := rfl
-- k ^ 2 = -1
example : (xa 3 : Q) ^ 2 = a 2 := rfl
-- i * j = k
example : (a 1 : Q) * xa 0 = xa 3 := rfl
-- j * i = -k
example : (xa 0 : Q) * a 1 = xa 1 := rfl
-- j * k = i
example : (xa 0 : Q) * xa 3 = a 1 := rfl
-- k * j = -i
example : (xa 3 : Q) * xa 0 = a 3 := rfl
-- k * i = j
example : (xa 3 : Q) * a 1 = xa 0 := rfl
-- i * k = -j
example : (a 1 : Q) * xa 3 = xa 2 := rfl

namespace Exercises

/- Exercise 1.5.1 -/
example : orderOf (a 0 : Q) = 1 := by
  rw [QuaternionGroup.orderOf_a]; rfl
example : orderOf (a 1 : Q) = 4 := by
  rw [QuaternionGroup.orderOf_a]; rfl
example : orderOf (a 2 : Q) = 2 := by
  rw [QuaternionGroup.orderOf_a]; rfl
example : orderOf (a 3 : Q) = 4 := by
  rw [QuaternionGroup.orderOf_a]; rfl
example : orderOf (xa 1 : Q) = 4 := by
  rw [QuaternionGroup.orderOf_xa]
example : orderOf (xa 2 : Q) = 4 := by
  rw [QuaternionGroup.orderOf_xa]
example : orderOf (xa 3 : Q) = 4 := by
  rw [QuaternionGroup.orderOf_xa]
example : orderOf (xa 4 : Q) = 4 := by
  rw [QuaternionGroup.orderOf_xa]

/- TODO -/

end Exercises

end Dnf.C01.S05
