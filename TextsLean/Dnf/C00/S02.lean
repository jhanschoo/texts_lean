import TextsLean.Basic

namespace Dnf.C00.S02

namespace Exercises

#eval (fun a b ↦ (Nat.gcd a b, Nat.xgcd a b)) 11391 5673

/- Exercise 0.2.1.(a) -/
example : Nat.gcd 20 13 = 1 ∧ 1 = 2 * 20 + -3 * 13 := by simp
/- Exercise 0.2.1.(b) -/
example : Nat.gcd 69 372 = 3 ∧ 3 = 27 * 69 + -5 * 372 := by simp
/- Exercise 0.2.1.(c) -/
example : Nat.gcd 792 275 = 11 ∧ 11 = 8 * 792 + -23 * 275 := by simp
/- Exercise 0.2.1.(d) -/
example : Nat.gcd 11391 5673 = 3 ∧ 3 = -126 * 11391 + 253 * 5673 := by simp
/- Exercise 0.2.1.(e) -/
example : Nat.gcd 1761 1567 = 1 ∧ 1 = -105 * 1761 + 118 * 1567 := by simp
/- Exercise 0.2.1.(f) -/
example : Nat.gcd 507885 60808 = 691 ∧ 691 = -17 * 507885 + 142 * 60808 := by simp

/- Exercise 0.2.2 -/
example (k a b s t : ℤ) (hka : k ∣ a) (hkb : k ∣ b) : k ∣ s * a + t * b := by
  apply dvd_add
  · exact Dvd.dvd.mul_left hka s
  · exact Dvd.dvd.mul_left hkb t

/- Exercise 0.2.3 -/
example (n : ℕ) (hnP : ¬Prime n) (hn0 : n ≠ 0) (hn1 : n ≠ 1) : ∃ a b, n ∣ a * b ∧ ¬(n ∣ a) ∧ ¬(n ∣ b) := by
  simp [Prime] at hnP
  exact hnP hn0 hn1

/- Exercise 0.2.4 -/
example (a b N d x₀ y₀ x y t : ℤ) (ha0 : a ≠ 0) (_hb0 : b ≠ 0) (hd : d = gcd a b) (hN : a * x₀ + b * y₀ = N) (hxt : x = x₀ + b / d * t) (hyt : y = y₀ - a / d * t) : a * x + b * y = N := by
  subst hd hxt hyt hN
  have hdvda : gcd a b ∣ a := gcd_dvd_left a b
  have hdvdb : gcd a b ∣ b := gcd_dvd_right a b
  have ⟨t₁, ht₁⟩ := hdvda
  have ⟨t₂, ht₂⟩ := hdvdb
  -- todo: review
  suffices h : a * (b / gcd a b * t) + -(b * (a / gcd a b * t)) = 0
  · rw [mul_add a, mul_sub b, sub_eq_neg_add, add_assoc, ← add_assoc (a * (b / gcd a b * t)), h]
    simp
  have : gcd a b ≠ 0 := by
    intro contra
    rw [contra] at ht₁
    simp at ht₁
    contradiction
  set p := gcd a b
  rw [ht₁, ht₂]
  have ht₁' : p * t₁ / p = t₁ := by
    apply Int.ediv_eq_of_eq_mul_right <;> [exact this; rfl]
  have ht₂' : p * t₂ / p = t₂ := by
    apply Int.ediv_eq_of_eq_mul_right <;> [exact this; rfl]
  rw [ht₁', ht₂']
  ring

/- Exercise 0.2.5 -/
theorem t0 : Nat.totient 0 = 0 := Nat.totient_zero
theorem t1 : Nat.totient 1 = 1 := Nat.totient_one
theorem t2 : Nat.totient 2 = 1 := Nat.totient_prime (by norm_num)
theorem t3 : Nat.totient 3 = 2 := Nat.totient_prime (by norm_num)
theorem t4 : Nat.totient 4 = 2 := @Nat.totient_prime_pow 2 (by norm_num) 2 (by norm_num)
theorem t5 : Nat.totient 5 = 4 := Nat.totient_prime (by norm_num)
theorem t6 : Nat.totient 6 = 2 := @Nat.totient_mul 3 2 (by norm_num)
theorem t7 : Nat.totient 7 = 6 := Nat.totient_prime (by norm_num)
theorem t8 : Nat.totient 8 = 4 := @Nat.totient_prime_pow 2 (by norm_num) 3 (by norm_num)
theorem t9 : Nat.totient 9 = 6 := @Nat.totient_prime_pow 3 (by norm_num) 2 (by norm_num)
theorem t10 : Nat.totient 10 = 4 := @Nat.totient_mul 5 2 (by norm_num)
theorem t11 : Nat.totient 11 = 10 := Nat.totient_prime (by norm_num)
theorem t12 : Nat.totient 12 = 4 := @Nat.totient_mul 3 4 (by norm_num)
theorem t13 : Nat.totient 13 = 12 := Nat.totient_prime (by norm_num)
theorem t14 : Nat.totient 14 = 6 := @Nat.totient_mul 7 2 (by norm_num)
theorem t15 : Nat.totient 15 = 8 := @Nat.totient_mul 5 3 (by norm_num)
theorem t16 : Nat.totient 16 = 8 := @Nat.totient_prime_pow 2 (by norm_num) 4 (by norm_num)
theorem t17 : Nat.totient 17 = 16 := Nat.totient_prime (by norm_num)
theorem t18 : Nat.totient 18 = 6 := @Nat.totient_mul 9 2 (by norm_num)
theorem t19 : Nat.totient 19 = 18 := Nat.totient_prime (by norm_num)
theorem t20 : Nat.totient 20 = 8 := @Nat.totient_mul 5 4 (by norm_num)
theorem t21 : Nat.totient 21 = 12 := @Nat.totient_mul 7 3 (by norm_num)
theorem t22 : Nat.totient 22 = 10 := @Nat.totient_mul 2 11 (by norm_num)
theorem t23 : Nat.totient 23 = 22 := Nat.totient_prime (by norm_num)
theorem t24 : Nat.totient 24 = 8 := @Nat.totient_mul 3 8 (by norm_num)
theorem t25 : Nat.totient 25 = 20 := @Nat.totient_prime_pow 5 (by norm_num) 2 (by norm_num)
theorem t26 : Nat.totient 26 = 12 := @Nat.totient_mul 2 13 (by norm_num)
theorem t27 : Nat.totient 27 = 18 := @Nat.totient_prime_pow 3 (by norm_num) 3 (by norm_num)
theorem t28 : Nat.totient 28 = 12 := @Nat.totient_mul 7 4 (by norm_num)
theorem t29 : Nat.totient 29 = 28 := Nat.totient_prime (by norm_num)
theorem t30 : Nat.totient 30 = 8 := @Nat.totient_mul 5 6 (by norm_num)

-- TODO

end Exercises

end Dnf.C00.S02
