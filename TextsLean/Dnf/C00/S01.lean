import TextsLean.Basic

namespace Dnf.C00.S01

namespace Exercises

section
abbrev R2 := Fin 2 → ℝ

abbrev 𝓐 := Matrix (Fin 2) (Fin 2) ℝ

def M : 𝓐 := !![1, 1; 0, 1]

def 𝓑 := {A : 𝓐 | M * A = A * M }

theorem ex1_1 : !![1, 1; 0, 1] ∈ 𝓑 := by
  simp [𝓑, M]

theorem ex1_2 : !![1, 1; 1, 1] ∉ 𝓑 := by
  simp [𝓑, M]
  intro h
  rw [← Matrix.ext_iff] at h
  simp at h
  have h1 := h 1 1
  simp at h1

theorem ex1_3 : !![0, 0; 0, 0] ∈ 𝓑 := by
  simp [𝓑, M]
  rw [← Matrix.ext_iff]
  intro i j
  fin_cases i, j
  all_goals
    simp

theorem ex1_4 : !![1, 1; 1, 1] ∉ 𝓑 := by
  simp [𝓑, M]
  intro h
  rw [← Matrix.ext_iff] at h
  simp at h
  have h1 := h 1 1
  simp at h1

theorem ex1_5 : !![1, 0; 0, 1] ∈ 𝓑 := by
  simp [𝓑, M]

theorem ex1_6 : !![0, 1; 1, 0] ∉ 𝓑 := by
  simp [𝓑, M]
  intro h
  rw [← Matrix.ext_iff] at h
  simp at h
  have h1 := h 1 1
  simp at h1

theorem ex2 : ∀ P ∈ 𝓑, ∀ Q ∈ 𝓑, P + Q ∈ 𝓑 := by
  intros P hP Q hQ
  simp only [𝓑, Set.mem_setOf_eq, M] at *
  rw [mul_add, add_mul, hP, hQ]

theorem ex3 : ∀ P ∈ 𝓑, ∀ Q ∈ 𝓑, P * Q ∈ 𝓑 := by
  intros P hP Q hQ
  simp only [𝓑, Set.mem_setOf_eq, M] at *
  rw [← mul_assoc, hP, mul_assoc, hQ, ← mul_assoc]

-- theorem ex4 (p q r s : ℝ) : !![p, q; r, s] ∈ 𝓑 := by
--   rw [𝓑, M, Set.mem_setOf_eq, ← Matrix.ext_iff]
--   intro i j
--   fin_cases i, j <;> simp

theorem ex4 (p q r s : ℝ) : (r = 0 ∧ p + q = q + s) ↔ !![p, q; r, s] ∈ 𝓑 := by
  rw [𝓑, M, Set.mem_setOf_eq, ← Matrix.ext_iff]
  constructor
  · intro ⟨hr, h⟩
    subst hr
    intro i j
    fin_cases i, j <;> simp [h]
  · intro h
    constructor
    · have h00 := h 0 0
      simp at h00
      assumption
    have h01 := h 0 1
    simp at h01
    · rw [h01]
end

open Rat in
theorem ex5_a : ¬ ∃ (f : ℚ → ℤ), ∀ (a b : ℤ), f (a /. b) = a := by
  push_neg
  intro f
  have : Decidable (f (4 /. 2) = 4) := by infer_instance
  cases this with
  | isTrue h1 =>
    use 2, 1
    have h : 2 /. 1 = 4 /. 2 := by rfl
    rw [h, h1]
    simp
  | isFalse h1 =>
    use 4, 2

open Rat in
theorem ex5_b : ∃ (f : ℚ → ℚ), ∀ (a b : ℤ), b ≠ 0 → f (a /. b) = a^2 /. b^2 := by
  use λ p ↦ p.num ^ 2 /. p.den ^ 2
  intro a b _
  simp [pow_succ, pow_zero]
  suffices h : (a /. b).num /. (a /. b).den = a /. b
  · simp only [divInt_eq_div, Int.cast_mul] at *
    have h1 : ∀ (p q : ℚ), p * p / (q * q) = (p / q) * (p / q) := by
      intros p q
      ring
    rw [h1, h1, h]
  · simp

/-
The answer to exercise 6 depends on the ambiguous notion of "decimal expansion". It is known that numbers representable as a fraction of integers where the denominator is a power of 10 has two decimal expansions, in the less precise sense of the term; one has finitely many non-zeros, the other has finitely many non-nines; we formalize this notion below.
-/
noncomputable def g (f : ℕ → ℝ) : ℕ → ℝ := λ n ↦ (f n / 10 ^ n)
def f1' : ℕ → Fin 10 := λ n ↦
  if n = 0 then 1
  else 0

def f2' : ℕ → Fin 10 := λ n ↦
  if n = 0 then 0
  else 9

def into_sequence (f : ℕ → Fin 10) : ℕ → ℚ := λ n ↦ (f n) / 10 ^ n

def f1 := into_sequence f1'
def f2 := into_sequence f2'

theorem f1_f2_ne : f1 ≠ f2 := by
  intro h
  have :=
    calc
      1 = f1 0 := by simp [f1, into_sequence, f1']
      _ = f2 0 := by rw [h]
      _ = 0 := by simp [f2, into_sequence, f2']
  norm_num at this

theorem f1_to_1 : HasSum f1 1 := by
  have : (1 : ℚ) = (∑ b ∈ {0}, f1 b) := by
    simp [f1, into_sequence, f1']
  rw [this]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  simp [f1, into_sequence, f1']
  cases n <;> simp
  · apply hn
    simp

theorem f2_to_1 : HasSum f2 1 := by
  set g := fun (n : ℕ) ↦ if n = 0 then 0 else ((1:ℚ)/10) ^ n
  set g' := fun (n : ℕ) ↦ ((1:ℚ)/10) ^ n
  have : ‖(1 : ℚ) / 10‖ < 1 := by
    rw [← Rat.norm_cast_real, Real.norm_eq_abs]
    norm_cast
    rw [← sq_lt_one_iff_abs_lt_one]
    norm_num
  have hSg' : HasSum g' (1 - (1/10))⁻¹ := hasSum_geometric_of_norm_lt_one this
  ring_nf at hSg'
  have hgg' : g = Function.update g' 0 0 := by
    funext n
    cases n <;> simp [g, g']
  have hSg : HasSum g (1 / 9) := by
    have := HasSum.update hSg' 0 0
    ring_nf at this
    rwa [hgg']
  have hf2g : f2 = fun (i : ℕ) ↦ 9 * g i := by
    funext n
    cases n <;> simp [f2, into_sequence, f2', g]
    norm_cast
  have : (9 : ℚ) ≠ 0 := by norm_cast
  have := (hasSum_mul_left_iff this).mpr hSg
  rw [← hf2g] at this
  ring_nf at this
  assumption

theorem ex6 : f1 ≠ f2 ∧ HasSum f1 1 ∧ HasSum f2 1 := ⟨f1_f2_ne, f1_to_1, f2_to_1⟩

section

variable {A B : Type*}

variable (f : A → B)

def rel := fun a b ↦ f a = f b

theorem rel_f : Equivalence (rel f) := by
  unfold rel
  constructor <;> intros <;> try simp
  · case symm x y h => rw [h]
  · case trans x y z h1 h2 => rw [h1, h2]

theorem fibers_f (hSurj : Function.Surjective f) : { S : Set A | ∃ a, S = {b | rel f a b} } = { S : Set A | ∃ b, S = f⁻¹' {b}} := by
  ext S
  simp [rel, Function.Surjective] at *
  constructor
  · intro ⟨a, h⟩
    subst h
    use f a
    ext b
    simp [eq_comm]
  · intro ⟨b, h⟩
    subst h
    specialize hSurj b
    rcases hSurj with ⟨a, rfl⟩
    use a
    ext b
    simp [eq_comm]

theorem ex7 (hSurj : Function.Surjective f) : Equivalence (rel f) ∧ { S : Set A | ∃ a, S = {b | rel f a b} } = { S : Set A | ∃ b, S = f⁻¹' {b}} :=
  ⟨rel_f f, fibers_f f hSurj⟩

end
end Exercises
end Dnf.C00.S01
