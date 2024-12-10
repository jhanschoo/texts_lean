import TextsLean.Basic

/-!
# 2 Sums

## 2.1 Notation
-/

namespace Cm.C02
open BigOperators

example (n : ℕ) := ∑ i ∈ Finset.Icc 1 n, i

/- Equation 2.1, 2.2, 2.3 -/
example {α : Type*} [AddCommMonoid α] (n : ℕ) (a : ℕ → α) := ∑ k in Finset.Icc 1 n, a k

example (n : ℕ) := ∑ i ∈ Finset.range n, 2 ^ i
example := ∑ k ∈ { x ∈ Finset.Ico 1 100 | Odd x }, k ^ 2
example := ∑ k ∈ Finset.range 50, (2 * k + 1) ^ 2
example : ∑ k ∈ { x ∈ Finset.Ico 1 100 | Odd x }, k ^ 2 = ∑ k ∈ Finset.Icc 0 49, (2 * k + 1) ^ 2 := by
  apply Finset.sum_bij (fun k _ ↦ (k - 1) / 2)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, Odd] at hk ⊢
    rcases hk with ⟨⟨hklb, hkub⟩, ⟨m, hm⟩⟩
    subst k
    simp
    linarith
  · simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, Odd]
    intro k ⟨⟨hklb, hkub⟩, ⟨m, hm⟩⟩ k' ⟨⟨hklb', hkub'⟩, ⟨m', hm'⟩⟩ h
    subst k k'
    simp at h
    linarith
  · simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, Odd]
    intro k ⟨hklb, hkub⟩
    use 2 * k + 1
    have : 1 ≤ 2 * k + 1 ∧ 2 * k + 1 < 100 := by constructor <;> linarith
    use (by constructor <;> [(constructor <;> linarith) ; exact ⟨k, rfl⟩])
    simp
  · simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, Odd]
    intro k ⟨⟨hklb, hkub⟩, ⟨k', h⟩⟩
    subst k
    simp
example (N : ℕ) := ∑ p ∈ { p ∈ Finset.range N | Nat.Prime p }, 1 / (p:ℚ)

noncomputable example (N : ℕ) := ∑ k ∈ Finset.range (N.primeCounting'), 1 / ((Nat.nth Nat.Prime k) : ℚ)
example (N : ℕ) : ∑ k ∈ Finset.range (N.primeCounting'), 1 / ((Nat.nth Nat.Prime k) : ℚ) = ∑ p ∈ { p ∈ Finset.range N | Nat.Prime p }, 1 / (p:ℚ) := by
  apply Finset.sum_bij (fun k _ ↦ Nat.nth Nat.Prime k) <;> simp only [Finset.mem_filter, Finset.mem_range]
  · intro k hk
    constructor <;> [skip ; simp]
    have :=
      calc
        (Nat.nth Nat.Prime k).primeCounting' = k := by simp
        _ < N.primeCounting' := hk
    exact Monotone.reflect_lt Nat.monotone_primeCounting' this
  · intro k hk k' hk' h
    have : Function.Injective (Nat.nth Nat.Prime) := Nat.nth_injective Nat.infinite_setOf_prime
    exact this h
  · intro p ⟨pub, hp⟩
    use p.primeCounting'
    have : p.primeCounting' < N.primeCounting' := by
      apply LE.le.lt_of_ne
      apply Nat.monotone_primeCounting'
      linarith
      unfold Nat.primeCounting'
      apply ne_of_lt
      exact Nat.count_strict_mono hp pub
    use this
    simp [Nat.primeCounting', hp]
  intro a ha
  trivial

/- TODO: asymptotics -/

/-!
## 2.2 Sums and recurrences
-/

/- Note that in general we do inductive definitions as $F_{n+1}$ in terms of $F_{i≤n}$, whereas Concrete Mathematics does of as $F_n$ in terms of $F_{i< n}$, which is less well-behaved. Hence we have analogous results but may differ. -/

section

variable {β : Type*} [AddCommMonoid β] (a : ℕ → β)
def S (n : ℕ) := ∑ i in Finset.range n, a i

/- Equation 2.6 -/
def S' : ℕ → β
  | 0 => 0
  | (n + 1) => S' n + a n

example (n : ℕ) : S a n = S' a n := by
  induction n <;> simp [S, S'] at *
  · case succ n hn =>
    rw [Finset.sum_range_succ, hn]
end

section

variable {β : Type*} [AddCommGroup β] (a : ℕ → β)
def S (n : ℕ) := ∑ i in Finset.range n, a i


end

-- open scoped

end Cm.C02
