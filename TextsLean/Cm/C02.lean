import TextsLean.Basic

/-!
# Sums

## Notation
-/

namespace Cm.C02
open BigOperators

example (n : ℕ) := ∑ i ∈ Finset.range n, 2 ^ i
example := ∑ k ∈ { x ∈ Finset.range 100 | Odd x }, k ^ 2
example := ∑ k ∈ Finset.range 50, (2 * k + 1) ^ 2
example (N : ℕ) := ∑ p ∈ { p ∈ Finset.range (N+1) | Nat.Prime p }, 1/(p:ℚ)

-- TODO

/-!
## Sums and recurrences
-/

theorem sum_zero {β : Type} [AddCommMonoid β] : ∀ (a : ℕ → β), (∑ i in Finset.range 0, a i) = 0 := by simp

theorem sum_recurrence_ind {β : Type} [AddCommMonoid β] : ∀ (a : ℕ → β) n, (∑ i ∈ Finset.range (n + 1), a i) = (∑ i in Finset.range n, a i) + a n := by
  intro a n
  calc
    ∑ i ∈ Finset.range (n + 1), a i
      = ∑ i ∈ insert n (Finset.range n), a i := by rw [Finset.range_succ]
    _ = ∑ i ∈ Finset.range n, a i + a n := by simp [add_comm]

-- open scoped

end Cm.C02
