import TextsLean.Basic

namespace Cm.C01

/-!
# Recurrent Problems

## The tower of Hanoi
-/

def T : ℕ → ℕ
  | 0 => 0
  | n+1 => 2 * T n + 1

def U (n : ℕ) : ℕ := T n + 1

example : U 0 = 1 := rfl

lemma U_ind : ∀ n, U (n + 1) = 2 * U n := by
  intro n
  simp [U, T]
  rw [Nat.add_assoc, ← Nat.succ_eq_one_add, ← Nat.mul_one (Nat.succ 1), ← Nat.left_distrib]

theorem U_closed (n : ℕ) : U n = 2^n := by
  cases n with
  | zero => rfl
  | succ n' =>
    rw [U_ind, U_closed]
    simp [Nat.pow_succ, Nat.mul_comm]

theorem T_closed (n : ℕ) : T n = 2^n - 1 := by
  have h := U_closed n
  simp [U] at h
  rw [← Nat.add_sub_cancel (T n) 1, h]

/-!
## Lines in the plane
-/

def L : ℕ → ℕ
  | 0 => 1
  | n+1 => L n + n + 1

def S : ℕ → ℕ
  | 0 => 0
  | n+1 => S n + n + 1

theorem L_S (n : ℕ) : L n = S n + 1 := by
  cases n
  · rfl
  · case succ n =>
    simp [L, S]
    have ih := L_S n
    rw [ih]
    ring

theorem two_S_closed (n : ℕ) : 2 * S n = n * (n + 1) := by
  cases n
  · rfl
  · case succ n =>
    simp [S]
    have ih := two_S_closed n
    calc
      2 * (S n + n + 1) = 2 * S n + 2 * n + 2 := by ring
      _ = n * (n + 1) + 2 * n + 2 := by rw [ih]
      _ = (n + 1) * (n + 2) := by ring

theorem S_closed (n : ℕ) : S n = n * (n + 1) / 2 := by
  rw [Nat.div_eq_of_eq_mul_left (Nat.zero_lt_succ 1)]
  rw [← two_S_closed, Nat.mul_comm]

theorem two_L_closed (n : ℕ) : 2 * L n = n * (n + 1) + 2 := by
  rw [L_S, Nat.left_distrib, two_S_closed]

theorem L_closed (n : ℕ) : L n = n * (n + 1) / 2 + 1 := by
  rw [L_S, S_closed]

def Z (n : ℕ) : ℕ := L (2 * n) - 2 * n

theorem Z_L (n : ℕ) : Z n + 2 * n = L (2 * n) := by
  simp [Z]
  apply Nat.sub_add_cancel
  rcases n with ⟨rfl | rfl⟩
  · simp
  · rw [Nat.left_distrib]
    simp [L]

-- TODO: asymptotic analysis of L, Z omitted

/-!
## The Josephus problem
-/

/- See: definition of Nat.log2 -/
theorem J_terminates : ∀ n, n ≠ 0 -> n / 2 < n
  | 0, h => by contradiction
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | n+4, _ => by
    rw [Nat.div_eq, if_pos]
    refine Nat.succ_lt_succ (Nat.lt_trans ?_ (Nat.lt_succ_self _))
    exact J_terminates (n+2) (by simp)
    simp

def J (n : ℕ) : ℤ :=
  if n = 0 then 0 else
  match n % 2 with
  | 0 =>
    2 * J (n / 2) - 1
  | _ =>
    2 * J (n / 2) + 1
  decreasing_by rename n ≠ 0 => h; exact J_terminates _ h

-- def J : ℕ → ℕ
--   | 0 => 0
--   | n'+1 =>
--     let n := n' + 1
--     match n % 2 with
--     | 0 =>
--       2 * J (n / 2) - 1
--     | _ =>
--       2 * J (n / 2) + 1

theorem J_closed (m : ℕ) : ∀ l < 2 ^ m, J (2 ^ m + l) = 2 * l + 1 := by
  intro l hl
  have hl' : l / 2 < 2 ^ (m - 1) := by
    cases m <;> simp at *
    · subst hl
      rfl
    · case succ n =>
      apply Nat.div_lt_of_lt_mul
      rw [Nat.pow_succ] at hl
      linarith
  unfold J
  split
  · -- n = 0 ⇒ l < 0, contradiction
    linarith
  split
  · case h_1 hne0 n' heq =>
    /- special case: m = 0 -/
    cases m <;> simp at *
    · subst hl
      simp at *
    case succ m' =>
    have hlmod : (2 ^ (m' + 1) + l) % 2 = l % 2 := calc
      (2 ^ (m' + 1) + l) % 2 = (2 * 2 ^ m' + l) % 2 := by rw [Nat.pow_succ, Nat.mul_comm]
      _ = l % 2 := by rw [Nat.mul_add_mod]
    suffices hdestruct : (n' + 1) / 2 = 2 ^ m' + l / 2
    · simp [hdestruct]
      have ih := J_closed m' (l / 2) hl'
      rw [ih]
      split <;> simp at *
      · case h_1 _ heven =>
        rw [← heq, hlmod] at heven
        calc
          2 * (2 * (l / 2) + 1)
            = 2 * (l / 2 * 2) + 2 := by ring
          _ = 2 * l + 2 := by rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)]
      · case h_2 _ hodd =>
        rw [← heq, hlmod] at hodd
        calc
          2 * (l / 2) + 1
            = (l / 2) * 2 + l % 2 := by rw [Nat.mul_comm, hodd]
          _ = l := Nat.div_add_mod' l 2
      -- We now prove hdestruct
    · have hm'mod : 2 ^ (m' + 1) % 2 = 0 := by
        calc
          2 ^ (m' + 1) % 2 = 2 * 2 ^ m' % 2 := by rw [Nat.pow_succ, Nat.mul_comm]
          _ = 0 % 2 := by
            rw [← Nat.mul_add_mod 2 (2 ^ m') 0, add_zero]
          _ = 0 := by simp
      have if_test : ¬ (2 ≤ 2 ^ (m' + 1) % 2 + l % 2) := by
        push_neg
        rw [hm'mod]
        simp
        apply Nat.mod_lt _ (by norm_num)
      rw [← heq, Nat.add_div (by norm_num)]
      simp [if_test]
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]

#eval J 100
#eval (2:ℕ) ^ 6 + 36
#eval 2 * 36 + 1

/-!  TODO: binary representation of Josephus with cyclic shift -/

-- There is discussion on a "repertoire method" for solving recurrences. This is a heuristic;
-- for example, we were attempting to find f(n) = aA(n) + bB(n) + cC(n), where A, B, C are "simple". But in general, this is not always possible, and we can always use the degenerate assignment f = A.

/-!
## Exercises

-/

section Exercises
theorem ex1 : ∃ (f : ℕ → ℕ), ¬(∀ d, (∀ d' < d, f 0 = f d' ∧ f 1 = f (d' + 1)) → f 0 = f d) := by
  use id
  push_neg
  use 1
  constructor <;> norm_num


/-!
ex2:
1 disk: A -> M -> B
2 disks: A -> M -> B, A -> M, B -> M -> A, M -> B, A -> B -> M

To move the nth disk A -> M, we need to move n-1 disks A -...-> B. Then while n-1 disks are on B, to move the nth disk M -> B, we need to move n-1 disks B -...-> A. Then we move the nth disk M -> B. Then we move n-1 disks A -...-> B. We thus have the recurrence

T_2 1 = 2
T_2 (n+1) = 2 + 3 * T_2 n
-/

def T_2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * T_2 n + 2

theorem ex2 (n : ℕ) : T_2 n = 3^n - 1 := by
  cases n
  · rfl
  · case succ n =>
    have ih := ex2 n
    rw [T_2, ih]
    calc
      3 * (3 ^ n - 1) + 2 = 3 * (3 ^ n - 1) + 3 - 1 := by rw [Nat.add_succ_sub_one]
      _ = 3 * (3 ^ n - 1 + 1) - 1 := by ring_nf
      _ = 3 * 3 ^ n - 1 := by rw [Nat.sub_add_cancel (Nat.pos_pow_of_pos n (by norm_num))]
      _ = 3 ^ (n + 1) - 1 := by rw [mul_comm, Nat.pow_succ]

/-!
Ex 3
There are 3^n ways to distribute n disks among 3 pegs. Furthermore, suppose a peg contains some subset of the disks; then there is only one way to arrange the disks on the peg from largest to smallest, with the disks being totally ordered by their respective sizes. Hence there are 3^n arrangements of disks on the pegs. We see that including the initial state, moving the disks according to ex2 bases through 3^n states with 3^n - 1 moves. (If a state was repeated in the sequence, then we would not have to have made the intermediate moves.)
-/

/-!
Ex 4
No. Assume wlog that the nth smallest disk is on peg A and we want to move it to peg B. Then we move the n-1 disks from various pegs to peg C, then move the nth disk to peg B, then redistribute the n-1 disks from peg C to their respective desired destinations. This requires not more than 2^n - 1 moves.
-/

/-!
Ex 5
No, if they are to remain circles in the Euclidean plane.
-/

/-!

consider adding a line to the plane. TODO

-/

/-!
TODO
-/

def Q (a : ℚ) (b : ℚ) : ℕ → ℚ
  | 0 => a
  | 1 => b
  | n + 2 => (1 + Q a b (n + 1)) / Q a b n

end Exercises

end Cm.C01
