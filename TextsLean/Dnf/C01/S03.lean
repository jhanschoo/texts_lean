import TextsLean.Basic

namespace Dnf.C01.S03

/- Definition 1.3.1 **symmetric group**, **permutations** -/
#check Equiv.Perm.permGroup
abbrev S := Equiv.Perm

#check fun {α : Type*} (σ τ : S α) ↦ σ * τ
example {α : Type*} (a : α) : (1 : S α) a = a := rfl
example (σ : S α) : σ * σ⁻¹ = 1 := by rw [mul_inv_eq_one]
example (σ : S α) : σ⁻¹ * σ = 1 := by rw [inv_mul_eq_one]

/- Definition 1.3.2 **symmetric group** of degree n -/
abbrev Sn n := Equiv.Perm (Fin n)

example : Fintype.card (Sn n) = Nat.factorial n := by rw [Fintype.card_perm, Fintype.card_fin]

/- Definition 1.3.3 **cycle** -/

#check (c[0, 11, 7, 9, 3] * c[1, 12] * c[2] * c[4, 10, 6] * c[5, 8] : Sn 13)
example : (c[0, 11, 7, 9, 3] * c[1, 12] * c[2] * c[4, 10, 6] * c[5, 8] : Sn 13)⁻¹ = c[8, 5] * c[6, 10, 4] * c[2] * c[12, 1] * c[3, 9, 7, 11, 0] := by
  repeat rw [mul_inv_rev]
  repeat rw [← mul_assoc]
  congr <;> rw [← Cycle.formPerm_reverse] <;> simp
example : c[0, 1] * c[0, 2] = c[0, 2, 1] := by
  ext i
  by_cases h : i ≤ 2
  · interval_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  · simp at *
    repeat (rw [Equiv.swap_apply_of_ne_of_ne] <;> try linarith)

/- The cyclic factors of a permutation are disjoint and commute -/
/- Definition 1.3.4 **cycle decomposition** -/
#check Equiv.Perm.cycleFactorsFinset

/- Definition 1.3.5 **length**, or **order** of a cycle. **disjoint** cycles -/

/- TODO: statement that a permutation's cycle decomposition is unique -/

namespace Exercises

/- Exercise 1.3.1 -/
section
def s' : Fin 5 → Fin 5
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 0
def s'inv : Fin 5 → Fin 5
  | 0 => 4
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 2
def t' : Fin 5 → Fin 5
  | 0 => 4
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 0
def t'inv : Fin 5 → Fin 5
  | 0 => 4
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 0
def s : Sn 5 :={
  toFun := s',
  invFun := s'inv,
  left_inv := (by
    simp [Function.LeftInverse, s', s'inv]
    intro x
    fin_cases x <;> simp),
  right_inv := (by
    simp [Function.RightInverse, Function.LeftInverse, s', s'inv]
    intro x
    fin_cases x <;> simp),
}
def t : Sn 5 :={
  toFun := t',
  invFun := t'inv,
  left_inv := (by
    simp [Function.LeftInverse, t', t'inv]
    intro x
    fin_cases x <;> simp)
  right_inv := (by
    simp [Function.RightInverse, Function.LeftInverse, t', t'inv]
    intro x
    fin_cases x <;> simp)
}
theorem s_cycle : s = c[0, 2, 4] * c[1, 3] := by
  ext x
  fin_cases x <;> reduce <;> rfl
theorem t_cycle : t = c[0, 4] * c[1, 2] := by
  ext x
  fin_cases x <;> reduce <;> rfl
theorem s2_cycle : s ^ 2 = c[0, 4, 2] := by
  ext x
  fin_cases x <;> reduce <;> rfl
theorem st_cycle : s * t = c[1, 4, 2, 3] := by
  ext x
  fin_cases x <;> reduce <;> rfl
theorem ts_cycle : t * s = c[0, 1, 3, 2] := by
  ext x
  fin_cases x <;> reduce <;> rfl
theorem t2s_cycle : t ^ 2 * s = c[0, 2, 4] * c[1, 3] := by
  ext x
  fin_cases x <;> reduce <;> rfl
theorem s_order : orderOf s = 6 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rw [Equiv.Perm.cycleType_def]
  rw [s_cycle]
  repeat rw [Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union]
  repeat' rw [Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton]
  · norm_cast
  all_goals try apply Cycle.isCycle_formPerm _ _ (by simp)
  all_goals apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
theorem t_order : orderOf t = 2 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rw [Equiv.Perm.cycleType_def]
  rw [t_cycle]
  repeat rw [Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union]
  repeat' rw [Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton]
  · norm_cast
  all_goals try apply Cycle.isCycle_formPerm _ _ (by simp)
  all_goals apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
theorem s2_order : orderOf (s ^ 2) = 3 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rw [Equiv.Perm.cycleType_def]
  rw [s2_cycle]
  rw [Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton]
  · norm_cast
  all_goals try apply Cycle.isCycle_formPerm _ _ (by simp)
theorem st_order : orderOf (s * t) = 4 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rw [Equiv.Perm.cycleType_def]
  rw [st_cycle]
  repeat' rw [Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton]
  · norm_cast
  all_goals try apply Cycle.isCycle_formPerm _ _ (by simp)
theorem ts_order : orderOf (t * s) = 4 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rw [Equiv.Perm.cycleType_def]
  rw [ts_cycle]
  repeat' rw [Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton]
  · norm_cast
  all_goals try apply Cycle.isCycle_formPerm _ _ (by simp)
theorem t2s_order : orderOf (t ^ 2 * s) = 6 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rw [Equiv.Perm.cycleType_def]
  rw [t2s_cycle]
  repeat rw [Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union]
  repeat' rw [Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton]
  · norm_cast
  all_goals try apply Cycle.isCycle_formPerm _ _ (by simp)
  all_goals apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
end

/- Exercise 1.3.2 -/
section
/- TODO -/
/- Exercise 1.3.3 -/
end

/- Exercise 1.3.4 -/
example : Fintype.card (Sn 3) = 6 := by rw [Fintype.card_perm, Fintype.card_fin]; rfl
example : Fintype.card (Sn 4) = 24 := by rw [Fintype.card_perm, Fintype.card_fin]; rfl

/- Exercise 1.3.5 -/
example : orderOf (c[0, 11, 7, 9, 3] * c[1, 12] * c[4, 10, 6] * c[5, 8] : Equiv.Perm (Fin 13)) = 30 := by
  rw [← Equiv.Perm.lcm_cycleType]
  rw [Equiv.Perm.cycleType_def]
  repeat' rw [Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union]
  repeat' rw [Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton]
  -- repeat' apply Cycle.isCycle_formPerm _ _ (by simp)
  -- repeat' apply Equiv.Perm.Disjoint.mul_left _ _
  · norm_cast
  all_goals try apply Cycle.isCycle_formPerm _ _ (by simp)
  · apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
  · apply Equiv.Perm.Disjoint.mul_left _ _
    · apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
    · apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
  · apply Equiv.Perm.Disjoint.mul_left _ _
    · apply Equiv.Perm.Disjoint.mul_left _ _
      · apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
      · apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp
    · apply (List.formPerm_disjoint_iff _ _ _ _).mpr <;> simp

/- Exercise 1.3.6 -/

/- Exercise 1.3.7 -/

/- Exercise 1.3.8 -/
example : Infinite (Equiv.Perm ℕ) := by
  set f := (fun n ↦ (Equiv.swap 0 n : Equiv.Perm ℕ)) with hf
  apply Infinite.of_injective f
  · simp [f]
    intro x x' h
    calc
      x = Equiv.swap 0 x 0 := by simp
      _ = Equiv.swap 0 x' 0 := by simp at h; rw [h]
      _ = x' := by simp

/- Exercise 1.3.9 -/
-- example (n : ℤ) : orderOf (c[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] ^ n : Sn 12) = 12 ↔ ∃ k, ∃ t ∈ [1, 5, 7, 11], n = 12 * k + t := by
--   have hord : orderOf (c[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : Sn 12) = 12 := by
--     rw [Equiv.Perm.IsCycle.orderOf]
--     · norm_cast
--     apply Cycle.isCycle_formPerm
--     simp
--   rw [← zpow_mod_orderOf _ n, hord]
--   norm_cast
--   by_cases hn : n % 12 = 0
--   · rw [hn]
--     simp at *
--     intro x
--     simp
--   constructor
--   ·
  --   mod_cases n % 12
  --     <;> norm_cast
  --     <;> rw [Int.ModEq.eq H]
  --     <;> conv_lhs => lhs; rhs; rhs; simp; rw []
  -- · intro ⟨k, t, ht, hn⟩
  --   rw [hn]
  --   rw [← zpow_mod_orderOf _ _]
  --   rw [hord]
  --   norm_cast
  --   rw [Int.ModEq.eq ht]


/- TODO -/

end Exercises

end Dnf.C01.S03
