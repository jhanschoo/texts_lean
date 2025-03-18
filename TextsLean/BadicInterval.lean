import TextsLean.Basic

open Set
open scoped Function

private theorem add_mul_emod_eq_add_mul_emod_iff_eq
    {i j b k k' : ℤ} (inneg : 0 ≤ i) (jnneg : 0 ≤ j) (ib : i < b) (jb : j < b)
    (h : i + k * b = j + k' * b) : i = j :=
  calc
    i = (i + k * b) % b := by rw [Int.add_mul_emod_self, Int.emod_eq_of_lt inneg ib]
    _ = (j + k' * b) % b := by rw [h]
    _ = j := by rw [Int.add_mul_emod_self, Int.emod_eq_of_lt jnneg jb]

inductive BadicType
  | LE
  | LT

/-- The `i`th **`b`-adic interval** of order `n` is the interval from
k * b ^ n to (k+1) * b ^ n -/
def BadicI (I : BadicType) (b : ℕ) (n i : ℤ) : Set ℝ :=
  let I' := match I with | .LE => Ico | .LT => Ioc
  I' (i * b ^ n) ((i + 1) * b ^ n)

/-- The `0`th `b`-adic interval of order `0` is the unit interval -/
theorem BadicI_LE_eq_unit_Ico (b : ℕ) : BadicI .LE b 0 0 = Ico 0 1 := by
  dsimp [BadicI]; norm_num
/-- The `0`th `b`-adic interval of order `0` is the unit interval -/
theorem BadicI_LT_eq_unit_Ioc (b : ℕ) : BadicI .LT b 0 0 = Ioc 0 1 := by
  dsimp [BadicI]; norm_num

/-- The `1`-adic (monadic) intervals are degenerate with respect to order -/
theorem BadicI_monadic_eq (I : BadicType) (m n i : ℤ) : BadicI I 1 m i = BadicI I 1 n i := by simp only [BadicI, Nat.cast_one, one_zpow, mul_one]

/-- The `b`-adic intervals of identical order are disjoint -/
theorem pairwise_disjoint_BadicI (I : BadicType) (b : ℕ) (n : ℤ) : Pairwise (Disjoint on (fun i ↦ BadicI I b n i)) := by
  cases I <;> dsimp [BadicI]
  <;> [convert pairwise_disjoint_Ico_zsmul (b ^ n : ℝ) using 4
      ;convert pairwise_disjoint_Ioc_zsmul (b ^ n : ℝ) using 4]
  <;> simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]

/-- The `t`th `b`-adic interval of order `n` lies in the `u`th `b`-adic interval of order `n+1` exactly when t / b = u rounded towards -∞. -/
theorem BadicI_subset_succ_iff_ediv (I : BadicType) {b : ℕ} (hb : 0 < b) (n t u : ℤ) :
    BadicI I b n t ⊆ BadicI I b (n+1) u ↔ t / b = u := by
  have hsucc : t * b ^ n < (t + 1 : ℝ) * b ^ n := mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
  have h : (u:ℝ) * b ^ (n + 1) ≤ t * b ^ n ∧ (t + 1 : ℝ) * b ^ n ≤ (u + 1) * b ^ (n + 1) ↔ t / b = u := by
    rw [zpow_add₀ (by positivity), zpow_one, mul_comm _ (b:ℝ), ← mul_assoc, ← mul_assoc, add_mul (u:ℝ), one_mul, add_comm _ (b:ℝ)]
    calc
      (u:ℝ) * b * b ^ n ≤ t * b ^ n ∧ (t + 1:ℝ) * b ^ n ≤ (b + u * b) * b ^ n
        ↔ (u:ℝ) * b ≤ t ∧ (t + 1:ℝ) ≤ b + u * b := by
        apply Iff.and <;> exact mul_le_mul_right (by positivity)
      _ ↔ b * u ≤ t ∧ (t + 1) ≤ b + b * u := by norm_cast; rw [mul_comm u]
      _ ↔ 0 ≤ t - b * u ∧ t - b * u < b := Iff.and (Int.sub_nonneg.symm)
        <| Iff.trans Int.add_one_le_iff Int.sub_lt_iff.symm
      _ ↔ t - b * u + b * u = t ∧ 0 ≤ t - b * u ∧ t - b * u < b := by rw [sub_add_cancel]; tauto
      _ ↔ t / b = u ∧ t % b = t - b * u := (Int.ediv_emod_unique (by positivity)).symm
      _ ↔ t / b = u := by rw [Int.emod_def]; tauto
  rcases I <;> dsimp [BadicI]
  <;> [rw [Set.Ico_subset_Ico_iff hsucc]; rw [Set.Ioc_subset_Ioc_iff hsucc]]
  <;> tauto

/-- The `i`th **`b`-adic set** of order `n` is the union of the `i+bℤ`-th `b`-adic intervals of order `n`. -/
def BadicSet (I : BadicType) (b : ℕ) (n i : ℤ) := ⋃ k, BadicI I b n (i + k * b)

/-- The `b`-adic sets of identical order are disjoint modulo `bℤ` -/
theorem pairwise_disjoint_BadicSet (I : BadicType) (b : ℕ) (n : ℤ) : Pairwise (Disjoint on (fun (i : Fin b) ↦ BadicSet I b n i)) := by
  have h := pairwise_disjoint_BadicI (I:=I) b n
  simp only [Pairwise, BadicSet, disjoint_iUnion_right, disjoint_iUnion_left] at h ⊢
  intro i j hij k k'
  refine h (fun contra ↦ hij ((Fin.val_eq_val _ _).mp (Int.natCast_inj.mp ?_)))
  refine add_mul_emod_eq_add_mul_emod_iff_eq ?_ ?_ ?_ ?_ contra
  all_goals simp only [Nat.cast_nonneg, Nat.cast_lt, Fin.is_lt]

/-- The `i+bℤ`-th `b`-adic sets of identical order are equal -/
theorem BadicSet_eq (I : BadicType) (b : ℕ) (n i k : ℤ) : BadicSet I b n i = BadicSet I b n (i + k * b) := by sorry

/-- The `i+bℤ`-th `b`-adic sets of identical order are equal -/
theorem BadicSet_eq_iff (I : BadicType) (b : ℕ) (n i j : ℤ) : BadicSet I b n i = BadicSet I b n j ↔ j - i ∣ b := by sorry

/-- The intersection of the `t / b`th `b`-adic inverval of order `n+1` and the `t % b`th `b`-adic set of order `n` is the `t`th `b`-adic interval $T$ of order `n` itself -/
theorem BadicI_succ_inter_BadicSet_eq (I : BadicType) {b : ℕ} (hb : 0 < b) (n t : ℤ) :
    BadicI I b (n+1) (t / b) ∩ BadicSet I b n (t % b) = BadicI I b n t := by
  sorry

theorem BadicI_subset_succ_iff_inter_BadicSet (I : BadicType) {b : ℕ} (hb : 0 < b) (n t u : ℤ) :
    BadicI I b n t ⊆ BadicI I b (n+1) u ↔ BadicI I b n t = BadicI I b n u ∩ BadicSet I b (n+1) (t % b) := by sorry
