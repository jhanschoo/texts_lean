import TextsLean.Basic

open Set
open scoped Function

private theorem Int.ediv_mul_eq_sub_emod (a b : ℤ) : a / b * b = a - a % b :=
  eq_sub_iff_add_eq.mpr (Int.ediv_add_emod' _ _)

private theorem Int.ediv_ediv_pow_eq_ediv_pow_add_one (x : ℤ) (hd : 0 < d) (n : ℕ) :
    x / d / d ^ n = x / d ^ (n + 1) := by
  rw [← Int.mul_eq_mul_right_iff (by positivity : d ^ n ≠ 0),
    ← Int.mul_eq_mul_right_iff (by positivity : d ≠ 0),
    mul_assoc (x / d ^ (n + 1)),
    Int.ediv_mul_eq_sub_emod,
    ← Int.pow_succ,
    Int.ediv_mul_eq_sub_emod,
    Int.sub_mul,
    Int.ediv_mul_eq_sub_emod,
    sub_sub,
  ]
  congr
  /-
    x / d % d ^ n ≡ x / d [ ZMOD d ]
      ↔ (x / d % d ^ n) * d ≡ (x / d) * d [ ZMOD d ^ (n + 1) ]
      ↔ x % d + (x / d % d ^ n) * d ≡ x [ ZMOD d ^ (n + 1) ]
      ↔ x % d + (x / d % d ^ n) * d ≡ x % d ^ (n + 1)
  -/
  nth_rw 3 [← Int.ediv_add_emod' x d]
  have : x % d + x / d % d ^ n * d = (x % d + x / d % d ^ n * d) % d ^ (n + 1) := by
    refine (Int.emod_eq_of_lt ?_ ?_).symm
    · exact Int.add_nonneg (Int.emod_nonneg _ (by positivity)) (Int.mul_nonneg (Int.emod_nonneg _ (by positivity)) (le_of_lt hd))
    · calc
        x % d + x / d % d ^ n * d
          < d + x / d % d ^ n * d := by rel [Int.emod_lt_of_pos x hd]
        _ = (1 + x / d % d ^ n) * d := by rw [add_mul, one_mul]
        _ ≤ (1 + (d ^ n - 1)) * d := by
          have : x / d % d ^ n < d ^ n := Int.emod_lt_of_pos (x / d) (by positivity)
          have := Int.le_sub_one_of_lt this
          rel [this]
        _ = d ^ n * d := by rw [add_comm, sub_add_cancel]
        _ = d ^ (n + 1) := by rw [Int.pow_succ]
  have hmodeq : x % d + x / d % d ^ n * d ≡ x / d * d + x % d [ZMOD d ^ (n + 1)] := by
    rw [add_comm (x % d), Int.pow_succ]
    exact Int.ModEq.add_right _ (Int.ModEq.mul_right' (Int.mod_modEq _ _))
  rw [Int.modEq_iff_add_fac] at hmodeq
  rcases hmodeq with ⟨t, hmodeq⟩
  rw [hmodeq, mul_comm (d ^ (n + 1)), Int.add_mul_emod_self]
  exact this

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

/-- The `i`th **`b`-adic interval** of rank `n` is the interval from k * b ^ n to (k+1) * b ^ n -/
def badicI (I : BadicType) (b : ℕ) (n i : ℤ) : Set ℝ :=
  let I' := match I with | .LE => Ico | .LT => Ioc
  I' (i * b ^ n) ((i + 1) * b ^ n)

/-- The `0`th `b`-adic interval of rank `0` is the unit interval -/
theorem badicI_LE_eq_unit_Ico (b : ℕ) : badicI .LE b 0 0 = Ico 0 1 := by
  dsimp [badicI]; norm_num
/-- The `0`th `b`-adic interval of rank `0` is the unit interval -/
theorem badicI_LT_eq_unit_Ioc (b : ℕ) : badicI .LT b 0 0 = Ioc 0 1 := by
  dsimp [badicI]; norm_num

theorem nonempty_badicI (I : BadicType) {b : ℕ} (hb : 0 < b) (n i : ℤ) : (badicI I b n i).Nonempty := by
  dsimp [badicI]
  split <;> [rw [Set.nonempty_Ico]; rw [Set.nonempty_Ioc]]
    <;> rel [lt_add_one (i : ℝ)]

/-- The `1`-adic (monadic) intervals are degenerate with respect to rank -/
theorem badicI_monadic_eq (I : BadicType) (m n i : ℤ) : badicI I 1 m i = badicI I 1 n i := by simp only [badicI, Nat.cast_one, one_zpow, mul_one]

/-- The `b`-adic intervals of identical rank are disjoint -/
theorem pairwise_disjoint_badicI (I : BadicType) (b : ℕ) (n : ℤ) : Pairwise (Disjoint on (fun i ↦ badicI I b n i)) := by
  cases I <;> dsimp [badicI]
  <;> [convert pairwise_disjoint_Ico_zsmul (b ^ n : ℝ) using 4
      ;convert pairwise_disjoint_Ioc_zsmul (b ^ n : ℝ) using 4]
  <;> simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]

private theorem tile_Ico_biUnion_eq_Ico (n : ℝ) {b : ℝ} (bnneg : 0 ≤ b) (k : ℕ) : ⋃ i < k, Ico (n + i * b) (n + (i + 1) * b) = Ico n (n + k * b) := by
  induction k
  case zero => simp
  case succ k ih =>
    have kbnneg : 0 ≤ (k:ℝ) * b := by positivity
    rw [Set.biUnion_lt_succ, ih, Set.Ico_union_Ico_eq_Ico (by nth_rw 1 [← add_zero (n:ℝ)]; rel [kbnneg]) (by rel [le_of_lt (lt_add_one (k:ℝ))])]
    norm_cast

private theorem tile_Ioc_biUnion_eq_Ioc (n : ℝ) {b : ℝ} (bnneg : 0 ≤ b) (k : ℕ) : ⋃ i < k, Ioc (n + i * b) (n + (i + 1) * b) = Ioc n (n + k * b) := by
  induction k
  case zero => simp
  case succ k ih =>
    have kbnneg : 0 ≤ (k:ℝ) * b := by positivity
    rw [Set.biUnion_lt_succ, ih, Set.Ioc_union_Ioc_eq_Ioc (by nth_rw 1 [← add_zero (n:ℝ)]; rel [kbnneg]) (by rel [le_of_lt (lt_add_one (k:ℝ))])]
    norm_cast

theorem badicI_rank_succ_eq_biUnion_badicI (I : BadicType) {b : ℕ} (hb : 0 < b) (n k : ℤ) :
    badicI I b (n+1) k = ⋃ i < b, badicI I b n (i + k * b) := by
  rify at hb
  simp [badicI, zpow_add_one₀ (ne_of_gt hb)]
  conv_rhs => arg 1; ext i; arg 1; ext h; arg 5; rw [(by ring : (i + k * b) * (b:ℝ) ^ n = k * (b ^ n * b) + i * b ^ n)]
  conv_rhs => arg 1; ext i; arg 1; ext h; arg 6; rw [(by ring : (i + k * b + 1) * (b:ℝ) ^ n = k * (b ^ n * b) + (i + 1) * b ^ n)]
  split
  · rw [tile_Ico_biUnion_eq_Ico (k * (b ^ n * b)) (by positivity) b, mul_comm (b:ℝ)]; ring_nf
  · rw [tile_Ioc_biUnion_eq_Ioc (k * (b ^ n * b)) (by positivity) b, mul_comm (b:ℝ)]; ring_nf

/-- The `t`th `b`-adic interval of rank `n` lies in the `u`th `b`-adic interval of rank `n+1` exactly when t / b = u rounded towards -∞. -/
theorem badicI_subset_rank_succ_iff_ediv (I : BadicType) {b : ℕ} (hb : 0 < b) (n t u : ℤ) :
    badicI I b n t ⊆ badicI I b (n+1) u ↔ t / b = u := by
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
  rcases I <;> dsimp [badicI]
  <;> [rw [Set.Ico_subset_Ico_iff hsucc]; rw [Set.Ioc_subset_Ioc_iff hsucc]]
  <;> tauto

/-- The `i`-th  **`b`-adic set** of rank `n` is the union of the `i+bℤ`-th `b`-adic intervals of rank `n`. -/
def badicSet (I : BadicType) (b : ℕ) (n i : ℤ) := ⋃ k, badicI I b n (i + k * b)

theorem badicSet_def (I : BadicType) (b : ℕ) (n i : ℤ) : badicSet I b n i = ⋃ k, badicI I b n (i + k * b) := by rfl

/-- The `b`-adic sets of identical rank are disjoint modulo `bℤ` -/
theorem pairwise_disjoint_badicSet (I : BadicType) (b : ℕ) (n : ℤ) : Pairwise (Disjoint on (fun (i : Fin b) ↦ badicSet I b n i)) := by
  have h := pairwise_disjoint_badicI (I:=I) b n
  simp only [Pairwise, badicSet, disjoint_iUnion_right, disjoint_iUnion_left] at h ⊢
  intro i j hij k k'
  refine h (fun contra ↦ hij ((Fin.val_eq_val _ _).mp (Int.natCast_inj.mp ?_)))
  refine add_mul_emod_eq_add_mul_emod_iff_eq ?_ ?_ ?_ ?_ contra
  all_goals simp only [Nat.cast_nonneg, Nat.cast_lt, Fin.is_lt]

/-- The `i+bℤ`-th `b`-adic sets of identical rank are equal -/
theorem badicSet_eq (I : BadicType) (b : ℕ) (n i j : ℤ) (hmeq : i ≡ j [ZMOD b]) : badicSet I b n i = badicSet I b n j := by
  have ⟨k, hmeq⟩ := Int.modEq_iff_add_fac.mp hmeq
  dsimp [badicSet]; ext x; constructor <;> intro h <;> rw [Set.mem_iUnion] at h ⊢ <;> rcases h with ⟨k', hk'⟩
  · use (k' - k)
    rwa [hmeq, (by ring : i + b * k + (k' - k) * b = i + (k' * b))]
  · use (k + k')
    rwa [(by ring : i + (k + k') * b = i + b * k + k' * b), ← hmeq]

theorem badicI_subset_badicSet (I : BadicType) (b : ℕ) (n i : ℤ) : badicI I b n i ⊆ badicSet I b n i := by
  have := Set.subset_iUnion (fun k ↦ badicI I b n (i + k * b)) 0
  simpa

theorem badicI_subset_badicSet_of_modEq (I : BadicType) (b : ℕ) (n i j : ℤ) (hmeq : i ≡ j [ZMOD b]) : badicI I b n i ⊆ badicSet I b n j :=
    badicSet_eq _ _ _ _ _ hmeq ▸ badicI_subset_badicSet _ _ _ _

theorem disjoint_badicI_badicSet_of_not_base_dvd (I : BadicType) (b : ℕ) (n i j : ℤ) (hmeq : ¬ i ≡ j [ZMOD b]) :
    Disjoint (badicI I b n i) (badicSet I b n j) := by
  rw [badicSet_def, Set.disjoint_iUnion_right]
  intro k
  contrapose! hmeq
  have := Pairwise.eq (pairwise_disjoint_badicI I b n) hmeq
  exact (Int.modEq_iff_add_fac.mpr ⟨k, mul_comm k b ▸ this⟩).symm

theorem modEq_of_badicI_subset_badicSet (I : BadicType) {b : ℕ} (hb : 0 < b) (n i j : ℤ) (h : badicI I b n i ⊆ badicSet I b n j) :
    i ≡ j [ZMOD b] := by
  by_contra hmeq
  have hdism := disjoint_badicI_badicSet_of_not_base_dvd I b n i j hmeq
  rw [Set.disjoint_of_subset_iff_left_eq_empty h] at hdism
  have ⟨e, he⟩ := hdism ▸ nonempty_badicI I hb n i
  exact he

theorem modEq_of_badicSet_eq (I : BadicType) {b : ℕ} (hb : 0 < b) (n i j : ℤ) (h : badicSet I b n i = badicSet I b n j) :
    i ≡ j [ZMOD b] := by
  apply subset_of_eq at h
  rw [badicSet_def, Set.iUnion_subset_iff] at h
  specialize h 0; simp only [zero_mul, add_zero] at h
  exact modEq_of_badicI_subset_badicSet I hb n i j h

/-- The `i+bℤ`-th `b`-adic sets of identical rank are equal -/
theorem badicSet_eq_iff (I : BadicType) {b : ℕ} (hb : 0 < b) (n i j : ℤ) : badicSet I b n i = badicSet I b n j ↔ i ≡ j [ZMOD b] :=
  ⟨modEq_of_badicSet_eq I hb n i j, badicSet_eq I b n i j⟩

/-- The intersection of the `t / b`th `b`-adic inverval of rank `n+1` and the `t % b`th `b`-adic set of rank `n` is the `t`th `b`-adic interval $T$ of rank `n` itself -/
theorem badicI_rank_succ_inter_badicSet_eq (I : BadicType) {b : ℕ} (hb : 0 < b) (n t : ℤ) :
    badicI I b (n+1) (t / b) ∩ badicSet I b n t = badicI I b n t := by
  apply subset_antisymm
  · intro x hx
    rw [badicSet_def, badicI_rank_succ_eq_biUnion_badicI _ (by positivity), Set.mem_inter_iff, Set.mem_iUnion₂, Set.mem_iUnion] at hx
    rcases hx with ⟨⟨n', hn', hxl⟩, k, hxr⟩
    have : t + k * (b:ℤ) = (n':ℤ) + t / b * ↑b := by
      have := (pairwise_disjoint_on _).mp (pairwise_disjoint_badicI I b n)
      rcases lt_trichotomy (t + k * (b:ℤ)) ((n':ℤ) + t / b * ↑b) with ht | ht | ht
      · exfalso; exact (Set.not_disjoint_iff.mpr ⟨x, hxr, hxl⟩) (this ht)
      · exact ht
      · exfalso; exact (Set.not_disjoint_iff.mpr ⟨x, hxl, hxr⟩) (this ht)
    have hn'' : n' = t % b := by
      apply_fun (· % (b:ℤ)) at this
      simp [Int.add_emod] at this
      norm_cast at this
      rw [Nat.mod_eq_of_lt hn'] at this
      exact this.symm
    rwa [hn'', add_comm (t % b), Int.ediv_add_emod'] at hxl
  · simp only [subset_inter_iff]
    constructor
    · exact (badicI_subset_rank_succ_iff_ediv _ hb _ _ _).mpr rfl
    · exact badicI_subset_badicSet_of_modEq _ _ _ _ _ (Int.ModEq.refl _)

/-- We may derive the `t`th `b`-adic interval of rank `n` from the `t/b^k`-th `b`-adic interval of rank `k`, through
  intersecting it with the `k` `b`-adic sets of ranks `n+i=n+0, n+1, ..., n+k-1`, where for the `n+i`-th ranked `b`-adic set we choose the `t/b^i`-th. -/
theorem badicI_rank_add_biInter_badicSet_eq (I : BadicType) {b : ℕ} (hb : 0 < b) (n t : ℤ) (k : ℕ) :
    badicI I b (n + k) (t / b ^ k) ∩ ⋂ i < k, badicSet I b (n + i) (t / b ^ i) = badicI I b n t := by
  induction k generalizing n t
  case zero => simp
  case succ k' IH =>
    rw [Set.biInter_lt_succ', Set.inter_comm (badicSet I b (n + _) _)]
    conv_lhs => arg 2; arg 1; arg 1; ext i; arg 1; ext h; arg 3; rw [(by omega : n + (i + 1:ℕ) = n + 1 + i)]
    conv_lhs => arg 2; arg 1; arg 1; ext i; arg 1; ext h; arg 4; rw [← Int.ediv_ediv_pow_eq_ediv_pow_add_one _ (by positivity)]
    rw [(by omega : n + (k' + 1:ℕ) = n + 1 + k'),
      (by rw [Int.ediv_ediv_pow_eq_ediv_pow_add_one _ (by positivity)] : t / b ^ (k' + 1) = t / b / b ^ k'),
      ← Set.inter_assoc,
      IH (n + 1) (t / b),
      pow_zero,
      Int.ediv_one,
      Nat.cast_zero,
      add_zero,
    ]
    exact badicI_rank_succ_inter_badicSet_eq _ (by positivity) _ _

theorem badicI_subset_rank_succ_iff_inter_badicSet (I : BadicType) {b : ℕ} (hb : 0 < b) (n t u : ℤ) :
    badicI I b n t ⊆ badicI I b (n+1) u ↔ badicI I b n t = badicI I b n u ∩ badicSet I b (n+1) (t % b) := by sorry
