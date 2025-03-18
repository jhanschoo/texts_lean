import TextsLean.Basic

/- This text makes extensive use of the unit interval in the following guise -/
@[simp]
def UI := (Set.Ioc (0:ℝ) 1)

theorem ceso_bounds (x : ℝ) : x - ⌈x - 1⌉ ∈ Set.Ioc 0 1 := by
  by_cases h : Int.fract x = 0
  · simp
    rw [← Int.floor_add_fract x, h]
    norm_num
  · rw [← ne_eq, ← Int.fract_sub_one] at h
    rw [Int.ceil_eq_add_one_sub_fract h]
    rw [Int.fract_sub_one, ne_comm] at h
    norm_num
    exact ⟨lt_of_le_of_ne (Int.fract_nonneg x) h, le_of_lt (Int.fract_lt_one x)⟩

theorem Nat.pos_of_lt {a b : ℕ} (h : a < b) : 0 < b :=
  Nat.lt_of_le_of_lt (by norm_num) h

@[bound]
theorem Int.ceil_nonneg' [LinearOrderedRing α] [FloorRing α] {a : α} (ha : -1 < a) : 0 ≤ ⌈a⌉ := by
  rw [Int.le_ceil_iff]; simp only [Int.cast_zero, zero_sub, ha]

theorem Int.natCast_ceil_eq_ceil' [LinearOrderedRing α] [FloorRing α] {a : α} (ha : -1 < a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg' ha)]

theorem Int.natCast_ceil_eq_ceil'' [LinearOrderedRing α] [FloorRing α] {a : α} (ha : -1 < a) : (⌈a⌉₊ : α) = (⌈a⌉:α) := by
  rw [← Int.natCast_ceil_eq_ceil' ha]
  norm_cast

noncomputable def facesLE (b : ℕ) (x : ℝ) (n : ℕ) : ℕ := ⌊(x * b ^ n - ⌊x * b ^ n⌋) * b⌋₊

noncomputable def facesLT (b : ℕ) (x : ℝ) (n : ℕ) : ℕ := ⌈(x * b ^ n - ⌈x * b ^ n - 1⌉) * b - 1⌉₊

/-- `dLE b x n` is the `n`th 0-indexed digit in the LE-base-`b` expansion of `x`.

By LE-base-`b` expansion of `x` we refer to the unique base-`b` expansion of `x`
where every `x` that admits a finite expansion (a finite sum in terms of base `b` equals `x` itself) chooses it. -/
theorem facesLE_def (b : ℕ) (x : ℝ) (n : ℕ) : facesLE b x n = ⌊(x * b ^ n - ⌊x * b ^ n⌋) * b⌋₊ := by rfl

/-- `dLT b x n` is the `n`th 0-indexed digit in the LT-base-`b` expansion of `x`.

By LT-base-`b` expansion of `x` we refer to the unique binary expansion of `x`, where every finite sum of the series is less than `x`.
This distinguishes it from the other binary expansion that some `x` admit where some finite sums may be equal `x` in that expansion. -/
theorem facesLT_def (b : ℕ) (x : ℝ) (n : ℕ) : facesLT b x n = ⌈(x * b ^ n - ⌈x * b ^ n - 1⌉) * b - 1⌉₊ := by rfl

/-- The range of `d` is in {0, 1} -/
theorem facesLE_range (hb : 1 < b) {x : ℝ} : Set.range (facesLE b x) ⊆ Finset.range b := by
  intro t ht
  simp at ht ⊢
  rcases ht with ⟨n, hn⟩
  subst t
  simp [facesLE]
  rw [Nat.floor_lt' (by positivity)]
  exact mul_lt_of_lt_one_left (by positivity) (Int.fract_lt_one _)

/-- The range of `d` is in {0, 1} -/
theorem facesLT_range (hb : 1 < b) {x : ℝ} : Set.range (facesLT b x) ⊆ Finset.range b := by
  intro t ht
  simp at ht ⊢
  rcases ht with ⟨n, hn⟩
  subst t
  dsimp [facesLT]
  have hceso := ceso_bounds (x * b ^ n)
  have hceso : (x * b ^ n - ⌈x * b ^ n - 1⌉) * b - 1 ∈ Set.Ioc (-(1:ℝ)) (b - 1) := by
    rw [Set.sub_mem_Ioc_iff_left]
    simp only [neg_add_cancel, sub_add_cancel, Int.cast_sub, Int.cast_one, Set.mem_Ioc] at hceso ⊢
    exact ⟨mul_pos hceso.1 (by positivity), mul_le_of_le_one_left (by positivity) hceso.2⟩
  zify
  simp only [Set.mem_Ioc] at hceso
  rw [Int.natCast_ceil_eq_ceil' hceso.1, Int.ceil_lt_iff, (by norm_num: ((b:ℤ):ℝ)=(b:ℝ))]
  exact hceso.2

/-- If f denote a sequence of 0's and 1's, then `unit_val f n` interprets the sequence as a binary expansion, and evaluates to the contribution of the `n`th 0-indexed bit. While also defined for f evaluating to beyond {0, 1}, we make no statement on the behavior there. -/
noncomputable def placeVal (f : ℕ → ℕ) (b n : ℕ) := (f n : ℝ) * (b:ℝ)⁻¹ ^ (n + 1)

theorem placeVal_def (f : ℕ → ℕ) (b n : ℕ) : placeVal f b n = (f n : ℝ) * (b:ℝ)⁻¹ ^ (n + 1) := by rfl

/-- The statement of `d'_def` without using inverse powers -/
theorem placeVal_mul (f : ℕ → ℕ) (b n : ℕ) (hb : 0 < b) : placeVal f b n * b ^ (n + 1) = f n := by
  rw [placeVal_def]
  calc
    f n * (b:ℝ)⁻¹ ^ (n + 1) * b ^ (n + 1) = f n * ((b:ℝ)⁻¹ * b) ^ (n + 1) := by ring
    _ = f n := by rw [inv_mul_cancel₀ (by positivity), one_pow, mul_one]

/-- The range of `unit_val` lies in `[0,+∞)` -/
theorem placeVal_nonneg {f : ℕ → ℕ} {b n : ℕ} : 0 ≤ placeVal f b n := by
  dsimp [placeVal]
  positivity

/-- The range of `d` lies in `(-∞,2^(-n-1)]` -/
theorem placeVal_le {f : ℕ → ℕ} {b : ℕ} (n : ℕ) (hfb : Set.range f ⊆ Finset.range b) : placeVal f b n + (b:ℝ)⁻¹ ^ (n + 1) ≤ (b⁻¹:ℝ) ^ n := by
  dsimp [placeVal]
  have := hfb (Set.mem_range_self n)
  simp only [Finset.coe_range, Set.mem_Iio] at this
  have b_pos : 0 < b := Nat.pos_of_lt this
  apply Nat.add_one_le_of_lt at this
  rify [b_pos] at this
  calc
    f n * (b:ℝ)⁻¹ ^ (n + 1) + (b:ℝ)⁻¹ ^ (n + 1) = (f n + 1) * (b:ℝ)⁻¹ ^ (n + 1) := by ring
    _ ≤ b * (b:ℝ)⁻¹ ^ (n + 1) := by rel [this]
    _ = (b * (b:ℝ)⁻¹) * (b:ℝ)⁻¹ ^ n := by ring
    _ = (b:ℝ)⁻¹ ^ n := by rw [mul_inv_cancel₀ (by positivity), one_mul]

theorem placeVal_le_of_lt {f f' : ℕ → ℕ} {b n : ℕ} (hff' : placeVal f b n < placeVal f' b n) : placeVal f b n + (b:ℝ)⁻¹ ^ (n + 1) ≤ placeVal f' b n := by
  simp only [Finset.coe_range, Set.mem_Iio, placeVal, ge_iff_le] at hff' ⊢
  replace hff' := lt_of_mul_lt_mul_right hff' (by positivity)
  norm_cast at hff'
  apply Nat.add_one_le_of_lt at hff'
  calc
    f n * (b:ℝ)⁻¹ ^ (n + 1) + (b:ℝ)⁻¹ ^ (n + 1) = (f n + 1 : ℕ) * (b:ℝ)⁻¹ ^ (n + 1) := by norm_num; ring
    _ ≤ f' n * (b:ℝ)⁻¹ ^ (n + 1) := by rel [hff']

/-- If f denote a sequence of 0's and 1's, then `unit_sum f n` interprets the sequence as a binary expansion, and evaluates to the fraction represented by the first `n` bits. While also defined for f evaluating to beyond {0, 1}, we make no statement on the behavior there. -/
noncomputable def placePSum (f : ℕ → ℕ) (b n : ℕ) := ∑ i ∈ Finset.range n, placeVal f b i

theorem placePSum_def (f : ℕ → ℕ) (b n : ℕ) : placePSum f b n = ∑ i ∈ Finset.range n, placeVal f b i := by rfl

theorem placePSum_zero {f : ℕ → ℕ} {b : ℕ} : placePSum f b 0 = 0 := by
  rw [placePSum_def, Finset.range_zero, Finset.sum_empty]

theorem placePSum_succ (f : ℕ → ℕ) (b n : ℕ) : placePSum f b (n + 1) = placePSum f b n + placeVal f b n :=
  Finset.sum_range_succ _ _

theorem placePSum_add (f : ℕ → ℕ) (b n k : ℕ) : placePSum f b (n + k) = placePSum f b n + ∑ i ∈ Finset.range k, placeVal f b (n + i) :=
  Finset.sum_range_add _ _ _

theorem placePSum_le_add (f : ℕ → ℕ) (b n k : ℕ) : placePSum f b n ≤ placePSum f b (n + k) := by
  rw [placePSum_def, placePSum_def, Finset.sum_range_add]
  exact Finset.sum_nonneg' (fun _ ↦ placeVal_nonneg) |> le_add_of_nonneg_right

theorem placePSum_nonneg {b : ℕ} {f : ℕ → ℕ} {n : ℕ} : 0 ≤ placePSum f b n := by
  rw [placePSum_def]
  exact Finset.sum_nonneg' (fun _ ↦ placeVal_nonneg)

theorem placePSum_diff_le {b : ℕ} (hb : 1 < b) {f : ℕ → ℕ} (hf : Set.range f ⊆ Finset.range b) (n k : ℕ) : placePSum f b (n + k) - placePSum f b n ≤ (b:ℝ)⁻¹ ^ n - (b:ℝ)⁻¹ ^ (n + k) := by
  rw [placePSum_add, add_sub_right_comm, sub_self, zero_add]
  have (i : ℕ) : placeVal f b (n + i) ≤ (b:ℝ)⁻¹ ^ (n + i) - (b:ℝ)⁻¹ ^ (n + i + 1) := le_sub_right_of_add_le <| placeVal_le (n + i) hf
  have (i : ℕ) (hi : i ∈ Finset.range k) : placeVal f b (n + i) ≤ (b:ℝ)⁻¹ ^ i * ((b:ℝ)⁻¹ ^ n * (1 - (b:ℝ)⁻¹)) := calc
    placeVal f b (n + i) ≤ (↑b)⁻¹ ^ (n + i) - (↑b)⁻¹ ^ (n + i + 1) := this i
    _ = (b:ℝ)⁻¹ ^ i * ((b:ℝ)⁻¹ ^ n * (1 - (b:ℝ)⁻¹)) := by ring
  suffices h : ∑ i ∈ Finset.range k, (b:ℝ)⁻¹ ^ i * ((b:ℝ)⁻¹ ^ n * (1 - (b:ℝ)⁻¹)) = (b:ℝ)⁻¹ ^ n - (b:ℝ)⁻¹ ^ (n + k) from h ▸ Finset.sum_le_sum this
  rw [← Finset.sum_mul, geom_sum_eq (by rw [inv_ne_one]; norm_cast; omega) _]
  -- ⊢ ((↑b)⁻¹ ^ k - 1) / ((↑b)⁻¹ - 1) * ((↑b)⁻¹ ^ n * (1 - (↑b)⁻¹)) = (↑b)⁻¹ ^ n - (↑b)⁻¹ ^ (n + k)
  calc
    ((b:ℝ)⁻¹ ^ k - 1) / ((b:ℝ)⁻¹ - 1) * ((b:ℝ)⁻¹ ^ n * (1 - (b:ℝ)⁻¹))
      = ((b:ℝ)⁻¹ ^ n - (b:ℝ)⁻¹ ^ (n + k)) * (((b:ℝ)⁻¹ - 1) / ((b:ℝ)⁻¹ - 1) ) := by ring
    _ = (b:ℝ)⁻¹ ^ n - (b:ℝ)⁻¹ ^ (n + k) := by rw [div_self (by rw [sub_ne_zero, inv_ne_one]; norm_cast; omega), mul_one]

theorem placePSum_le {b : ℕ} (hb : 1 < b) {f : ℕ → ℕ} (hf : Set.range f ⊆ Finset.range b) (n : ℕ) : placePSum f b n ≤ 1 - (b:ℝ)⁻¹ ^ n := by
  have := placePSum_diff_le hb hf 0 n
  rwa [zero_add, placePSum_zero, sub_zero, pow_zero] at this

theorem placePSum_le_of_lt {b : ℕ} (hb : 1 < b) {f f' : ℕ → ℕ} (hf : Set.range f ⊆ Finset.range b) (hf' : Set.range f' ⊆ Finset.range b) (n : ℕ) (h : placePSum f b n < placePSum f' b n) : placePSum f b n + (b:ℝ)⁻¹ ^ n ≤ placePSum f' b n := by
  induction n generalizing f f'
  case zero => simp [placePSum] at h
  case succ n IH =>
    rw [placePSum_succ, placePSum_succ] at h
    rcases lt_trichotomy (placePSum f b n) (placePSum f' b n) with h' | h' | h'
    · have := IH hf hf' h'
      rw [placePSum_succ f, placePSum_succ f', add_assoc]
      calc
        placePSum f b n + (placeVal f b n + (↑b)⁻¹ ^ (n + 1))
          ≤ placePSum f b n + (b⁻¹:ℝ) ^ n := by rel [placeVal_le n hf]
        _ ≤ placePSum f' b n := this
        _ = placePSum f' b n + 0 := (add_zero _).symm
        _ ≤ placePSum f' b n + placeVal f' b n := by rel [placeVal_nonneg]
    · rw [h'] at h
      apply lt_of_add_lt_add_left at h
      rw [placePSum_succ f, placePSum_succ f', h', add_assoc]
      exact add_le_add_left (placeVal_le_of_lt h) _
    · have := IH hf' hf h'
      have := calc
        placePSum f' b n + placeVal f' b n = placePSum f' b n + (placeVal f' b n + 0) := by rw [add_zero]
        _ < placePSum f' b n + (placeVal f' b n + (b:ℝ)⁻¹ ^ (n + 1)) := by
          rel [(by positivity : 0 < (b:ℝ)⁻¹ ^ (n + 1))]
        _ ≤ placePSum f' b n + (b:ℝ)⁻¹ ^ n := by rel [placeVal_le n hf']
        _ ≤ placePSum f b n := this
        _ = placePSum f b n + 0 := (add_zero _).symm
        _ ≤ placePSum f b n + placeVal f b n := by rel [placeVal_nonneg]
        _ < placePSum f' b n + placeVal f' b n := h
      linarith

theorem placePSum_add_lt_of_lt {b : ℕ} (hb : 1 < b) {f f' : ℕ → ℕ} (hf : Set.range f ⊆ Finset.range b) (hf' : Set.range f' ⊆ Finset.range b) (n : ℕ) (h : placePSum f b n < placePSum f' b n) (k : ℕ) : placePSum f b (n + k) < placePSum f' b n := by
  induction n generalizing f f' k
  case zero => simp [placePSum] at h
  case succ n IH =>
    rw [placePSum_succ, placePSum_succ] at h
    rcases lt_trichotomy (placePSum f b n) (placePSum f' b n) with h' | h' | h'
    · have := IH hf hf' h' (1 + k)
      rw [← add_assoc] at this
      exact lt_of_lt_of_le this (placePSum_le_add f' b n 1)
    · apply lt_of_tsub_lt_tsub_right (c := placePSum f b (n + 1))
      apply lt_of_le_of_lt (placePSum_diff_le hb hf (n + 1) k)
      rw [placePSum_succ f, placePSum_succ f', h', ← sub_sub, add_sub_right_comm, sub_self, zero_add]
      rw [h'] at h
      apply lt_of_add_lt_add_left at h
      apply placeVal_le_of_lt at h
      replace h := le_sub_left_of_add_le h
      refine lt_of_lt_of_le ?_ h
      apply sub_lt_self
      positivity
    · have := IH hf' hf h' 1
      rw [placePSum_succ] at this
      have := calc
        placePSum f' b n + placeVal f' b n < placePSum f b n := this
        _ ≤ placePSum f b n + placeVal f b n := le_add_of_nonneg_right placeVal_nonneg
        _ < placePSum f' b n + placeVal f' b n := h
      linarith

theorem placePSum_inj {b : ℕ} (hb : 1 < b) {f f' : ℕ → ℕ} (hf : Set.range f ⊆ Finset.range b) (hf' : Set.range f' ⊆ Finset.range b) (n : ℕ) (h : placePSum f b n = placePSum f' b n) (i : ℕ) (hi : i ∈ Finset.range n) : f i = f' i := by
  induction n
  case zero => simp at hi
  case succ n IH =>
    · rcases lt_trichotomy (placePSum f b n) (placePSum f' b n) with hsum | hsum | hsum
      · have := placePSum_add_lt_of_lt hb hf hf' n hsum
        have := calc
          placePSum f b (n + 1) < placePSum f' b n := this 1
          _ ≤ placePSum f' b (n + 1) := placePSum_le_add f' b n 1
          _ = placePSum f b (n + 1) := h.symm
        linarith
      · rw [placePSum_succ, placePSum_succ, hsum] at h
        simp only [placeVal, inv_pow, add_right_inj, mul_eq_mul_right_iff, Nat.cast_inj,
          inv_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
          not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero] at h
        rcases h with h | h <;> [skip; linarith]
        rw [Finset.mem_range_succ_iff, le_iff_lt_or_eq] at hi
        rcases hi with hi | hi
        · rw [← Finset.mem_range] at hi
          exact IH hsum hi
        · subst i
          exact h
      · have := placePSum_add_lt_of_lt hb hf' hf n hsum
        have := calc
          placePSum f' b (n + 1) < placePSum f b n := this 1
          _ ≤ placePSum f b (n + 1) := placePSum_le_add f b n 1
          _ = placePSum f' b (n + 1) := h
        linarith

-- TODO: some injectivity modulo interval on facesLT and facesLE

/-- Assume that `x ∈ (0,1]`. Then `facesLE_sum b x n` is the fraction represented by the first `n` bits in the LE-binary expansion of `x`. -/
noncomputable def facesLEPSum (b : ℕ) (x : ℝ) := placePSum (facesLE b x) b

/-- Assume that `x ∈ (0,1]`. Then `facesLT_sum b x n` is the fraction represented by the first `n` bits in the LT-binary expansion of `x`. -/
noncomputable def facesLTPSum (b : ℕ) (x : ℝ) := placePSum (facesLT b x) b

theorem facesLEPSum_def (b : ℕ) (x : ℝ) : facesLEPSum b x = placePSum (facesLE b x) b := by rfl

theorem facesLTPSum_def (b : ℕ) (x : ℝ) : facesLTPSum b x = placePSum (facesLT b x) b := by rfl

/-- Assume that `x ∈ (0, 1]`. Then `facesLTPSum b x n` multiplied by `2^n` is an integer whose binary representation is the first `n` most significant bits of the LT-binary expansion of `x`. -/
theorem facesLTPSum_mul {b : ℕ} (hb : 1 < b) {x : ℝ} (hx : x ∈ UI) (n : ℕ) : facesLTPSum b x n * b ^ n = ⌈x * b ^ n - 1⌉ := by
  have hx' := hx
  simp only [UI, Set.mem_Ioc] at hx'
  induction n
  · simp only [facesLTPSum, placePSum_zero, zero_mul, pow_zero, mul_one, Int.ceil_sub_one, Int.cast_sub, Int.cast_one]
    norm_cast
    symm
    rw [Int.sub_eq_zero, Int.ceil_eq_iff]
    simpa only [Int.cast_one, sub_self]
  · case succ n' IH =>
      rw [facesLTPSum_def] at IH
      have (a : ℝ) : a * (↑b)⁻¹ ^ (n' + 1) * (↑b ^ n' * ↑b) = a * ((↑b)⁻¹ * ↑b) ^ (n' + 1) := by ring
      rw [facesLTPSum_def, placePSum_succ, pow_add, pow_one, add_mul, ← mul_assoc, IH, placeVal_def, facesLT_def, Int.natCast_ceil_eq_ceil'' (by
        apply lt_of_add_lt_add_right (a:=1)
        rw [neg_add_cancel, sub_add_cancel]
        exact mul_pos (Set.mem_Ioc.mp (ceso_bounds (x * b ^ n'))).1 (by positivity)
      ), this, inv_mul_cancel₀ (by positivity), one_pow, mul_one]
      simp only [Int.ceil_sub_one, ← mul_assoc]
      norm_num
      by_cases h1 : Int.fract (x * b ^ n') = 0
      · have h1' := Int.floor_add_fract (x * b ^ n')
        rw [h1, add_zero] at h1'
        have h2 : Int.fract (x * b ^ n' * b) = 0 := calc
          Int.fract (x * b ^ n' * b) = x * b ^ n' * b - ⌊x * b ^ n' * b⌋ := (Int.self_sub_floor _).symm
          _ = x * b ^ n' * b - ⌊(⌊x * b ^ n'⌋ + Int.fract (x * b ^ n')) * b⌋ := by rw [Int.floor_add_fract]
          _ = x * b ^ n' * b - ⌊(⌊x * b ^ n'⌋ * b + Int.fract (x * b ^ n') * b)⌋ := by ring_nf
          _ = x * b ^ n' * b - ⌊x * b ^ n'⌋ * b := by
            rw [h1, zero_mul, add_zero, (by norm_cast : (⌊x * b ^ n'⌋:ℝ) * b = (⌊x * b ^ n'⌋ * b:ℤ)), Int.floor_intCast]
          _ = 0 := by rw [← sub_mul, Int.self_sub_floor, h1, zero_mul]
        have h2' := Int.floor_add_fract (x * b ^ n' * b)
        rw [h2, add_zero] at h2'
        rw [← Int.floor_add_fract (x * b ^ n' * b), h2, ← Int.floor_add_fract (x * b ^ n'), h1]
        norm_num
        rw [h1', h2']
        ring
      rw [← ne_eq] at h1
      have h1' := Int.floor_add_fract (x * 2 ^ n')
      rw [Int.ceil_eq_add_one_sub_fract h1,
        (by ring : (x * b ^ n' + 1 - Int.fract (x * b ^ n') - 1) * b = (x * b ^ n' * b - Int.fract (x * b ^ n') * b)),
        (by ring : (x * b ^ n' - (x * b ^ n' + 1 - Int.fract (x * b ^ n') - 1)) * b = Int.fract (x * b ^ n') * b)
      ]
      have h2h3 : Int.fract (x * b ^ n' * b) = Int.fract (Int.fract (x * b ^ n') * b) := by
        nth_rw 1 [← Int.floor_add_fract (x * b ^ n'), add_mul]
        norm_cast
        rw [Int.fract_int_add]
      by_cases h2 : Int.fract (x * b ^ n' * b) = 0 <;> have h3 := h2 <;> rw [h2h3] at h3
      · have h2' := Int.floor_add_fract (x * b ^ n' * b)
        rw [h2, add_zero] at h2'
        have h3' := Int.floor_add_fract (Int.fract (x * b ^ n') * b)
        rw [h3, add_zero] at h3'
        rw [← Int.floor_add_fract (Int.fract (x * b ^ n') * b), h3, add_zero]
        norm_num
        rw [← Int.floor_add_fract (x * b ^ n' * b), h2, add_zero]
        norm_num
      · rw [← ne_eq] at h2 h3
        rw [Int.ceil_eq_add_one_sub_fract h2, Int.ceil_eq_add_one_sub_fract h3, ← h2h3]
        ring

/-- Assume that `x ∈ (0, 1]`. Then `facesLTPSum b x n` is bounded below by `x - 2^(-n)`. Note: this bound is tight for some `n` and `x`. -/
theorem le_facesLTPSum {b : ℕ} (hb : 1 < b) {x : ℝ} (hx : x ∈ UI) (n : ℕ) : x - (b:ℝ)⁻¹ ^ n ≤ facesLTPSum b x n := by
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < (b:ℝ) ^ n)
  rw [facesLTPSum_mul hb hx _, sub_mul, ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
  exact Int.le_ceil _

/-- Assume that `x ∈ (0, 1]` and `1 < b`. Then `facesLTPSum b x n` is strictly bounded above by `x`. -/
theorem facesLTPSum_lt {b : ℕ} (hb : 1 < b) {x : ℝ} (hx : x ∈ UI) (n : ℕ) : facesLTPSum b x n < x := by
  refine lt_of_mul_lt_mul_right ?_ (by positivity : 0 ≤ (b:ℝ) ^ n)
  rw [facesLTPSum_mul hb hx]
  have := Int.ceil_lt_add_one (x * b ^ n - 1)
  rwa [sub_add_cancel] at this

theorem bin_cau (b:ℕ) (hb : 1 < b) : IsCauSeq abs fun n ↦ ∑ m ∈ Finset.range n, (b:ℝ)⁻¹ ^ m :=
  IsCauSeq.geo_series (b:ℝ)⁻¹ <| by
    rw [abs_lt, inv_lt_one₀ (by positivity)]
    exact ⟨lt_trans neg_one_lt_zero (inv_pos_of_pos (by positivity)), by norm_cast⟩

/-- Assume that `x ∈ (0, 1]` and `1 < b`. The infinite sum of the `facesLT b i x` is `x` itself. -/
theorem eq_1_7' {b : ℕ} (hb : 1 < b) {x : ℝ} (hunit : x ∈ UI) : HasSum (fun (n : ℕ) ↦ placeVal (facesLT b x) b n) x := by
  refine hasSum_of_isLUB_of_nonneg x ?_ ?_
  · intro n
    exact placeVal_nonneg
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    constructor
    intro a
    by_cases ha : a.Nonempty
    refine le_trans (?_ : ∑ i ∈ a, placeVal (facesLT b x) b i ≤ facesLTPSum b x (a.max' ha + 1)) ?_
    · rw [facesLTPSum_def, ← add_le_add_iff_left
      (∑ i ∈ Finset.range (a.max' ha + 1) \ a, placeVal (facesLT b x) b i), Finset.sum_sdiff]
      · apply le_add_of_nonneg_left
        apply Finset.sum_nonneg'
        intro i
        exact placeVal_nonneg
      intro x hx
      simp
      apply Nat.lt_succ_of_le
      exact Finset.le_max' a x hx
    · apply le_of_sub_nonneg
      refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < b ^ (a.max' ha + 1))
      rw [sub_mul, facesLTPSum_mul hb hunit, zero_mul]
      norm_num
      exact le_of_lt (Int.ceil_lt_add_one (x * b ^ (a.max' ha + 1)))
    · simp at ha
      rw [ha]
      simp at hunit ⊢
      exact le_of_lt hunit.1
    · intro a ha
      refine le_of_forall_lt ?_
      intro c hxc
      by_cases hcnn : c < 0
      · specialize ha ∅
        simp at ha
        exact lt_of_lt_of_le hcnn ha
      · push_neg at hcnn
        have hx := hunit
        simp at hx
        rw [← sub_lt_sub_iff_right c, sub_self] at hxc
        have hclog := Int.zpow_log_le_self hb hxc
        have hxcub : x - c ≤ 1 := by linarith
        have hlog := Int.log_of_right_le_one b hxcub
        rw [← neg_eq_iff_eq_neg] at hlog
        have hbound := le_facesLTPSum hb hunit (Nat.clog b ⌈(x - c)⁻¹⌉₊ + 1)
        rw [sub_le_comm] at hbound
        have ha' := ha (Finset.range (Nat.clog b ⌈(x - c)⁻¹⌉₊ + 1))
        rw [pow_add, pow_one, ← zpow_natCast, ← hlog, inv_zpow', neg_neg] at hbound
        refine lt_of_lt_of_le ?_ ha'
        rw [← sub_lt_sub_iff_left x]
        refine lt_of_le_of_lt hbound ?_
        refine lt_of_lt_of_le ?_ hclog
        apply mul_lt_of_lt_one_right ?_ (by rw [inv_lt_comm₀ (by positivity) (by positivity), inv_one]; norm_cast)
        apply zpow_pos (by positivity)

/-- Assume that `x ∈ (0, 1]`. The infinite sum of the `d' i x` is `x` itself. This is more conventional notation. -/
theorem eq_1_7 {b : ℕ} (hb : 1 < b) {x : ℝ} (hunit : x ∈ UI) : ∑' n, placeVal (facesLT b x) b n = x := HasSum.tsum_eq (eq_1_7' hb hunit)

/-- Assume that `x ∈ (0, 1]`. For each `n`, `x` lies in an interval defined by its LT-binary expansion up to `n` digits. -/
theorem eq_1_9' {b : ℕ} (hb : 1 < b) {x : ℝ} (hunit : x ∈ UI) (n : ℕ) : x ∈ Set.Ioc (facesLTPSum b x n) (facesLTPSum b x n + (b:ℝ)⁻¹ ^ n) := by
  simp only [inv_pow, Set.mem_Ioc]
  constructor
  · exact facesLTPSum_lt hb hunit _
  · rw [← sub_le_iff_le_add, ← inv_pow]
    exact le_facesLTPSum hb hunit _

/-- Assume that `x ∈ (0, 1]`. For each `n`, `x` lies in an interval defined by its LT-binary expansion up to `n` digits. -/
theorem eq_1_9 {b : ℕ} (hb : 1 < b) (u : ℕ → ℕ) (hu : Set.range u ⊆ Finset.range b) (n : ℕ) : { x ∈ UI | ∀ i ∈ Finset.range n, facesLT b x i = u i } = Set.Ioc (placePSum u b n) (placePSum u b n + (b:ℝ)⁻¹ ^ n) := by
  ext x
  constructor
  · intro h1
    simp only [Set.mem_Ioc, Finset.mem_range, Set.mem_setOf_eq] at h1 ⊢
    rcases h1 with ⟨hunit, h1⟩
    have h : placePSum (facesLT b x) b n = placePSum u b n :=
      Finset.sum_congr (by rfl) (by intro x' hx'; simp [placeVal] at hx' ⊢; rw [h1 _ hx']; left; rfl)
    rw [← h]
    refine ⟨facesLTPSum_lt hb hunit n, sub_le_iff_le_add.mp (le_facesLTPSum hb hunit n)⟩
  · intro ⟨hlb, hub⟩
    have hunit : x ∈ UI := by
      constructor
      · apply lt_of_le_of_lt placePSum_nonneg hlb
      · exact le_trans hub (le_sub_iff_add_le.mp (placePSum_le hb hu n))
    refine ⟨hunit, ?_⟩
    refine placePSum_inj hb (facesLT_range hb) hu n ?_
    have hf := Set.mem_Ioc.mp (eq_1_9' hb hunit n)
    rcases lt_trichotomy (placePSum (facesLT b x) b n) (placePSum u b n) with htr | htr | htr
    · have := calc
        x ≤ facesLTPSum b x n + (↑b)⁻¹ ^ n := hf.2
        _ ≤ placePSum u b n := placePSum_le_of_lt hb (facesLT_range hb) hu n htr
        _ < x := hlb
      linarith
    · exact htr
    · have := calc
        x ≤ placePSum u b n + (↑b)⁻¹ ^ n := hub
        _ ≤ facesLTPSum b x n := placePSum_le_of_lt hb hu (facesLT_range hb) n htr
        _ < x := hf.1
      linarith
