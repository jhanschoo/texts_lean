import Mathlib

/-- Assume that `0 ≤ (r : ℝ) < 1` and `2 ≤ (b : ℕ)`. Return the first `t` `b`-its in the `b`-ary expansion of the fractional part of `r` (`r` minus its floor) in big-endian order.
  That is, the first element is the most-significant `b`-it of the fractional part, and if
  multiple representations are possible, choose the one that comes **later** in the natural dictionary order of sequences of digits. -/
def Rat.leFractTakeAux (b : ℕ) (r : ℚ) : ℕ → List ℕ
  | 0 => []
  | t + 1 =>
      let r' := b * r
      let r'fl := ⌊r'⌋₊
      r'fl :: Rat.leFractTakeAux b (r' - r'fl) t

/-- Assume that `2 ≤ (b : ℕ)`. Return the first `t` `b`-its in the `b`-ary expansion of the fractional part of `r` (`r` minus its floor) in big-endian order.
  That is, the first element is the most-significant `b`-it of the fractional part, and if
  multiple representations are possible, choose the one that comes **later** in the natural dictionary order of sequences of digits. -/
def Rat.leFractTake (b : ℕ) (r : ℚ) : ℕ → List ℕ :=
  Rat.leFractTakeAux b (r - ⌊r⌋)

/-- The following function is defined so that its image bijects with ℝ in the natural manner -/
def Rat.asleIntFractTake (b : ℕ) (r : ℚ) : ℤ × (ℕ → List ℕ) := (⌊r⌋, Rat.leFractTake b r)

/-- Assuming `2 ≤ (b : ℕ)`, and given a size `t`, returns a constant list of size `t` containing `b-1` -/
def Rat.ltFractTakeAuxMax (b : ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => (b - 1) :: Rat.ltFractTakeAuxMax b t

/-- Assume that `0 < (r : ℝ) ≤ 1` and `2 ≤ (b : ℕ)`. Return the first `t` `b`-its in the `b`-ary expansion of (`r+1-⌈r⌉`) in big-endian order.
  That is, the first element is the most-significant `b`-it of the fractional part, and if
  multiple representations are possible, choose the one that comes **earlier** in the natural dictionary order of sequences of digits -/
def Rat.ltFractTakeAux (b : ℕ) (r : ℚ) : ℕ → List ℕ
  | 0 => []
  | t + 1 =>
      let r' := b * r
      let r'fl := ⌈r' - 1⌉₊
      r'fl :: Rat.leFractTakeAux b (r' - r'fl) t

/-- Assume that `2 ≤ (b : ℕ)`. Return the first `t` `b`-its in the `b`-ary expansion of (`r+1-⌈r⌉`) in big-endian order.
  That is, the first element is the most-significant `b`-it of the fractional part, and if
  multiple representations are possible, choose the one that comes **earlier** in the natural dictionary order of sequences of digits -/
def Rat.ltFractTake (b : ℕ) (r : ℚ) : ℕ → List ℕ :=
  Rat.ltFractTakeAux b (r - ⌈r - 1⌉)

/-- The following function is defined so that its image bijects with ℝ in the natural manner -/
def Rat.asltIntFractTake (b : ℕ) (r : ℚ) : ℤ × (ℕ → List ℕ) := (⌈r - 1⌉, Rat.ltFractTake b r)
