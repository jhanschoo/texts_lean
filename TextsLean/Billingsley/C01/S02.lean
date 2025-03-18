import TextsLean.Basic

open scoped symmDiff

/- 1.2 Probability measures -/
namespace Billingsley.C01.S02
/- 1.2.1 Spaces -/
-- TODO
/- 1.2.2 Assigning probabilities -/
-- TODO
/- 1.2.3 Classes of sets -/

/- Example 1.2.1 TODO -/

/- Definition 1.2.1: **Algebra of sets**, or **Field of sets** -/
example (𝒜 : Set (Set α)) : MeasureTheory.IsSetAlgebra 𝒜 ↔
  ∅ ∈ 𝒜 ∧ ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, sᶜ ∈ 𝒜 ∧ s ∪ t ∈ 𝒜 := by sorry
/- Equivalent characterizations -/
example (𝒜 : Set (Set α)) : MeasureTheory.IsSetAlgebra 𝒜 ↔
  ⊤ ∈ 𝒜 ∧ ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, sᶜ ∈ 𝒜 ∧ s ∪ t ∈ 𝒜 := by sorry
example (𝒜 : Set (Set α)) : MeasureTheory.IsSetAlgebra 𝒜 ↔
  Nonempty 𝒜 ∧ ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, sᶜ ∈ 𝒜 ∧ s ∪ t ∈ 𝒜 := by sorry
example (𝒜 : Set (Set α)) : MeasureTheory.IsSetAlgebra 𝒜 ↔
  ∅ ∈ 𝒜 ∧ ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, sᶜ ∈ 𝒜 ∧ s ∩ t ∈ 𝒜 := by sorry
#check MeasureTheory.IsSetAlgebra
#check MeasureTheory.IsSetAlgebra.empty_mem
#check MeasureTheory.IsSetAlgebra.compl_mem
#check MeasureTheory.IsSetAlgebra.union_mem
#check MeasureTheory.IsSetAlgebra.univ_mem
#check MeasureTheory.IsSetAlgebra.inter_mem
#check MeasureTheory.IsSetAlgebra.diff_mem
#check MeasureTheory.IsSetAlgebra.biUnion_mem
#check MeasureTheory.IsSetAlgebra.biInter_mem
/- Definition 1.2.1: **σ-algebra** -/
example : (∃ m : MeasurableSpace α, m.MeasurableSet' = P) ↔
  P ∅ ∧ (∀ s, P sᶜ) ∧
  (∀ (f : ℕ → Set α), (∀ i, P (f i)) → P (⋃ i, f i)) := by sorry
/- Equivalent characterizations -/
example : (∃ m : MeasurableSpace α, m.MeasurableSet' = P) ↔
  P ∅ ∧ (∀ s, P sᶜ) ∧
  (∀ (f : ℕ → Set α), (∀ i, P (f i)) → P (⋂ i, f i)) := by sorry
/- a σ-algebra is an algebra of sets -/
example [MeasurableSpace α] : MeasureTheory.IsSetAlgebra { s : Set α | MeasurableSet s } := by sorry
#check MeasurableSet.empty
#check MeasurableSet.compl_iff
#check MeasurableSet.univ
#check MeasurableSet.iUnion
#check MeasurableSet.biUnion

/- Example 1.2.2 TODO -/
-- namespace Billingsley.C01.S02.E02
-- def ℬ₀ := { S : Set ℝ : ∃ (n : ℕ) }

/- Example 1.2.3 TODO -/

/- Example 1.2.4 TODO -/

example : ∃ m : MeasurableSpace α, 𝒫 ⊤ = { s | m.MeasurableSet' s } := by sorry
example : ∃ m : MeasurableSpace α, ∀ s, m.MeasurableSet' s ↔ s = ⊤ ∨ s = ⊥ := by sorry
example {𝒜 : Set (Set α)} (h : MeasureTheory.IsSetAlgebra 𝒜) (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) : A \ B ∈ 𝒜 := by sorry
example {𝒜 : Set (Set α)} (h : MeasureTheory.IsSetAlgebra 𝒜) (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) : A ∆ B ∈ 𝒜 := by sorry

-- TODO

/- 1.2.4 Probability measures -/
-- TODO
/- 1.2.5 Lebesgue measure on the unit interval -/
-- TODO
/- 1.2.6 Sequence space -/
-- TODO
/- 1.2.7 Constructing σ-fields -/
-- TODO
section Exercises
end Exercises

end Billingsley.C01.S02
