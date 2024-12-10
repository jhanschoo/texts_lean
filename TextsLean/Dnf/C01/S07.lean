import TextsLean.Basic

namespace Dnf.C01.S07

/- Definition 1.5.1 Group Action -/
#check MulAction
#check MulAction.toSMul.smul
#check MulAction.one_smul
example [Monoid α] [MulAction α β] (b : β): (1 : α) • b = b := MulAction.one_smul b
#check MulAction.mul_smul
example [Monoid α] [MulAction α β] (x y : α) (b : β) : (x * y) • b = x • y • b := MulAction.mul_smul x y b
#check AddAction
#check AddAction.toVAdd.vadd
#check AddAction.zero_vadd
#check AddAction.add_vadd

/- Definition 1.5.2 associated permutation representation -/
/- Note that the following require that the acting structure is a group and not just a monoid; since we wanted to show that the induced structure is a permutation and not just a monoid endomorphism -/
/- the homomorphism to permutations induced by each element -/
#check MulAction.toPermHom
/- the map to permutations induced by each element that has forgotten that it is a hom -/
#check MulAction.toPerm
/- and the statement of equivalence -/
#check MulAction.toPermHom_apply
/- and the identification of the permutation with the action -/
#check MulAction.toPerm_apply

/- Examples 1.5.3.1 trivial action -/
def MulAction.trivial [Monoid α] : MulAction α β := { smul := fun _ b => b, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
example [Monoid α] (a : α) (b : β) : MulAction.trivial.smul a b = b := rfl
-- faithful smul
#check FaithfulSMul
-- the action is faithful once the underlying smul is faithful
#check MulAction.toPerm_injective
-- kernel of an action is the subgroup of elements that act trivially; that is, the kernel of the associated map to the permutation representation
/- Example 1.5.3.2 -/
-- TODO
/- Example 1.5.3.3 -/

namespace Exercises

end Exercises

end Dnf.C01.S07
