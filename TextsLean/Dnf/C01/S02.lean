import TextsLean.Basic

namespace Dnf.C01.S02

/- Definition 1.2.1 **dihedral group** -/
#check DihedralGroup

open DihedralGroup in
example : (sr 9 : DihedralGroup 12) * sr 6 = r 9 := rfl

/- TODO: statement of properties -/

/- TODO: equivalence with symmetries of a polygon under rigid motion -/

/- TODO: discussion on generators and presentation -/
/- see: Subgroup.closure -/

namespace Exercises

/- Exercise 1.2.1.(a) -/
example : Fintype.card (DihedralGroup 3) = 6 := rfl
example : Fintype.card (DihedralGroup 4) = 8 := rfl
example : Fintype.card (DihedralGroup 5) = 10 := rfl

/- TODO -/

end Exercises

end Dnf.C01.S02
