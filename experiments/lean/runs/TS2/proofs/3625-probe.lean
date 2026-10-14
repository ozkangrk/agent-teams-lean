
import FormalConjectures.OEIS.«3625»
open OeisA3625 Polynomial ZMod legendreSym

#check @legendreSym.eq_one_iff
#check @legendreSym.eq_one_iff'
#check @legendreSym.at_neg
#check @legendreSym.quadratic_reciprocity'
#check @ZMod.val_natCast
#check @ZMod.natCast_zmod_val
#check @Polynomial.exists_root_of_degree_eq_one
#check @Polynomial.not_irreducible_iff
#check @Polynomial.dvd_iff_isRoot
#check @χ₄_eq_neg_one_pow
#check @neg_one_pow_of_even
#check @Polynomial.degree_eq_natDegree
example : IsSquare ((2 : ZMod 7)) := by decide
example : ¬ IsSquare ((3 : ZMod 7)) := by decide
example (p : Nat) (h7 : p % 7 < 7) : True := by interval_cases p % 7 <;> trivial
