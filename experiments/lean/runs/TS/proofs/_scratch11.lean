import Mathlib.NumberTheory.LegendreSymbol.Basic
open ZMod
example (p : ℕ) : ((p : ℤ) : ZMod 7) = ((p % 7 : ℕ) : ZMod 7) := by
  norm_num [Int.natCast_mod, Nat.add_mul_mod_self_left]
example : ¬ IsSquare ((3 : ℕ) : ZMod 7) := by
  rintro ⟨y, hy⟩
  fin_cases y
  all_goals exact absurd hy (by decide)
example : IsSquare ((2 : ℕ) : ZMod 7) := ⟨3, by decide⟩
example : IsSquare ((4 : ℕ) : ZMod 7) := ⟨2, by decide⟩
