import Mathlib.NumberTheory.LegendreSymbol.Basic
#print legendreSym
example {p : ℕ} [Fact p.Prime] (a : ℤ) : legendreSym p a = 0 ∨ legendreSym p a = 1 ∨ legendreSym p a = -1 := by
  rcases show legendreSym p a = _ from rfl with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | -1 => exact Or.inr (Or.inr rfl)
