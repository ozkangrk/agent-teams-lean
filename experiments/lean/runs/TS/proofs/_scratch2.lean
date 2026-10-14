import FormalConjectures.OEIS.«113250»

example (f : ℕ → ℤ) (m : ℕ) (h : f (2 * m + 5) = 3) : f (2 * (m + 1) + 3) = 3 := by
  ring_nf at h ⊢
  exact h

example : OeisA113250.a (2 * 3 + 1) = (64 * 2) * (64 * 2) := by norm_num [OeisA113250.a]
