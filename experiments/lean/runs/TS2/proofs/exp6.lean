import FormalConjectures.OEIS.«113250»
def f : ℕ → ℤ := fun n =>
  match n % 6 with
  | 0 => -1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => -1
  | _ => 4

example (n : ℕ) (h : n % 6 = 3) : f (n + 4) = -f (n + 3) + f (n + 1) + f n := by
  simp only [f, Nat.add_mod, h]
  decide
