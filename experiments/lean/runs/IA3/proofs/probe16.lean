import Mathlib
open Finset Nat
example (n m : ℕ) (h3 : 3 ≤ m)
    (h2b : (m - 1) * (m / (m - 1)) ≤ m - 1)
    (hrestsum' : ∑ x ∈ Finset.Ico 2 (m - 1), x * (m / x) ≤ m * m - 3 * m) :
    1 * (m / 1) + ((m - 1) * (m / (m - 1)) + (m * (m / m) + ∑ x ∈ Finset.Ico 2 (m - 1), x * (m / x))) + 1 ≤ m * m := by
  have hm0 : 0 < m := by omega
  rw [Nat.div_one, Nat.div_self hm0]
  omega
